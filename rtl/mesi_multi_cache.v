// Formal model of N caches, each running mesi_cache_core.v, sharing one
// cache line over a single snooping bus. Proves MESI's coherence
// invariants (mutual exclusion of Modified, no stale reads after
// invalidation) rather than modeling cache capacity or replacement.
module mesi_multi_cache #(
    parameter integer N = 3
) (
    input  wire         clk,
    input  wire         rst_n,
    input  wire [N-1:0] cpu_read,
    input  wire [N-1:0] cpu_write
);
    localparam [1:0] ST_I = 2'd0;
    localparam [1:0] ST_S = 2'd1;
    localparam [1:0] ST_E = 2'd2;
    localparam [1:0] ST_M = 2'd3;

    wire [1:0] state        [0:N-1];
    wire       issue_busrd  [0:N-1];
    wire       issue_busrdx [0:N-1];
    wire [N-1:0] other_has_line;
    wire [N-1:0] snoop_read_in;
    wire [N-1:0] snoop_readex_in;

    genvar gi, gj;

    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : G_FANIN
            wire [N-1:0] has_mask, rd_mask, rdx_mask;
            for (gj = 0; gj < N; gj = gj + 1) begin : G_FANIN_J
                assign has_mask[gj] = (gj == gi) ? 1'b0 : (state[gj] != ST_I);
                assign rd_mask[gj]  = (gj == gi) ? 1'b0 : issue_busrd[gj];
                assign rdx_mask[gj] = (gj == gi) ? 1'b0 : issue_busrdx[gj];
            end
            assign other_has_line[gi]  = |has_mask;
            assign snoop_read_in[gi]   = |rd_mask;
            assign snoop_readex_in[gi] = |rdx_mask;
        end
    endgenerate

    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : G_CACHE
            mesi_cache_core core (
                .clk(clk),
                .rst_n(rst_n),
                .cpu_read(cpu_read[gi]),
                .cpu_write(cpu_write[gi]),
                .snoop_read(snoop_read_in[gi]),
                .snoop_readex(snoop_readex_in[gi]),
                .other_has_line(other_has_line[gi]),
                .state(state[gi]),
                .issue_busrd(issue_busrd[gi]),
                .issue_busrdx(issue_busrdx[gi])
            );
        end
    endgenerate

`ifdef FORMAL
    // ================= Environment assumptions =================
    initial assume(!rst_n);

    genvar ga;
    generate
        for (ga = 0; ga < N; ga = ga + 1) begin : G_ASSUME_PER_CACHE
            always @(posedge clk) begin
                // A1: each cache issues at most one kind of request per cycle.
                if (rst_n) assume(!(cpu_read[ga] && cpu_write[ga]));
            end
        end
    endgenerate

    // A2: serialize only the events that can actually race: a real bus
    // transaction, or a silent E-to-M upgrade (no bus transaction, but still
    // vulnerable to losing its write if a real bus transaction lands the
    // same cycle, see docs/verification_plan.md section 3).
    wire [N-1:0] bus_txn_mask;
    wire [N-1:0] silent_upgrade_mask;
    generate
        for (ga = 0; ga < N; ga = ga + 1) begin : G_BUSTXN
            assign bus_txn_mask[ga] = issue_busrd[ga] | issue_busrdx[ga];
            assign silent_upgrade_mask[ga] = (state[ga] == ST_E || state[ga] == ST_M) && cpu_write[ga] && !cpu_read[ga];
        end
    endgenerate
    always @(posedge clk) begin
        if (rst_n) assume($onehot0(bus_txn_mask | silent_upgrade_mask));
    end

    // ================= Safety properties =================
    // Per-cache checks are left unlabeled: a static label inside generate
    // for collides across iterations in this yosys build. sby still
    // reports the failing cache instance via its hierarchical path.
    genvar gp;
    generate
        for (gp = 0; gp < N; gp = gp + 1) begin : G_SAFETY
            always @(posedge clk) begin
                if (rst_n) begin
                    // P1: state is always one of the 4 defined encodings.
                    assert(state[gp] <= ST_M);

                    // P2: single-writer invariant. If this cache holds E or
                    // M, no other cache holds any copy of the line.
                    assert(!(state[gp] == ST_E || state[gp] == ST_M)
                           || !other_has_line[gp]);
                end
            end
        end
    endgenerate

    // P3: mutual exclusion of Modified, the headline property, stated
    // directly rather than relying on P2 alone.
    wire [N-1:0] m_mask;
    generate
        for (gp = 0; gp < N; gp = gp + 1) begin : G_MMASK
            assign m_mask[gp] = (state[gp] == ST_M);
        end
    endgenerate
    always @(posedge clk) begin
        if (rst_n) begin
            mutex_modified: assert($onehot0(m_mask));
        end
    end

    // ================= Functional correctness (per-cache) =================
    // Next-cycle claims, expressed with $past() since this yosys build
    // does not accept concurrent SVA (assert property (@(...) ...)).
    generate
        for (gp = 0; gp < N; gp = gp + 1) begin : G_FUNC
            wire p4_ante = (state[gp] == ST_I) && cpu_read[gp] && !cpu_write[gp] && !other_has_line[gp];
            wire p5_ante = (state[gp] == ST_I) && cpu_read[gp] && !cpu_write[gp] && other_has_line[gp];
            wire p6_ante = cpu_write[gp] && !cpu_read[gp];
            wire p8_ante = (state[gp] == ST_E || state[gp] == ST_M) && snoop_read_in[gp] && !snoop_readex_in[gp];

            always @(posedge clk) begin
                if (rst_n && $past(rst_n)) begin
                    // P4: read miss with no other owner becomes Exclusive.
                    assert (!$past(p4_ante) || state[gp] == ST_E);

                    // P5: read miss with another owner becomes Shared, never Exclusive.
                    assert (!$past(p5_ante) || state[gp] == ST_S);

                    // P6: any local write results in Modified.
                    assert (!$past(p6_ante) || state[gp] == ST_M);

                    // P7: a remote BusRdX invalidates this cache unconditionally.
                    assert (!$past(snoop_readex_in[gp]) || state[gp] == ST_I);

                    // P8: a remote BusRd downgrades E/M to Shared, not Invalid.
                    assert (!$past(p8_ante) || state[gp] == ST_S);
                end

                // P9: silent upgrade. A write to an Exclusive line becomes
                // Modified without issuing a bus transaction that cycle.
                if (rst_n) begin
                    assert (!(state[gp] == ST_E && cpu_write[gp]) || !issue_busrdx[gp]);
                end
            end
        end
    endgenerate

    // ================= Coverage =================
    generate
        for (gp = 0; gp < N; gp = gp + 1) begin : G_COVER
            always @(posedge clk) begin
                // C1-C3: each cache can individually reach S, E, and M.
                if (rst_n) begin
                    cover(state[gp] == ST_S);
                    cover(state[gp] == ST_E);
                    cover(state[gp] == ST_M);
                end
                if (rst_n && $past(rst_n)) begin
                    // C4: the silent E to M upgrade path is actually exercised.
                    cover($past(state[gp]) == ST_E && state[gp] == ST_M);
                    // C5: a Modified line is later invalidated by a remote write.
                    cover($past(state[gp]) == ST_M && state[gp] == ST_I);
                end
            end
        end
    endgenerate

    generate
        if (N >= 2) begin : G_COVER_MULTI
            always @(posedge clk) begin
                // C6: two different caches hold Shared simultaneously.
                if (rst_n) begin
                    reach_two_shared: cover(state[0] == ST_S && state[1] == ST_S);
                end
                // C7: ownership transfer. Cache 0 downgrades from Modified
                // the same cycle cache 1's read pulls both to Shared.
                if (rst_n && $past(rst_n)) begin
                    cover_ownership_transfer: cover($past(state[0]) == ST_M && state[0] == ST_S && state[1] == ST_S);
                end
                // C9: two caches issue a genuinely concurrent local read in
                // the same cycle, both already Shared. A2 only serializes
                // real bus transactions and silent E/M writes now, so this
                // harmless concurrency, forbidden under a blanket
                // one-request-at-a-time assumption, is reachable.
                if (rst_n) begin
                    concurrent_shared_reads: cover(state[0] == ST_S && state[1] == ST_S
                                                    && cpu_read[0] && cpu_read[1]);
                end
            end
        end
    endgenerate
    generate
        if (N >= 3) begin : G_COVER_TRIPLE
            always @(posedge clk) begin
                // C8: all three caches hold Shared simultaneously.
                if (rst_n) begin
                    reach_three_shared: cover(state[0] == ST_S && state[1] == ST_S && state[2] == ST_S);
                end
            end
        end
    endgenerate
`endif
endmodule
