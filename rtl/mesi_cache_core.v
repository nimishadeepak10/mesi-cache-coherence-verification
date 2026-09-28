// Single cache-line MESI FSM core, instantiated N times by
// mesi_multi_cache.v. Same state machine as mesi_line.v, extended with
// two multi-cache signals: other_has_line (does another cache currently
// hold this line, decides Exclusive vs Shared on a read miss) and
// issue_busrd/issue_busrdx (the bus transaction this cache's local
// request implies for the other caches this cycle).
module mesi_cache_core (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       cpu_read,
    input  wire       cpu_write,
    input  wire       snoop_read,     // BusRd:  another cache read-shared
    input  wire       snoop_readex,   // BusRdX: another cache read-exclusive / invalidate
    input  wire       other_has_line,
    output reg  [1:0] state,
    output wire       issue_busrd,
    output wire       issue_busrdx
);
    localparam [1:0] ST_I = 2'd0;
    localparam [1:0] ST_S = 2'd1;
    localparam [1:0] ST_E = 2'd2;
    localparam [1:0] ST_M = 2'd3;

    wire local_req = cpu_read | cpu_write;
    wire snoop     = snoop_read | snoop_readex;

    // A read from I needs the bus to learn if anyone else has the line.
    // A write from I or S needs the bus to invalidate everyone else.
    // A write from E or M is a silent upgrade, no broadcast needed.
    assign issue_busrd  = local_req && cpu_read  && !cpu_write && (state == ST_I);
    assign issue_busrdx = local_req && cpu_write && ((state == ST_I) || (state == ST_S));

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= ST_I;
        end else if (snoop) begin
            case (state)
                ST_E: state <= snoop_readex ? ST_I : ST_S;
                ST_M: state <= snoop_readex ? ST_I : ST_S;
                ST_S: state <= snoop_readex ? ST_I : ST_S;
                default: state <= ST_I;
            endcase
        end else if (local_req) begin
            case (state)
                ST_I: state <= cpu_write ? ST_M : (other_has_line ? ST_S : ST_E);
                ST_S: state <= cpu_write ? ST_M : ST_S;
                ST_E: state <= cpu_write ? ST_M : ST_E;
                ST_M: state <= ST_M;
                default: state <= ST_I;
            endcase
        end
    end
endmodule
