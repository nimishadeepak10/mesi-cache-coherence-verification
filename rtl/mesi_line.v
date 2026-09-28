// Single cache-line MESI controller (reference model for a single cache).
// States: I = Invalid, S = Shared, E = Exclusive, M = Modified.
// Snoops take priority over a local request in the same cycle.
module mesi_line (
    input  wire       clk,
    input  wire       rst_n,
    input  wire       cpu_read,
    input  wire       cpu_write,
    input  wire       snoop_read,    // BusRd: other core read-shared
    input  wire       snoop_readex,  // BusRdX: other core read-exclusive / invalidate
    output reg  [1:0] state
);
    localparam [1:0] ST_I = 2'd0;
    localparam [1:0] ST_S = 2'd1;
    localparam [1:0] ST_E = 2'd2;
    localparam [1:0] ST_M = 2'd3;

    wire local_req = cpu_read | cpu_write;
    wire snoop     = snoop_read | snoop_readex;

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
                ST_I: state <= cpu_write ? ST_M : ST_E;
                ST_S: state <= cpu_write ? ST_M : ST_S;
                ST_E: state <= cpu_write ? ST_M : ST_E;
                ST_M: state <= ST_M;
                default: state <= ST_I;
            endcase
        end
    end

`ifdef FORMAL
    // Environment assumptions: at most one local request and one snoop type per cycle.
    initial assume(!rst_n);
    always @(posedge clk) begin
        if (rst_n) begin
            assume(!(cpu_read && cpu_write));
            assume(!(snoop_read && snoop_readex));
        end
    end

    // Safety: state is always one of the 4 defined encodings.
    always @(posedge clk) begin
        if (rst_n) valid_encoding: assert(state <= ST_M);
    end

    // Coverage: each of S, E, M is reachable.
    always @(posedge clk) begin
        if (rst_n) begin
            reach_shared:    cover(state == ST_S);
            reach_exclusive: cover(state == ST_E);
            reach_modified:  cover(state == ST_M);
        end
    end
`endif
endmodule
