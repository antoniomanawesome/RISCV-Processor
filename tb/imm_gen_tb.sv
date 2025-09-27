`timescale 1ns / 10ps

module imm_gen_tb;

localparam I_TYPE = 3'b000;
localparam S_TYPE = 3'b001;
localparam B_TYPE = 3'b010;
localparam U_TYPE = 3'b011;
localparam J_TYPE = 3'b100;

logic[31:0] instr;
logic[2:0] immSrc;
logic[31:0] immOut;

logic clk = 1'b0;
logic rst = 1'b0;
int err_count = 0;

imm_gen DUT (
    .instr(instr),
    .immSrc(immSrc),
    .immOut(immOut)
);

initial begin : clk_gen
    forever #5 clk <= ~clk;
end

initial begin : reset
    rst <= 1;
    instr <= 32'b0;
    immSrc <= 3'b000;
    #50;
    rst <= 0;    
end

initial begin : driver
    $timeformat(-9, 0," ns");
    #60;

    for (int i = 0; i < 5; i++) begin // only 5 cases
        immSrc <= i;
        //for (int j = 0; j < 2**32; j++) begin // CANT RUN THIS LOOP ON QUESTA TOO LARGE
        // must find appropriate crv distribution for instr
        instr <= 'h7F352393;
        @(posedge clk);
        scoreboard(instr, immSrc, immOut);
        //end
    end
    
    $display("Test completed with %0d errors", err_count);
    disable clk_gen;
end

function void scoreboard
(
    logic[31:0] instr,
    logic[2:0] immSrc,
    logic[31:0] imm
);
    logic[31:0] expected_imm;

    case (immSrc)
        I_TYPE:
            expected_imm = {{20{instr[31]}}, instr[31:20]};
        S_TYPE:
            expected_imm = {{20{instr[31]}}, instr[31:25], instr[11:7]};
        B_TYPE:
            expected_imm = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
        U_TYPE:
            expected_imm = {instr[31:12], 12'b0};
        J_TYPE:
            expected_imm = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};
        default:
            expected_imm = 32'b0;
    endcase

    assert (imm === expected_imm) 
    else $error($realtime, "Mismatch for immSrc=%b, instr=%h: got %h, expected %h", immSrc, instr, immOut, expected_imm, err_count++);

endfunction

endmodule
