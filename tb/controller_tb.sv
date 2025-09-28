`timescale 1ns / 10ps

module controller_tb;

//opcodes
localparam R_TYPE = 7'b0110011;
localparam I_TYPE = 7'b0010011;
localparam LOAD = 7'b0000011;
localparam STORE = 7'b0100011;
localparam BRANCH = 7'b1100011;
localparam JALR = 7'b1100111;
localparam JAL = 7'b1101111;
localparam LUI = 7'b0110111;
localparam AUIPC = 7'b0010111;

logic [6:0] opcode;
logic regWriteD;
logic memWriteD;
logic jumpD;
logic branchD;
logic aluSrcD;
logic [1:0] aluOp;
logic [1:0] resultSrcD;
logic [2:0] immSrcD;

logic clk = 1'b0;
logic rst = 1'b0;
int err_count = 0;

controller DUT (
    .opcode(opcode),
    .regWriteD(regWriteD),
    .memWriteD(memWriteD),
    .jumpD(jumpD),
    .branchD(branchD),
    .aluSrcD(aluSrcD),
    .aluOp(aluOp),
    .resultSrcD(resultSrcD),
    .immSrcD(immSrcD)
);

covergroup cg @(posedge clk);
    option.per_instance = 1;
    opcode_cp : coverpoint opcode {
        bins R_TYPE = {R_TYPE};
        bins I_TYPE = {I_TYPE};
        bins LOAD = {LOAD};
        bins STORE = {STORE};
        bins BRANCH = {BRANCH};
        bins JALR = {JALR};
        bins JAL = {JAL};
        bins LUI = {LUI};
        bins AUIPC = {AUIPC};
        bins others = {[0:127]};
    }
endgroup

cg group;

initial begin : clk_gen
    forever #5 clk <= ~clk;
end

initial begin : reset
    rst <= 1;
    opcode <= 7'b0000000;
    #50;
    rst <= 0;    
end

assert property (@(posedge clk) rst |-> (regWriteD == 1'b0 && memWriteD == 1'b0 && jumpD == 1'b0 && branchD == 1'b0 && aluSrcD == 1'b0 && aluOp == 2'b00 && resultSrcD == 2'b00 && immSrcD == 3'b000))
else $error($realtime, "Reset failed", err_count++);

initial begin : driver
    group = new();
    $timeformat(-9, 0," ns");
    #100;

    for (int i = 0; i < 128; i++) begin //since opcode is 7 bits
        opcode <= i;
        @(posedge clk);
        scoreboard(opcode, regWriteD, memWriteD, jumpD, branchD, aluSrcD, aluOp, resultSrcD, immSrcD);
    end

    $display("Test completed with %0d errors", err_count);
    $display("Coverage: %0.2f%%", group.get_inst_coverage());
    disable clk_gen;
end

typedef struct {
    logic       regWrite;
    logic       memWrite;
    logic       jump;
    logic       branch;
    logic       aluSrc;
    logic [1:0] aluOp;
    logic [1:0] resultSrc;
    logic [2:0] immSrc;
} results_s;

function void scoreboard
(
    logic [6:0] opcode,
    logic regWriteD, logic memWriteD, logic jumpD, logic branchD,
    logic aluSrcD, logic [1:0] aluOp, logic [1:0] resultSrcD, logic [2:0] immSrcD
);
    results_s res;

    case (opcode)
        R_TYPE:  res = '{1,0,0,0,0,2'b10,2'b00,3'bxxx};
        I_TYPE:  res = '{1,0,0,0,1,2'b10,2'b00,3'b000};
        LOAD:    res = '{1,0,0,0,1,2'b00,2'b01,3'b000};
        STORE:   res = '{0,1,0,0,1,2'b00,2'b00,3'b001};
        BRANCH:  res = '{0,0,0,1,0,2'b01,2'b00,3'b010};
        JALR:    res = '{1,0,1,0,1,2'b00,2'b10,3'b000};
        JAL:     res = '{1,0,1,0,0,2'b00,2'b10,3'b100};
        LUI:     res = '{1,0,0,0,0,2'b00,2'b11,3'b011};
        AUIPC:   res = '{1,0,0,0,1,2'b00,2'b00,3'b011};
        default: res = '{0,0,0,0,0,2'b00,2'b00,3'b000};
    endcase

    assert(regWriteD === res.regWrite) else $error($realtime, "regWriteD mismatch", err_count++);
    assert(memWriteD === res.memWrite) else $error($realtime, "memWriteD mismatch", err_count++);
    assert(jumpD     === res.jump)     else $error($realtime, "jumpD mismatch", err_count++);
    assert(branchD   === res.branch)   else $error($realtime, "branchD mismatch", err_count++);
    assert(aluSrcD   === res.aluSrc)   else $error($realtime, "aluSrcD mismatch", err_count++);
    assert(aluOp     === res.aluOp)    else $error($realtime, "aluOp mismatch", err_count++);
    assert(resultSrcD=== res.resultSrc)else $error($realtime, "resultSrcD mismatch", err_count++);
    assert(immSrcD   === res.immSrc)   else $error($realtime, "immSrcD mismatch", err_count++);
endfunction

endmodule