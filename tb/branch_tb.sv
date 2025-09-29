//Georges Sfeir
//Branch testbench using coverage, constraint random, and assertions
//Current Coverage: 100%
`timescale 1ns / 10ps

module branch_tb #(parameter NUM_TESTS = 10000);

//branch op corresponding funct3 codes
localparam BEQ = 3'b000;
localparam BNE = 3'b001;
localparam BLT = 3'b100;
localparam BGE = 3'b101;
localparam BLTU = 3'b110;
localparam BGEU = 3'b111;

logic [31:0] rs1;
logic [31:0] rs2;
logic [2:0] funct3;
logic branchD;
logic take_branch;

logic expected_branch = 1'b0;
logic clk = 1'b0;
logic rst = 1'b0;
int err_count = 0;

class input_item;

    rand bit [31:0] rs1;
    rand bit [31:0] rs2;
    rand bit [2:0] funct3;
    randc bit branchD;

    constraint rs1_dist {
        rs1 dist {
            0 :/ 10,
            2**32 - 1:/ 10,
            [1:30] :/ 80
        };
    }
    constraint rs2_dist {
        rs2 dist {
            0 :/ 10,
            2**32 - 1:/ 10,
            [1:2**32-2] :/ 80
        };
    }

    constraint funct3_dist {
        funct3 dist {
            [0:1] :/ 32,
            [2:3] :/ 3, //felt like this was fair
            [4:7] :/ 65
        };
    }
endclass

//could probably cover more cases but I can't think of any rn
covergroup branch_cg @(posedge clk);
    funct3_cp : coverpoint funct3 {
        bins BEQ_BIN = {BEQ};
        bins BNE_BIN = {BNE};
        bins BLT_BIN = {BLT};
        bins BGE_BIN = {BGE};
        bins BLTU_BIN = {BLTU};
        bins BGEU_BIN = {BGEU};
        bins NOFUNCT = {2,3};
    }
    rs1_cp : coverpoint rs1 {
        bins MIN = {0};
        bins MAX = {32'hFFFFFFFF};
        bins RANGE = {[1:32'hFFFFFFFE]};
    }
    rs2_cp : coverpoint rs2 {
        bins MIN = {0};
        bins MAX = {32'hFFFFFFFF};
        bins RANGE = {[1:32'hFFFFFFFE]};
    }
    branchD_cp : coverpoint branchD {
        bins OFF = {0};
        bins ON = {1};
    }
endgroup

branch_cg group;

input_item item;

branch DUT (
    .rs1(rs1),
    .rs2(rs2),
    .funct3(funct3),
    .branchD(branchD),
    .take_branch(take_branch)
);

initial begin : clk_gen
    forever #5 clk <= ~clk;
end

initial begin : reset
    rst <= 1;
    rs1 <= 32'h00000000;
    rs2 <= 32'h00000000;
    funct3 <= 3'b000;
    branchD <= 1'b0;
    #50;
    rst <= 0;
end

initial begin : driver
    //have to hop on UF ECE server for Questa Pro
    group = new;
    item = new;
    $timeformat(-9, 0," ns");
    #75;

    for (int i = 0; i < NUM_TESTS; i++) begin
        assert(item.randomize())
        else $fatal(1, "ERROR: Randomization failed.");
        @(posedge clk);
        rs1 <= item.rs1;
        rs2 <= item.rs2;
        funct3 <= item.funct3;
        branchD <= item.branchD;
    end

    $display("Test completed with %0d errors", err_count);
    $display("Coverage: %0.2f%%", group.get_inst_coverage());
    disable clk_gen;
end

always_comb begin : scoreboard
    if (branchD == 1'b1) begin
        case (funct3)
            BEQ:  expected_branch = (rs1 === rs2) ? 1'b1 : 1'b0;
            BNE:  expected_branch = (rs1 !== rs2) ? 1'b1 : 1'b0;
            BLT:  expected_branch = ($signed(rs1) < $signed(rs2)) ? 1'b1 : 1'b0;
            BGE:  expected_branch = ($signed(rs1) >= $signed(rs2)) ? 1'b1 : 1'b0;
            BLTU: expected_branch = (rs1 < rs2) ? 1'b1 : 1'b0;
            BGEU: expected_branch = (rs1 >= rs2) ? 1'b1 : 1'b0;
            default: expected_branch = 1'b0;
        endcase
    end else begin
        expected_branch = 1'b0;
    end

    assert property (@(posedge clk) disable iff (rst) branchD |-> (expected_branch == take_branch))
    else $error($realtime, "Output mismatch, branchD ENABLED: %0h", funct3, err_count++);
        
    assert property (@(posedge clk) disable iff (rst) !branchD |-> (take_branch == 1'b0))
    else $error($realtime, "Output is true, branchD DISABLED: %0h", funct3, err_count++);
end

endmodule