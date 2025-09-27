`timescale 1ns / 10ps

module branch_tb;

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

logic clk = 1'b0;
logic rst = 1'b0;
int err_count = 0;

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
    $timeformat(-9, 0," ns");
    #100;

    for (int i = 0; i < 8; i++) begin //since funct3 is 3 bits
        funct3 <= i;
        branchD <= 1'b1;
        //need to implement CRV dist for branchD, rs1 & rs2 to get 100% coverage
        rs1 <= 32'h6785319A;
        rs2 <= 32'h08880219;
        @(posedge clk);
        scoreboard(rs1, rs2, funct3, branchD, take_branch);
    end

    $display("Test completed with %0d errors", err_count);
    disable clk_gen;
end

function void scoreboard(logic [31:0] rs1, logic [31:0] rs2, logic [2:0] funct3, logic branchD, logic take_branch);

    logic expected_branch;

    case (funct3)
        BEQ:  expected_branch = (rs1 == rs2);
        BNE:  expected_branch = (rs1 != rs2);
        BLT:  expected_branch = ($signed(rs1) < $unsigned(rs2));
        BGE:  expected_branch = ($signed(rs1) >= $unsigned(rs2));
        BLTU: expected_branch = (rs1 < rs2);
        BGEU: expected_branch = (rs1 >= rs2);
        default: expected_branch = 1'b0;
    endcase

    assert(expected_branch === take_branch) else $error($realtime, "take_branch mismatch for funct3: %0h", funct3, err_count++);
endfunction


endmodule