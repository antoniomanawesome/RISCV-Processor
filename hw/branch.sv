//branch decision unit, depends on branchD from controller.sv & funct3 from instruction
// NOTE: needs prediction logic added for pipelining

module branch (
    input logic [31:0] rs1,
    input logic [31:0] rs2,
    input logic [2:0] funct3,
    input logic branchD,
    output logic take_branch
);

//branch op corresponding funct3 codes
localparam BEQ = 3'b000;
localparam BNE = 3'b001;
localparam BLT = 3'b100;
localparam BGE = 3'b101;
localparam BLTU = 3'b110;
localparam BGEU = 3'b111;

always_comb begin
    take_branch = 1'b0;
    if (branchD) begin
        case (funct3)
            BEQ: take_branch = (rs1 == rs2);
            BNE: take_branch = (rs1 != rs2);
            BLT: take_branch = ($signed(rs1) < $signed(rs2));
            BGE: take_branch = ($signed(rs1) >= $signed(rs2));
            BLTU: take_branch = (rs1 < rs2);
            BGEU: take_branch = (rs1 >= rs2);
            default: take_branch = 1'b0;
        endcase
    end
end

endmodule