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
localparam BEQ = 3'h0;
localparam BNE = 3'h1;
localparam BLT = 3'h4;
localparam BGE = 3'h5;
localparam BLTU = 3'h6;
localparam BGEU = 3'h7;

always_comb begin
    take_branch = 1'b0;
    if (branchD) begin
        case (funct3)
            BEQ: take_branch = (rs1 === rs2) ? 1'b1 : 1'b0;
            BNE: take_branch = (rs1 !== rs2) ? 1'b1 : 1'b0;
            BLT: take_branch = ($signed(rs1) < $signed(rs2)) ? 1'b1 : 1'b0;
            BGE: take_branch = ($signed(rs1) >= $signed(rs2)) ? 1'b1 : 1'b0;
            BLTU: take_branch = (rs1 < rs2) ? 1'b1 : 1'b0;
            BGEU: take_branch = (rs1 >= rs2) ? 1'b1 : 1'b0;
            default: take_branch = 1'b0;
        endcase
    end
end

endmodule