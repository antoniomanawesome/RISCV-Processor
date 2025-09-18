import alu_pkg::*;

module alu
#(parameter int WIDTH)
(
    input logic [WIDTH-1:0] rs1,
    input logic [WIDTH-1:0] rs2,
    input logic [31:0]      imm,
    input logic [4:0]       sel,
    input logic [WIDTH-1:0] pc,
    output logic [WIDTH-1:0] rd
);

always_comb begin
    case(sel)
        add: rd = rs1 + rs2;
        sub: rd = rs1 - rs2;
        sll: rd = rs1 << rs2[4:0];
        srl: rd = rs1 >> rs2[4:0];
        sra: rd = $signed(rs1) >>> rs2[4:0];
        aand: rd = rs1 & rs2;
        oor: rd = rs1 | rs2;
        xxor: rd = rs1 ^ rs2;
        slt: rd = ($signed(rs1) < $signed(rs2)) ? 1 : 0;
        sltu: rd = (rs1 < rs2) ? 1 : 0;
        addi: rd = rs1 + imm[11:0];
        slli: rd = rs1 << imm[4:0];
        srli: rd = rs1 >> imm[4:0];
        srai: rd = $signed(rs1) >>> imm[4:0];
        andi: rd = rs1 & imm[11:0];
        ori: rd = rs1 | imm[11:0];
        xori: rd = rs1 ^ imm[11:0];
        slti: rd = ($signed(rs1) < $signed(imm[11:0])) ? 1 : 0;
        sltiu: rd = (rs1 < imm[11:0]) ? 1 : 0;
        lui: rd = {imm[31:12], 12'b0};
        auipc: rd = pc + {imm[31:12], 12'b0};
        default: rd = '0;
    endcase
end

endmodule