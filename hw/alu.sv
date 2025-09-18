import alu_pkg::*;

module alu
#(parameter int WIDTH)
(
    input logic [WIDTH-1:0] in1,
    input logic [WIDTH-1:0] in2,
    input logic [4:0]       sel,
    output logic [WIDTH-1:0] out
);

always_comb begin

    
    case(sel)
        add: out = in1 + in2;

        sub: out = in1 - in2;

        sll: begin
            
        end

        srl: begin
            
        end

        sra: begin
            
        end

        and: begin
            
        end

        or: begin
            
        end

        xor: begin
            
        end

        slt: begin
            
        end

        sltu: begin
            
        end

        addi: begin
            
        end

        slli: begin
            
        end

        srli: begin
            
        end

        srai: begin
            
        end

        andi: begin
            
        end

        ori: begin
            
        end

        xori: begin
            
        end

        slti: begin
            
        end

        sltiu: begin
            
        end

        lui: begin
            
        end

        auipc: begin
            
        end
    endcase
end
endmodule