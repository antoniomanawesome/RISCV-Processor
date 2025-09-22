module alu_control
(
    input logic[1:0] aluOp,
    input logic[2:0] funct3,
    input logic[6:0] funct7,
    output logic[4:0] aluControl
);

localparam ALU_ADD  = 5'b00000;
localparam ALU_SUB  = 5'b00001;
localparam ALU_AND  = 5'b00010;
localparam ALU_OR   = 5'b00011;
localparam ALU_XOR  = 5'b00100;
localparam ALU_SLT  = 5'b00101;
localparam ALU_SLTU = 5'b00110;
localparam ALU_SLL  = 5'b00111;
localparam ALU_SRL  = 5'b01000;
localparam ALU_SRA  = 5'b01001;
localparam ALU_NOP  = 5'b11111;

always_comb begin
    aluControl = ALU_NOP;

    case (aluOp)

        //load/store/addi
        2'b00: aluControl = ALU_ADD;

        //use funct3 to decide branch type alu op
        2'b01: begin
            case (funct3)
                3'b000: aluControl = ALU_SUB;  // beq
                3'b001: aluControl = ALU_SUB;  // bne
                3'b100: aluControl = ALU_SLT;  // blt
                3'b101: aluControl = ALU_SLT;  // bge
                3'b110: aluControl = ALU_SLTU; // bltu
                3'b111: aluControl = ALU_SLTU; // bgeu
                default: aluControl = ALU_NOP;
            endcase
        end

        //use funct3 and funct7 to decide r/i type alu op
        2'b10: begin
            case (funct3)
                3'b000: begin
                    if (funct7 == 7'b0100000)
                        aluControl = ALU_SUB;
                    else
                        aluControl = ALU_ADD;
                end
                3'b111: aluControl = ALU_AND;
                3'b110: aluControl = ALU_OR;
                3'b100: aluControl = ALU_XOR;
                3'b010: aluControl = ALU_SLT;
                3'b011: aluControl = ALU_SLTU;
                3'b001: aluControl = ALU_SLL;
                3'b101: begin
                    if (funct7 == 7'b0100000)
                        aluControl = ALU_SRA;
                    else
                        aluControl = ALU_SRL;
                end
                default: aluControl = ALU_NOP;
            endcase
        end

        default: aluControl = ALU_NOP;

    endcase
end

endmodule