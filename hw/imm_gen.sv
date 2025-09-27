module imm_gen
(
    input logic[31:0] instr,
    input logic[2:0] immSrc,
    output logic[31:0] immOut
);

localparam I_TYPE = 3'b000;
localparam S_TYPE = 3'b001;
localparam B_TYPE = 3'b010;
localparam U_TYPE = 3'b011;
localparam J_TYPE = 3'b100;

always_comb begin
    case (immSrc)
        I_TYPE:
            immOut = {{20{instr[31]}}, instr[31:20]};
        S_TYPE:
            immOut = {{20{instr[31]}}, instr[31:25], instr[11:7]};
        B_TYPE:
            immOut = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
        U_TYPE:
            immOut = {instr[31:12], 12'b0};
        J_TYPE:
            immOut = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};
        default:
            immOut = 32'b0;
    endcase
end

endmodule