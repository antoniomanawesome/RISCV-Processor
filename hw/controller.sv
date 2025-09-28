module controller
(
    input logic[6:0] opcode,
    
    output logic regWriteD,
    output logic memWriteD,
    output logic jumpD,
    output logic branchD,
    output logic aluSrcD,
    output logic[1:0] aluOp,
    output logic[1:0] resultSrcD,
    output logic[2:0] immSrcD
);

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

    always_comb begin

        regWriteD = 1'b0;
        memWriteD = 1'b0;
        jumpD = 1'b0;
        branchD = 1'b0;
        aluSrcD = 1'b0;
        aluOp = 2'b00;
        resultSrcD = 2'b00;
        immSrcD = 3'b000;

        case(opcode)

            R_TYPE: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b0;
                aluOp = 2'b10;
                resultSrcD = 2'b00;
                immSrcD = 3'bxxx;
            end

            I_TYPE: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b10;
                resultSrcD = 2'b00;
                immSrcD = 3'b000;
            end

            LOAD: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                resultSrcD = 2'b01;
                immSrcD = 3'b000;
            end

            STORE: begin
                memWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                immSrcD = 3'b001;
            end

            BRANCH: begin
                branchD = 1'b1;
                aluSrcD = 1'b0;
                aluOp = 2'b01;
                immSrcD = 3'b010;
            end

            JALR: begin
                regWriteD = 1'b1;
                jumpD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                resultSrcD = 2'b10;
                immSrcD = 3'b000;
            end

            JAL: begin
                regWriteD = 1'b1;
                jumpD = 1'b1;
                resultSrcD = 2'b10;
                immSrcD = 3'b100;
            end

            LUI: begin
                regWriteD = 1'b1;
                resultSrcD = 2'b11;
                immSrcD = 3'b011;
            end

            AUIPC: begin
                regWriteD  = 1'b1;
                aluSrcD    = 1'b1;
                aluOp     = 2'b00;
                resultSrcD = 2'b00;
                immSrcD    = 3'b011;
            end

            default: begin
                regWriteD = 1'b0;
                memWriteD = 1'b0;
                jumpD = 1'b0;
                branchD = 1'b0;
                aluSrcD = 1'b0;
                aluOp = 2'b00;
                resultSrcD = 2'b00;
                immSrcD = 3'b000;
            end
        endcase
    end

endmodule