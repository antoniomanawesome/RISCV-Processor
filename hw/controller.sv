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
    logic r_type = (opcode == 7'b0110011);
    logic i_type = (opcode == 7'b0010011);
    logic load = (opcode == 7'b0000011);
    logic store = (opcode == 7'b0100011);
    logic branch = (opcode == 7'b1100011);
    logic jalr = (opcode == 7'b1100111);
    logic jal = (opcode == 7'b1101111);
    logic lui = (opcode == 7'b0110111);
    logic auipc = (opcode == 7'b0010111);

    always_comb begin

        regWriteD = 1'b0;
        memWriteD = 1'b0;
        jumpD = 1'b0;
        branchD = 1'b0;
        aluSrcD = 1'b0;
        aluOp = 2'b00;
        resultSrcD = 2'b00;
        immSrcD = 3'b000;

        case(1'b1)

            r_type: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b0;
                aluOp = 2'b10;
                resultSrcD = 2'b00;
                immSrcD = 3'bxxx;
            end

            i_type: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b10;
                resultSrcD = 2'b00;
                immSrcD = 3'b000;
            end

            load: begin
                regWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                resultSrcD = 2'b01;
                immSrcD = 3'b000;
            end

            store: begin
                memWriteD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                immSrcD = 3'b001;
            end

            branch: begin
                branchD = 1'b1;
                aluSrcD = 1'b0;
                aluOp = 2'b01;
                immSrcD = 3'b010;
            end

            jalr: begin
                regWriteD = 1'b1;
                jumpD = 1'b1;
                aluSrcD = 1'b1;
                aluOp = 2'b00;
                resultSrcD = 2'b10;
                immSrcD = 3'b000;
            end

            jal: begin
                regWriteD = 1'b1;
                jumpD = 1'b1;
                resultSrcD = 2'b10;
                immSrcD = 3'b100;
            end

            lui: begin
                regWriteD = 1'b1;
                resultSrcD = 2'b11;
                immSrcD = 3'b011;
            end

            auipc: begin
                regWriteD  = 1'b1;
                aluSrcD    = 1'b1;
                aluOp     = 2'b00;
                resultSrcD = 2'b00;
                immSrcD    = 3'b011;
            end

            default: begin
                //default values
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