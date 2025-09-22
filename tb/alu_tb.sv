`timescale 1 ns / 100 ps

module alu_tb #(
    parameter int WIDTH = 32
);
    logic [WIDTH-1:0] rs1;
    logic [WIDTH-1:0] rs2;
    logic [31:0]      imm;
    logic [4:0]       sel;
    logic [WIDTH-1:0] pc;
    logic [WIDTH-1:0] rd;

    alu #(WIDTH) alu_inst (.*);

    initial begin
        $timeformat(-9, 0, " ns");

        $display("Done.");
    end

endmodule