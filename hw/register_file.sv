//Register file, 32-bit wide, 31 registers

module register_file
#(parameter int WIDTH = 32, parameter int DEPTH = 31)
(
    input logic clk,
    input logic rst,
    input logic wr_en,
    input logic [$clog2(DEPTH)-1:0] regW,
    input logic [$clog2(DEPTH)-1:0] regA,
    input logic [$clog2(DEPTH)-1:0] regB,
    input logic [WIDTH-1:0] portW,
    output logic [WIDTH-1:0] portA,
    output logic [WIDTH-1:0] portB
);



endmodule