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

logic [WIDTH-1:0] regs [0:DEPTH-1];

//Write port
always_ff @(posedge clk or posedge rst) begin

    if (rst) begin
        for (int i = 0; i < DEPTH; i++) begin
            regs[i] <= '0;
        end
    end 
    else if (wr_en && (regW != 0)) begin
        regs[regW] <= portW;
    end

end

//Read ports
assign portA = (regA == 0) ? '0 : (wr_en == 1'b1) ? portA : regs[regA];
assign portB = (regB == 0) ? '0 : (wr_en == 1'b1) ? portB : regs[regB];

endmodule