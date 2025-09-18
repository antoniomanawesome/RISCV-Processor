//Parameterized register with active-high asynchronous reset
//https://stitt-hub.com/crafting-clean-reset-logic/

module register
#(parameter int WIDTH = 32)
(
    input logic clk,
    input logic rst,
    input logic en,
    input logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);

always_ff @(posedge clk or posedge rst) begin
    if (en) out <= in;
    if (rst) out <= '0; 
end

endmodule