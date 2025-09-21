//https://stitt-hub.com/crafting-clean-reset-logic/

//program counter!

module pc
#(parameter int WIDTH = 32)
(
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] next_pc, //calculated from the ctrl/branch/jump we do
    output logic [WIDTH-1:0] curr_pc
);

always_ff @(posedge clk or posedge rst) begin
    curr_pc <= next_pc;
    if(rst) curr_pc <= '0;
end

endmodule