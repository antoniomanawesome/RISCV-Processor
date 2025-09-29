//creating instruction memory (where we put our file with the things we want to run)
//if vivado doesn't infer the bram, remove the rst
//good to note that async reads will infer LUT ram

module imem
#(parameter int WIDTH = 32, parameter int DEPTH = 32, parameter string INIT_FILE = "../init/imem_init.hex")
(
    input logic clk,
    input logic rst,
    input logic rd_en,
    input logic [31:0] pc, //instruction address
    output logic [WIDTH-1:0] instr
);

logic [WIDTH-1:0] memory [0:DEPTH-1];

logic [$clog2(DEPTH)-1:0] iaddr_r;
logic [WIDTH-1:0] instr_r;

initial begin
    if (INIT_FILE != "") $readmemh(INIT_FILE, memory);
end

always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
        iaddr_r <= '0;
        instr_r <= '0;
    end else if (rd_en) begin
        if (pc[1:0] != 2'b00) begin
            instr_r <= '0;
            $display("ERROR: Misaligned instruction memory address: %h", pc);
        end else begin
            iaddr_r <= pc[$clog2(DEPTH)+1:2];
            instr_r <= memory[iaddr_r]; //one cycle delay (which vivado bram prefers)
        end
    end
end

assign instr = instr_r;

endmodule