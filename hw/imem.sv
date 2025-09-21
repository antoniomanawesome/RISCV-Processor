//creating instruction memory (where we put our file with the things we want to run)

module imem
#(parameter int WIDTH = 32, parameter int DEPTH = 65536, parameter string INIT_FILE = "../init/imem_initialization.hex")
(
    input logic clk,
    input logic rst,
    input logic rd_en,
    input logic [31:0] iaddr, //instruction address aka program counter
    output logic [WIDTH-1:0] instr //instruction
);

logic [WIDTH-1:0] memory [0:DEPTH-1];

logic [$clog2(DEPTH)-1:0] iaddr_r;  //16 bit address register
logic [WIDTH-1:0] instr_r;

initial begin
    if (INIT_FILE != "") $readmemh(INIT_FILE, memory);
end

always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
        iaddr_r <= '0;
        instr_r <= '0;
    end else if (rd_en) begin
        if (iaddr_r[1:0] != 2'b00) begin
            instr_r <= '0;
            $display("ERROR: Misaligned instruction memory address.");
        end else begin
            iaddr_r <= iaddr[31:2];
            instr_r <= memory[iaddr_r];
        end
    end
end

assign instr = instr_r;

endmodule