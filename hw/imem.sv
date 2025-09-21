//creating instruction memory (where we put our file with the things we want to run)

module imem
#(parameter int WIDTH = 32, parameter int DEPTH = 32)
(
    input logic [WIDTH-1:0] iaddr, //instruction address aka program counter
    // add read enable?
    output logic [WIDTH-1:0] instr //instruction
);

logic [WIDTH-3:0] address = '0;
logic [WIDTH-1:0] memory [0:DEPTH-1] = '0;

always_comb begin
    if (iaddr[7:0] != 0) begin
        instr = '0;
        $display("ERROR: Misaligned instruction memory address.")
    end else begin
        address = (iaddr >> 2);
        instr = memory[address];
    end
end

endmodule