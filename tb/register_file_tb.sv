`timescale 1 ns / 10 ps

module register_file_tb;
localparam WIDTH = 32;
localparam DEPTH = 32;
localparam NUM_TESTS = 10000;

logic clk, rst, wr_en;
logic [$clog2(DEPTH)-1:0] regW, regA, regB;
logic [WIDTH-1:0] portW, portA, portB;
logic [WIDTH-1:0] model_reg [0:DEPTH-1];

register_file #(.WIDTH(WIDTH), .DEPTH(DEPTH)) DUT (.*);

//generating the clock
initial begin : generate_clock
    clk <= 1'b0;
    forever #5 clk <= ~clk;
end

//creating a covegroup to cover all of the edge cases I want
covergroup cg @(posedge clk);
    //reading from each reg
    regA_bin : coverpoint regA { bins all_regs[] = {[0:DEPTH-1]};}
    regB_bin : coverpoint regB { bins all_regs[] = {[0:DEPTH-1]};}

    //writing to each reg when enable is asserted
    regW_bin : coverpoint regW iff (wr_en) {bins all_regs[] = {[0:DEPTH-1]};}

    //writing to reg0
    regW_0_write_bin : coverpoint regW iff (wr_en) {bins x0 = {0};}

    //same read from both ports
    regA_crossregB : cross regA, regB;

    //read and write at same time
    coverpoint wr_en;
    cross wr_en, regA, regW;

endgroup

//updating the model with the same behavior as the DUT
always_ff @(posedge clk) begin

    if(wr_en && regW != 0) model_reg[regW] <= portW;

    if(rst) for(int i = 0; i < DEPTH; i++) model_reg[i] <= '0;
end

cg cg_inst;

//driving the inputs
initial begin : drive_inputs
    cg_inst = new();
    $timeformat(-9, 0, " ns");

    //testing the reset and init the circuit
    rst <= 1'b1;
    wr_en <= 1'b0;
    repeat(5) @(posedge clk);
    rst <= 1'b0;

    //making regA reg0 and reading from portA to see if it's actually 0 and we can't write to it
    //and regB
    regW <= '0;
    regA <= '0;
    regB <= '0;
    portW <= $urandom;
    @(posedge clk);
    assert property (@(posedge clk) portA == '0);
    assert property (@(posedge clk) portB == '0);
    @(posedge clk);

    //reading and writing from the same reg
    regW <= 1;
    portW <= $urandom;
    @(posedge clk);
    portW <= $urandom;
    regA <= 1;
    @(posedge clk);
    //how to check if it's the old value or new value


    //performing rest of tests with random regs
    for(int i = 0; i < NUM_TESTS; i++) begin
        wr_en <= $urandom;
        regW <= $urandom;
        regA <= $urandom;
        regB <= $urandom;
        portW <= $urandom;
        @(posedge clk);
    end

    disable generate_clock;
    $display("Tests completed.");

end


assert property (@(posedge clk) !rst && wr_en |=> portA == model_reg[regA]);
assert property (@(posedge clk) !rst && wr_en |=> portB == model_reg[regB]);
assert property (@(posedge clk) disable iff (rst) !wr_en |=> portB == DUT.regs[regB]);
assert property (@(posedge clk) rst |=> portA == '0);


endmodule