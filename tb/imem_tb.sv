`timescale 1 ns / 10 ps

module imem_tb;

    localparam WIDTH = 32;
    localparam DEPTH = 32;
    localparam string INIT_FILE = "imem_init.hex";

    logic clk, rst, rd_en;
    logic [31:0] pc;
    logic [WIDTH-1:0] instr;
    int curr_pc;

    logic [WIDTH-1:0] model_mem [0:DEPTH-1];

    imem #(.WIDTH(WIDTH), .DEPTH(DEPTH), .INIT_FILE(INIT_FILE)) DUT (.*);

    initial begin
        $readmemh(INIT_FILE, model_mem);
        $display("Loaded first instr: model_mem[0] = %h", model_mem[0]);
    end

    initial begin : generate_clock
        clk <= 1'b0;
        forever #5 clk <= ~clk;
    end


    /*
    Testing the addr lining up with the contents of file
    Misaligned addr not returning junk values
    output matches hex file output
    */
    initial begin : drive_inputs
        $timeformat(-9, 0, " ns");

        rst <= 1'b1;
        rd_en <= 1'b0;
        pc <= '0;
        repeat(5) @(posedge clk);
        rst <= 1'b0;
        rd_en <= 1'b1;

        //aligned reads
        for(int i = 0; i < 22; i++) begin
            curr_pc = i*4;
            pc <= curr_pc;
            repeat(3) @(posedge clk); //remember that there's a one cycle latency due to registered iaddr_r
            assert(instr == model_mem[i])
            else $error("Mismatch in pc=0%0d: expected %h, got %h", pc, model_mem[i], instr);
        end
        rd_en <= 1'b0;
        repeat(2) @(posedge clk);

        //misaligned
        pc <= 3;
        rd_en <= 1'b1;
        repeat(3) @(posedge clk);
        assert(instr == '0)
        else $error("misaligned addr giving garbo value");

        repeat(2) @(posedge clk);

        //read en
        pc <= '0;
        rd_en <= 1'b0;
        repeat(3) @(posedge clk);
        assert(instr == '0)
        else $error("enable did not behave correctly");

        disable generate_clock;
        $display("Tests completed.");

    end

endmodule