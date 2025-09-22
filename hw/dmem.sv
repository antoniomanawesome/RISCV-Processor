module dmem 
#(parameter WIDTH = 32, parameter int DEPTH = 32) 
(
    input  logic               clk,
    input  logic               rst,
    input  logic [31:0]        addr,      
    input  logic [31:0]        wdata,  
    input  logic [2:0]         funct3,    
    input  logic               mem_read,  
    input  logic               mem_write,
    output logic [31:0]        rdata      
);

    logic [7:0] memory [0:DEPTH-1]; 

    logic [DEPTH-1:0] addr_r; 
    logic [31:0] rdata_r;            

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            addr_r <= '0;
            rdata_r <= '0;
        end else begin     
            if (mem_write) begin
                if (addr[1:0] != 2'b00) begin
                    $display("ERROR: Misaligned data memory address for write.");
                end else begin
                    addr_r <= addr[31:2];
                    case(funct3)
                        3'b000: begin // SB
                            memory[addr_r] <= wdata[7:0];
                        end
                        3'b001: begin // SH
                            memory[addr_r] <= wdata[7:0];
                            memory[addr_r + 1] <= wdata[15:8];
                        end
                        3'b010: begin // SW
                            memory[addr_r] <= wdata[7:0];
                            memory[addr_r + 1] <= wdata[15:8];
                            memory[addr_r + 2] <= wdata[23:16];
                            memory[addr_r + 3] <= wdata[31:24];
                        end
                    endcase
                end
            end
            if (mem_read) begin
                if (addr[1:0] != 2'b00) begin
                    rdata_r <= 32'b0;
                    $display("ERROR: Misaligned data memory address for read.");
                end else begin
                    addr_r <= addr[31:2];
                    case(funct3)
                        3'b000: begin // LB
                            rdata_r <= {{24{memory[addr_r + 3][7]}}, memory[addr_r + 3]};
                        end
                        3'b001: begin // LH
                            rdata_r <= {{16{memory[addr_r + 3][7]}}, memory[addr_r + 3], memory[addr_r + 2]};
                        end
                        3'b010: begin // LW
                            rdata_r <= {memory[addr_r + 3], memory[addr_r + 2], memory[addr_r + 1], memory[addr_r]};
                        end
                        3'b100: begin // LBU
                            rdata_r <= {24'b0, memory[addr_r + 3]};
                        end
                        3'b101: begin // LHU
                            rdata_r <= {16'b0, memory[addr_r + 3], memory[addr_r + 2]};
                        end
                    endcase
                end
            end
            
        end
    end

    assign rdata = rdata_r;

endmodule