`timescale 1 ns / 100 ps

import alu_pkg::*;

module alu_tb #(
    parameter int WIDTH = 32
);
    logic [WIDTH-1:0] rs1;
    logic [WIDTH-1:0] rs2;
    logic [31:0]      imm;
    logic [4:0]       sel;
    logic [WIDTH-1:0] pc;
    logic [WIDTH-1:0] rd;

    logic [WIDTH-1:0] expected;

    alu #(WIDTH) alu_inst (.*);

    // create a model for the ALU operations
    function automatic logic [WIDTH-1:0] alu_model(
        input logic [WIDTH-1:0] rs1,
        input logic [WIDTH-1:0] rs2,
        input logic [31:0]      imm,
        input logic [4:0]       sel,
        input logic [WIDTH-1:0] pc
    );
        case (sel)
            add: return rs1 + rs2;
            sub: return rs1 - rs2;
            sll: return rs1 << rs2[4:0];
            srl: return rs1 >> rs2[4:0];
            sra: return $signed(rs1) >>> rs2[4:0];
            aand: return rs1 & rs2;
            oor: return rs1 | rs2;
            xxor: return rs1 ^ rs2;
            slt: return ($signed(rs1) < $signed(rs2)) ? 1 : 0;
            sltu: return (rs1 < rs2) ? 1 : 0;
            addi: return rs1 + imm[11:0];
            slli: return rs1 << imm[4:0];
            srli: return rs1 >> imm[4:0];
            srai: return $signed(rs1) >>> imm[4:0];
            andi: return rs1 & imm[11:0];
            ori: return rs1 | imm[11:0];
            xori: return rs1 ^ imm[11:0];
            slti: return ($signed(rs1) < $signed(imm[11:0])) ? 1 : 0;
            sltiu: return (rs1 < imm[11:0]) ? 1 : 0;
            lui: return {imm[31:12], 12'b0};
            auipc: return pc + {imm[31:12], 12'b0};
            default: return '0;
        endcase
    endfunction

    initial begin
        $timeformat(-9, 0, " ns");

        for (int i = 0; i < 100; i++) begin
            rs1 <= $urandom;
            rs2 <= $urandom;
            imm <= $urandom;
            pc  <= $urandom;
            sel <= $urandom;
            #10;

            // test the operations with the model
            expected = alu_model(rs1, rs2, imm, sel, pc);

            if (rd != expected) begin
                $error("Mismatch for sel=%0d: rs1=%0h, rs2=%0h, imm=%0h, pc=%0h => got rd=%0h, expected rd=%0h",
                       sel, rs1, rs2, imm, pc, rd, expected);
            end else begin
                $display("Match for sel=%0d: rs1=%0h, rs2=%0h, imm=%0h, pc=%0h => rd=%0h",
                         sel, rs1, rs2, imm, pc, rd);
            end
        end

        $display("Done.");
    end

endmodule