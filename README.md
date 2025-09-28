# RISCV-Processor
This project is a custom-built 32-bit RISC-V CPU written in SystemVerilog, designed from the ground up to run on FPGA hardware.
The datapath is currently multicycle RV32I Base ISA

<img width="892" height="459" alt="datapathrv" src="https://github.com/user-attachments/assets/fcf2f006-d8d4-4272-b457-544d77f0e059" />

**Current completed components:**
ALU, ALU Control Unit, Controller, Data Memory, Instruction Memory, Immediate Value Generator, Program Counter, Register File

**To Do:**
Branch Unit, Top Level Arch, Execute a real RISCV program on PYNQ-Z2 SoC using our CPU datapath design

**Future Plans:**
Pipelining the datapath and running that on the board as well
