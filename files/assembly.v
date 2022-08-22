module DataPath(
  input clk,
  output [31:0] pc_r,
  output ewreg,
  output em2reg,
  output ewmem,
  output ealuimm,
  output [3:0] ealuc,
  output [4:0] edest_reg,
  output [31:0] eqa,
  output [31:0] eqb,
  output [31:0] eimm32,
  output mwreg,
  output mm2reg,
  output mwmem,
  output [31:0] mr,
  output [31:0] mqb,
  output [4:0] mdestreg,
  output wwreg,
  output wm2reg,
  output [4:0] wdestreg,
  output [31:0] wr,
  output [31:0] wdo
);
  wire [31:0] add_rs, inst, dinst;
  wire wreg, m2reg, wmem, aluimm, regrt;
  wire [3:0] aluc_dp;
  wire [4:0] dest_reg;
  wire [31:0] qa_dp, qb_dp, imm32;
  wire [31:0] mdo;

module Immediate_Extender(
  input [31:0] dinst_out,
  output reg [31:0] imm32
);
  wire [15:0] imm = dinst_out[15:0];
  always@(imm) begin
    imm32 <= {{16{imm[15]}}, imm[15:0]};
  end
endmodule

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 05/18/2020 12:27:00 PM
// Design Name: 
// Module Name: testbench
// Project Name: 7 segment display
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Create Date: 2022/02/06 21:23:55
// Module Name: test_bench
// 
//////////////////////////////////////////////////////////////////////////////////

    assign (strong1, weak0) GSR = GSR_int;
    assign (strong1, weak0) GTS = GTS_int;
    assign (weak1, weak0) PRLD = PRLD_int;

// "Instruction memory"
module InstMem(input [31:0] pc, output reg [31:0] inst_out);
  reg [31:0] memory [0:63];
  initial begin
    memory[25] <= 32'b10001100001000100000000000000000;
    memory[26] <= 32'b10001100001000110000000000000100;    
  end  
  always @ (pc)
  begin
    inst_out <= memory[pc[31:2]];
  end
endmodule

module Register_File(
  input clk,
  input [4:0] wdestreg,
  input [31:0] wbdata,
  input wwreg,
  input [31:0] dinst_out,
  output reg [31:0] qa,
  output reg [31:0] qb
);
  reg [31:0] registers;
  integer i;

module DataPath(
  input clk,
  output [31:0] pc_r,
  output ewreg,
  output em2reg,
  output ewmem,
  output ealuimm,
  output [3:0] ealuc,
  output [4:0] edest_reg,
  output [31:0] eqa,
  output [31:0] eqb,
  output [31:0] eimm32,
  output mwreg,
  output mm2reg,
  output mwmem,
  output [31:0] mr,
  output [31:0] mqb,
  output [4:0] mdestreg,
  output wwreg,
  output wm2reg,
  output [4:0] wdestreg,
  output [31:0] wr,
  output [31:0] wdo
);
  wire [31:0] add_rs, inst, dinst;
  wire wreg, m2reg, wmem, aluimm, regrt;
  wire [3:0] aluc_dp;
  wire [4:0] dest_reg;
  wire [31:0] qa_dp, qb_dp, imm32;
  wire [31:0] mdo;
  wire [31:0] wb_out;

// Module      : Up/Down Counter
// Description : Combinational circuit that generates the next state and LED control signals based on input u
// Input(s)    : 3-bit Current State, 1-bit u
// Output(s)   : 3-bit Next State, 7 1-bit segments of the LED
module counter(input [2:0] q, input u, output reg [2:0] ns, 
       output reg a, output reg b, output reg c, output reg d, output reg e, output reg f, output reg g );
   always @(*)
        begin     
            if (u == 1) begin  
                if (q == 3'b101) begin
                    ns <= 3'b000;
                end
                else begin 
                    ns <= q + 1;
                end
            end
            else begin 
                if (q == 3'b000) begin
                    ns <= 3'b101;
                end
                else begin 
                    ns <= q - 1;
                end
            end      
        case(q)
            3'b000: begin
                g=1'b1;  f=1'b0;  e=1'b0;  d=1'b0;  c=1'b0;  b=1'b0;  a=1'b0;
            end
            3'b001: begin
                g=1'b1;  f=1'b1;  e=1'b1;  d=1'b1;  c=1'b0;  b=1'b0;  a=1'b1;
            end
            3'b010: begin
                g=1'b0;  f=1'b1;  e=1'b0;  d=1'b0;  c=1'b1  ;b=1'b0;  a=1'b0;
            end
            3'b011: begin 
                g=1'b0;  f=1'b1;  e=1'b1;  d=1'b0;  c=1'b0;  b=1'b0;  a=1'b0;
            end
            3'b100: begin
                g=1'b0;  f=1'b0;  e=1'b1;  d=1'b1;  c=1'b0;  b=1'b0;  a=1'b1;
            end
            3'b101: begin
                g=1'b0;  f=1'b0;  e=1'b1;  d=1'b0;  c=1'b0;  b=1'b1;  a=1'b0;
            end       
        endcase
   end
endmodule

// Module      : Testbench
// Description : Using the test sequence given generate the output of the 7 segment display by calling dff3 and counter modules
module testbench();
    reg clrn_tb;
    reg clk_tb;
    reg u_tb;
    wire [2:0] q_tb;
    wire [2:0] ns_tb;
    wire a,b,c,d,e,f,g;
    dff3 dff3_tb(ns_tb, clrn_tb, clk_tb, q_tb);
    counter counter_tb(q_tb, u_tb, ns_tb, a, b, c, d, e, f, g);
    initial begin
        clrn_tb = 0;        
        clk_tb = 1;
        u_tb = 1; 
        #1 clrn_tb = 1;
        #16 u_tb = 0;        
    end   
    always begin
        #1;
        clk_tb = ~clk_tb;
    end
endmodule

    reg JTAG_CAPTURE_GLBL;
    reg JTAG_RESET_GLBL;
    reg JTAG_SHIFT_GLBL;
    reg JTAG_UPDATE_GLBL;
    reg JTAG_RUNTEST_GLBL;

    reg JTAG_SEL1_GLBL = 0;
    reg JTAG_SEL2_GLBL = 0 ;
    reg JTAG_SEL3_GLBL = 0;
    reg JTAG_SEL4_GLBL = 0;

module PC_Adder(
  input [31:0] pc,
  output reg [31:0] new
);
  initial begin
    new <= 32'd100;
  end
  always @(pc) begin
    new <= pc + 32'd4;
  end
endmodule

module glbl ();

  // ===== Lab 4 =====
  wire mwreg, mm2reg, mwmem;
  wire [31:0] mr, mqb;
  wire [4:0] mdestreg;
  wire wwreg, wm2reg;
  wire [31:0] wr, wdo;
  wire [4:0] wdestreg;
  // ===== Lab 4 =====

module Register_File(
  input [31:0] dinst_out,
  output reg [31:0] qa,
  output reg [31:0] qb
);
  reg [31:0] registers;
  integer i;

    initial begin
	GTS_int = 1'b1;
	#(TOC_WIDTH)
	GTS_int = 1'b0;
    end

    parameter ROC_WIDTH = 100000;
    parameter TOC_WIDTH = 0;

  PC pc_dp(clk, add_rs, pc_r);
  PC_Adder adder_dp(pc_r, add_rs);
  InstMem im_dp(pc_r, inst);
  IF_ID ifid_dp(clk, inst, dinst);
  Control_Unit cu_dp(dinst, wreg, m2reg, wmem, aluc_dp, aluimm, regrt);
  Regrt_Multiplexer mult_dp(dinst, regrt, dest_reg);
  Register_File rf_dp(dinst, qa_dp, qb_dp);
  Immediate_Extender ie_dp(dinst, imm32);
  ID_EXE idexe_dp(clk, wreg, m2reg, wmem, aluc_dp, aluimm, dest_reg, qa_dp, qb_dp, imm32, ewreg, em2reg, ewmem, ealuc, ealuimm, edest_reg, eqa, eqb, eimm32);
endmodule


// Program counter
module PC(
  input clk,
  input [31:0] new_addr,
  output reg [31:0] pc
);
  always @(posedge clk) begin
    pc <= new_addr;
  end
endmodule

module Control_Unit(
  // Decomposed into op and func
  input [31:0] dinst_out,
  output reg wreg,
  output reg m2reg,
  output reg wmem,
  output reg [3:0] aluc,
  output reg aluimm,
  output reg regrt
);
  reg [5:0] op;
  reg [5:0] func;
  always @ (dinst_out) begin
    op <= dinst_out[31:26];
    func <= dinst_out[5:0];
    case(op)
      // r-type
      6'b000000: begin
        case(func)
          // TODO
        endcase
      end
      // lw
      6'b100011: begin
        wreg = 1'b1;
        m2reg = 1'b1;
        wmem = 1'b0;
        aluc = 4'b0010;
        aluimm = 1'b1;
        regrt = 1'b1;
      end
    endcase
  end
endmodule

module ID_EXE(
  input clk,
  input wreg,
  input m2reg,
  input wmem,
  input [3:0] aluc,
  input aluimm,
  input [4:0] dest_reg,
  input [4:0] qa,
  input [4:0] qb,
  input [31:0] imm32,
  output reg ewreg,
  output reg em2reg,
  output reg ewmem,
  output reg [3:0] ealuc,
  output reg ealuimm, 
  output reg [4:0] edest_reg,
  output reg [31:0] eqa,
  output reg [31:0] eqb,
  output reg [31:0] eimm32
);
  always@(posedge clk) begin
    ewreg <= wreg;
    em2reg <= m2reg;
    ewmem <= wmem;
    ealuc <= aluc;
    ealuimm <= aluimm;
    edest_reg <= dest_reg;
    eqa <= qa;
    eqb <= qb;
    eimm32 <= imm32;
  end
endmodule

module ExememPipe(
  input clk,
  input ewreg,
  input em2reg,
  input ewmem,
  input [4:0] edestreg,
  input [31:0] alul_out,
  input [31:0] eqb,
  output reg mwreg,
  output reg mm2reg,
  output reg mwmem,
  output reg [4:0] mdestreg,
  output reg [31:0] mr,
  output reg [31:0] mqb
);
  always @(posedge clk) begin
    mwreg = ewreg;
    mm2reg = em2reg;
    mwmem = ewmem;
    mdestreg = edestreg;
    mr = alul_out;
    mqb = eqb;
  end
endmodule 

module ALU_Logic(
  input [31:0] eqa,
  input [31:0] alu_out,
  input [3:0] ealuc,
  output reg [31:0] alul_out
);
  always @(*) begin
    if (ealuc == 4'b0000) begin
      alul_out <= eqa & alu_out;
    end else if (ealuc == 4'b0001) begin
      alul_out <= eqa | alu_out;
    end else if (ealuc == 4'b0010) begin
      alul_out <= eqa + alu_out;
    end else if (ealuc == 4'b0110) begin
      alul_out <= eqa - alu_out;
    end else if (ealuc == 4'b0111) begin
      alul_out <= eqa < alu_out ? 1:0;
    end else if (ealuc == 4'b1100) begin
      alul_out <= ~(eqa | alu_out);
    end
  end
endmodule 

  PC pc_dp(clk, add_rs, pc_r);
  PC_Adder adder_dp(pc_r, add_rs);
  InstMem im_dp(pc_r, inst);
  IF_ID ifid_dp(clk, inst, dinst);
  Control_Unit cu_dp(dinst, wreg, m2reg, wmem, aluc_dp, aluimm, regrt);
  Regrt_Multiplexer mult_dp(dinst, regrt, dest_reg);
  Register_File rf_dp(clk, wdestreg, wb_out, wwreg, dinst, qa_dp, qb_dp);
  WriteBack_Mux wb(wm2reg, wr, wdo, wb_out);
  Immediate_Extender ie_dp(dinst, imm32);
  ID_EXE idexe_dp(clk, wreg, m2reg, wmem, aluc_dp, aluimm, dest_reg, qa_dp, qb_dp, imm32, ewreg, em2reg, ewmem, ealuc, ealuimm, edest_reg, eqa, eqb, eimm32);

//--------   STARTUP Globals --------------
    wire GSR;
    wire GTS;
    wire GWE;
    wire PRLD;
    tri1 p_up_tmp;
    tri (weak1, strong0) PLL_LOCKG = p_up_tmp;

module DataPath(
  input clk,
  output [31:0] pc_r,
  output ewreg,
  output em2reg,
  output ewmem,
  output ealuimm,
  output [3:0] ealuc,
  output [4:0] edest_reg,
  output [31:0] eqa,
  output [31:0] eqb,
  output [31:0] eimm32
);
  wire [31:0] add_rs, inst, dinst;
  wire wreg, m2reg, wmem, aluimm, regrt;
  wire [3:0] aluc_dp;
  wire [4:0] dest_reg;
  wire [31:0] qa_dp, qb_dp, imm32;

module MEMWB(
  input clk,
  input mwreg,
  input mm2reg,
  input [4:0] mdestreg,
  input [31:0] mr,
  input [31:0] mdo,
  output reg wwreg,
  output reg wm2reg,
  output reg [4:0] wdestreg,
  output reg [31:0] wr,
  output reg [31:0] wdo
);
  always @(posedge clk) begin
    wwreg = mwreg;
    wm2reg = mm2reg;
    wdestreg = mdestreg;
    wr = mr;
    wdo = mdo;
  end 
endmodule 

  // Local states
  reg [31:0] reg_q;
  reg [15:0] reg_r;
  reg [15:0] reg_b;
  reg [4:0] count;

`timescale 1ns / 1ps
// Module      : D flip-flop
// Description : At the positive edge of the clock, set the current state based on the clear
// Input(s)    : 3-bit Next State, Clear and Clock
// Output(s)   : 3-bit Current State
module dff3(input [2:0] ns, input clrn, input clk, output reg [2:0] q);
    always @ (posedge clk)
        begin
            if (clrn == 1) begin
                q <= ns;
            end
            else begin
                q <= 3'b000;
            end
        end
endmodule

module test_bench();
  reg clr, start, clk;
  reg [31:0] a;
  reg [15:0] b;
  wire [31:0] q;
  wire [15:0] r;
  wire busy, ready;
  wire [4:0] count;
  main divider(a, b, q, r, start, clk, clr, busy, ready, count);
  initial begin
    clr <= 0;
    start <= 0;
    // As described in the lab instructions
    a <= 32'h4c7f228a;
    b <= 16'h6a0e;
    clk <= 1;
    // Run simulation
    #5 clr <= 1;
    #0 start <= 1;
    #10 start <= 0;
  end
  always begin
    // Negate the clock
    #5 clk = ~clk;
  end
endmodule


    wire PROGB_GLBL;
    wire CCLKO_GLBL;
    wire FCSBO_GLBL;
    wire [3:0] DO_GLBL;
    wire [3:0] DI_GLBL;
   
    reg GSR_int;
    reg GTS_int;
    reg PRLD_int;

module WriteBack_Mux(
  input wm2reg,
  input [31:0] wr,
  input [31:0] wdo,
  output reg [31:0] wb_out
);
	always@(*) begin
    if (wm2reg == 0) begin
      wb_out <= wr;
    end else begin
      wb_out <= wdo;
    end
  end
endmodule

  PC pc_dp(clk, add_rs, pc_r);
  PC_Adder adder_dp(pc_r, add_rs);
  InstMem im_dp(pc_r, inst);
  IF_ID ifid_dp(clk, inst, dinst);
  Control_Unit cu_dp(dinst, wreg, m2reg, wmem, aluc_dp, aluimm, regrt);
  Regrt_Multiplexer mult_dp(dinst, regrt, dest_reg);
  Register_File rf_dp(dinst, qa_dp, qb_dp);
  Immediate_Extender ie_dp(dinst, imm32);
  ID_EXE idexe_dp(clk, wreg, m2reg, wmem, aluc_dp, aluimm, dest_reg, qa_dp, qb_dp, imm32, ewreg, em2reg, ewmem, ealuc, ealuimm, edest_reg, eqa, eqb, eimm32);

  always @(posedge clk or negedge clr) begin
    if (!clr) begin
      busy <= 0;
      ready <= 0;
    end else begin
      if (start) begin
        // Initialize in parallel
        reg_q <= a;
        reg_b <= b;
        reg_r <= 0;
        busy <= 1;
        ready <= 0;
        count <= 0;
      end else if (busy) begin
         reg_q <= {reg_q[30:0], ~sub_out[16]};
        reg_r <= mux_out;
        count <= count + 5'b1;
        // Computation completed.
        if (count + 1 == 5'b0) begin
          busy <= 0;
          ready <= 1;
        end
      end
    end
  end
endmodule


module ALU(input [31:0] eqb, input [31:0] eimm32, input ealuimm, output reg [31:0] alu_out);
  always @(*) begin
    if (ealuimm) begin
      alu_out = eimm32;
    end else begin
      alu_out = eqb;
    end
  end
endmodule 

`timescale 1ns / 1ps
// Create Date: 2022/03/20 21:22:36
module tb();
  reg clk;
  wire [31:0] pc_r;
  wire ewreg;
  wire em2reg;
  wire ewmem;
  wire ealuimm;
  wire [3:0] ealuc;
  wire [4:0] edest_reg;
  wire [31:0] eimm32, eqa, eqb;
  initial begin
    clk = 1;
  end
  DataPath dp(clk, pc_r, ewreg, em2reg, ewmem, ealuimm, ealuc, edest_reg, eqa, eqb, eimm32);
  always begin
    #5 clk = ~clk;
  end
endmodule


  initial begin
    for (i = 0; i < 32; i = i + 1) begin
      registers[i] <= 32'b0;
    end
  end

//--------   JTAG Globals --------------
    wire JTAG_TDO_GLBL;
    wire JTAG_TCK_GLBL;
    wire JTAG_TDI_GLBL;
    wire JTAG_TMS_GLBL;
    wire JTAG_TRST_GLBL;

module Regrt_Multiplexer(
  input [31:0] dinst_out,
  input regrt,
  output reg [4:0] dest_reg
);
  always @ (*) begin
    if (regrt == 0) begin
      // rd
      dest_reg <= dinst_out[15:11];
    end else begin
      // rt
      dest_reg <= dinst_out[20:16];
    end
  end
endmodule

`timescale 1ns / 1ps
// Create Date: 2022/03/20 21:22:36
module tb();
  reg clk;
  wire [31:0] pc_r;
  wire ewreg;
  wire em2reg;
  wire ewmem;
  wire ealuimm;
  wire [3:0] ealuc;
  wire [4:0] edest_reg;
  wire [31:0] eimm32, eqa, eqb;

  always @ (dinst_out) begin
    qa <= registers[dinst_out[25:21]];
    qb <= registers[dinst_out[20:16]];
  end
endmodule

module IF_ID(input clk, input [31:0] inst_out, output reg [31:0] dinst_out);
  always@(posedge clk)
  begin
    dinst_out <= inst_out;
  end
endmodule

    initial begin
	GSR_int = 1'b1;
	PRLD_int = 1'b1;
	#(ROC_WIDTH)
	GSR_int = 1'b0;
	PRLD_int = 1'b0;
    end

endmodule
`endif


  wire [31:0] alu_out;
  wire [31:0] alul_out;
  ALU alu_mux(eqb, eimm32, ealuimm, alu_out);
  ALU_Logic alu(eqa, alu_out, ealuc, alul_out);
  ExememPipe pipe(clk, ewreg, em2reg, ewmem, edestreg, alul_out, eqb, mwreg, mm2reg, mwmem, mdestreg, mr, mqb);
  MEMWB mb(clk, mwreg, mm2reg, mdestreg, mr, mdo, wwreg, wm2reg, wdestreg, wr, wdo);
endmodule


    reg JTAG_USER_TDO1_GLBL = 1'bz;
    reg JTAG_USER_TDO2_GLBL = 1'bz;
    reg JTAG_USER_TDO3_GLBL = 1'bz;
    reg JTAG_USER_TDO4_GLBL = 1'bz;

  initial begin
    clk = 1;
  end
  DataPath dp(clk, pc_r,
    ewreg, em2reg, ewmem, ealuimm, ealuc, edest_reg, eqa, eqb, eimm32,
    mwreg, mm2reg, mwmem, mr, mqb, mdestreg, wwreg, wm2reg, wdestreg, wr, wdo
  );
  always begin
    #5 clk = ~clk;
  end
endmodule


  // Subtract r and q with 0 and b
  wire [16:0] sub_out = {reg_r, reg_q[31]} - {1'b0, reg_b};
  // Controlled
  wire [15:0] mux_out = sub_out[16] ? {reg_r[14:0], reg_q[31]} : sub_out[15:0];
  assign q = reg_q;
  assign r = reg_r;

`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 2022/02/06 20:16:41
// Design Name: 
// Module Name: main
// Project Name: Cmpen 331 Lab 1
// Target Devices: As described on PDF
// Description: division
// 
//////////////////////////////////////////////////////////////////////////////////

module DataMem(input [31:0] mr, input [31:0] mqb, input mwmem, input clk, output reg [31:0] mdo);
  reg [31:0] data [0:63];
  initial begin
      data[0] = 32'hA00000AA;
      data[4] = 32'h10000011;
      data[8] = 32'h20000022;
      data[12] = 32'h30000033;
      data[16] = 32'h40000044;
      data[20] = 32'h50000055;
      data[24] = 32'h60000066;
      data[28] = 32'h70000077;
      data[32] = 32'h80000088;
      data[36] = 32'h90000099;
  end
  always @(*) begin
    mdo = data[mr];
  end
  always @(negedge clk)begin
    if (mwmem == 1) begin
      data[mr] = mqb;
    end
  end
endmodule 

  initial begin
    clk = 1;
  end
  DataPath dp(clk,
    // pc_r,
    // ewreg, em2reg, ewmem, ealuimm, ealuc, edest_reg, eqa, eqb, eimm32,
    // mwreg, mm2reg, mwmem, mr, mqb, mdestreg, wwreg, wm2reg, wdestreg,
     wwreg, wm2reg,
 wdestreg,
 wr, wdo
 wbdataout, r_s, r_t, qa, qb,r
  );
  always begin
    #5 clk = ~clk;
  end
endmodule


// "Instruction memory"
module InstMem(input [31:0] pc, output reg [31:0] inst_out);
  reg [31:0] memory [0:63];
  initial begin
    memory[25] <= 32'b10001100001000100000000000000000;
    memory[26] <= 32'b10001100001000110000000000000100;    
    memory[27] <= 32'b10001100001001000000000000001000;    
    memory[28] <= 32'b10001100001001010000000000001100;    
  end  
  always @ (pc)
  begin
    inst_out <= memory[pc[31:2]];
  end
endmodule

  // Implementation details
  input start, clk, clr;
  output reg busy, ready;
  output [4:0] count;

// $Header: /devl/xcs/repo/env/Databases/CAEInterfaces/verunilibs/data/glbl.v,v 1.14 2010/10/28 20:44:00 fphillip Exp $
`ifndef GLBL
`define GLBL
`timescale  1 ps / 1 ps

`timescale 1ns / 1ps
// Create Date: 2022/03/20 14:43:52
// Design Name: 

module main(a, b, q, r, start, clk, clr, busy, ready, count);
  // "Intended to be seen by other modules" I/O
  input [31:0] a;
  input [15:0] b;
  output [31:0] q;
  output [15:0] r;

module Control_Unit(
  // Decomposed into op and func
  input [31:0] dinst_out,
  output reg wreg,
  output reg m2reg,
  output reg wmem,
  output reg [3:0] aluc,
  output reg aluimm,
  output reg regrt
);
  reg [5:0] op;
  reg [5:0] func;
  always @ (dinst_out) begin
    op <= dinst_out[31:26];
    func <= dinst_out[5:0];
    case(op)
      // r-type
      6'b000000: begin
        // TODO
      end
      // lw
      6'b100011: begin
        wreg = 1'b1;
        m2reg = 1'b1;
        wmem = 1'b0;
        aluc = 4'b0010;
        aluimm = 1'b1;
        regrt = 1'b1;
      end
    endcase
  end
endmodule