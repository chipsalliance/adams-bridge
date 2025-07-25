/* 
ChipWhisperer Bergen Target - Simple testbench to check for signs of life.

Copyright (c) 2021, NewAE Technology Inc.
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted without restriction. Note that modules within
the project may have additional restrictions, please carefully inspect
additional licenses.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

The views and conclusions contained in the software and documentation are those
of the authors and should not be interpreted as representing official policies,
either expressed or implied, of NewAE Technology Inc.
*/

`timescale 1ns / 1ns
`default_nettype none 


module CW310_top_tb();
    parameter pADDR_WIDTH = 20;
    parameter pBYTECNT_SIZE = 8;
    parameter pUSB_CLOCK_PERIOD = 10;
    parameter pPLL_CLOCK_PERIOD = 10;
    parameter pSEED = 1;
    parameter pTIMEOUT = 30000;
    parameter pVERBOSE = 0;
    parameter pDUMP = 0;

localparam BASE_ADDR        = 32'h00000000;

  localparam ADDR_NAME0       = BASE_ADDR + 32'h00000000;
  localparam ADDR_NAME1       = BASE_ADDR + 32'h00000004;
  localparam ADDR_VERSION0    = BASE_ADDR + 32'h00000008;
  localparam ADDR_VERSION1    = BASE_ADDR + 32'h0000000C;

  localparam ADDR_CTRL        = BASE_ADDR + 32'h00000010; 
  
  localparam ADDR_STATUS          = BASE_ADDR + 32'h00000014;
  localparam STATUS_READY_BIT = 0;
  localparam STATUS_VALID_BIT = 1;

  localparam ADDR_SEED_START      = BASE_ADDR + 32'h00000058;
  localparam ADDR_SIGN_RND_START  = BASE_ADDR + 32'h00000078;
  // localparam ADDR_SEED_END        = BASE_ADDR + 32'h000000AC;

  localparam ADDR_MSG_START           = BASE_ADDR + 32'h00000098;
  localparam ADDR_PRIVKEY_OUT_START   = BASE_ADDR + 32'h00004000;
  localparam ADDR_PRIVKEY_IN_START    = BASE_ADDR + 32'h00006000;
  localparam ADDR_PUBKEY_START        = BASE_ADDR + 32'h00001000;

  localparam ADDR_SIGN_START     = BASE_ADDR + 32'h00002000;
  localparam ADDR_VERIFY_R_START  = BASE_ADDR + 32'h000000d8;
  localparam ADDR_IV_START        = BASE_ADDR + 32'h00000018;


    localparam REG_CRYPT_WR                   = 6;
  localparam REG_CRYPT_RD                   = 7;
  localparam REG_CRYPT_ADDR                 = 8;
  localparam REG_CRYPT_CTRL                 = 9;
  

   localparam NTT_SRC_BASE_ADDR = 14'h0;
   localparam NTT_INTERIM_BASE_ADDR = 14'h40;
   localparam NTT_DST_BASE_ADDR = 14'h80;
   localparam NTT_STATUS_REG = 12'hFFF;
   localparam NTT_ENABLE_REG = 12'hFFE;
   localparam NTT_CTRL_REG = 12'hFFD;
   localparam NTT_BASE_ADDR_REG = 12'hFFC;
   localparam NTT_SAMPLER_INPUT_0_REG = 12'hFFB;
   localparam NTT_SAMPLER_INPUT_1_REG = 12'hFFA;
   localparam NTT_SAMPLER_INPUT_2_REG = 12'hFF9;
   localparam NTT_SAMPLER_INPUT_3_REG = 12'hFF8;
   localparam NTT_LFSR_EN_REG = 12'hFF7;
   localparam NTT_LFSR_SEED0_0_REG = 12'hFF6;
   localparam NTT_LFSR_SEED0_1_REG = 12'hFF5;
   localparam NTT_LFSR_SEED1_0_REG = 12'hFF4;
   localparam NTT_LFSR_SEED1_1_REG = 12'hFF3;

   localparam MLDSA_Q = 23'd8380417;


    reg usb_clk;
    reg usb_clk_enable;
    wire [7:0] usb_data;
    reg [7:0] usb_wdata;
    reg [pADDR_WIDTH-1:0] usb_addr;
    reg usb_rdn;
    reg usb_wrn;
    reg usb_cen;
    reg usb_trigger;

    reg j16_sel;
    reg k16_sel;
    reg pushbutton;
    reg pll_clk1;
    wire tio_clkin;
    wire trig_out;

    wire led0;
    wire led1;
    wire led2;

    wire tio_trigger;
    wire tio_clkout;


    int seed;
    int errors;
    int warnings;
    int i;
    
    reg [31:0] write_data;

    wire clk = pll_clk1;  // shorthand for testbench

   int cycle;
   int total_time;

  reg [31 : 0]  cycle_ctr;
  reg [31 : 0]  error_ctr;
  reg [31 : 0]  tc_ctr;

  reg [7 : 0]  tc_number;
  reg [31 : 0]  read_data;

  int                   test_vector_cnt;

   // pragma uvmf custom class_item_additional begin
  bit [31:0] data;
  bit [31:0] SEED []; //32 Bytes
  bit [31:0] SIGN_RND [0:7]; //64 Bytes
  bit [31:0] SK []; //4896 Bytes
  bit [31:0] PK []; //2592 Bytes
  bit [31:0] actual_PK [648]; //2592 Bytes
  bit [31:0] MSG []; //64 Bytes
  bit [31:0] SIG []; //4628 Bytes
  bit [31:0] actual_SIG [1157]; //4628 Bytes
  // pragma uvmf custom class_item_additional end

  initial begin
    // pragma uvmf custom new begin
    // Construct arrays
    SEED = new[8];
    MSG = new[16];
    SK = new[1224];
    PK = new[648];
    SIG = new[1157];
    // actual_PK = new[648];
    // actual_SIG = new[1157];
    foreach (SIGN_RND[i]) begin
      SIGN_RND[i] = 32'h0;
    end
    // pragma uvmf custom new end
  end


   initial begin
      errors = 0;
      warnings = 0;
      usb_clk = 1'b1;
      usb_clk_enable = 1'b1;
      pll_clk1 = 1'b1;

      usb_wdata = 0;
      usb_addr = 0;
      usb_rdn = 1;
      usb_wrn = 1;
      usb_cen = 1;
      usb_trigger = 0;

      j16_sel = 1;
      k16_sel = 0;
      pushbutton = 1;
      pll_clk1 = 0;

      #(pUSB_CLOCK_PERIOD*2) pushbutton = 0;
      #(pUSB_CLOCK_PERIOD*2) pushbutton = 1;
      #(pUSB_CLOCK_PERIOD*10);

      // mldsa_keygen_and_signing_test(); 
      // zeroize_dut();
      init_mem_with_coeffs();
      $display("-----------------------------");
      pgm_base_addr(NTT_INTERIM_BASE_ADDR, NTT_SRC_BASE_ADDR, NTT_INTERIM_BASE_ADDR, NTT_DST_BASE_ADDR); //pwm_src_b, src, interim, dest
      $display("-----------------------------");
      start_lfsr();
      $display("-----------------------------");
      // zeroize_dut();
      // ct_test(1,0); //shuf, mode
      // $display("-----------------------------");
      // pgm_base_addr(NTT_DST_BASE_ADDR, NTT_INTERIM_BASE_ADDR, NTT_DST_BASE_ADDR);
      // $display("-----------------------------");
      // gs_test(1,0,1,1); //shuf, mask, check, mode
      // $display("-----------------------------");
      pwm_test(0,0,0,1,2); //shuf, mask, acc, check, mode
      $display("-----------------------------");
      pwm_test(0,0,1,1,2);
      // $display("-----------------------------");
      // pwm_test(1,0,0,1,2);
      // $display("-----------------------------");
      // pwm_test(1,0,1,1,2);
      // $display("-----------------------------");
      // pwm_sampler_test(0,0,1,2); //mask, acc, check, mode
      // $display("-----------------------------");
      // pwm_sampler_test(0,1,1,2);
      // $display("-----------------------------");
      // pwm_test(0,1,0,1,2);
      // $display("-----------------------------");
      // pwm_test(0,1,1,0,2);
      // $display("-----------------------------");
      // pwm_test(1,1,0,1,2);
      // $display("-----------------------------");
      // pwm_test(1,1,1,1,2);
      // $display("-----------------------------");
      // pwm_sampler_test(1,0,1,2);
      // $display("-----------------------------");
      // pwm_sampler_test(1,1,0,2);
      // gs_test(1,1,1,1);
      $finish;

   end

   // maintain a cycle counter
   always @(posedge clk) begin
      if (pushbutton == 0)
         cycle <= 0;
      else
         cycle <= cycle + 1;
   end




   reg read_select;

   assign usb_data = read_select? 8'bz : usb_wdata;
   assign tio_clkin = pll_clk1;

   always @(*) begin
      if (usb_wrn == 1'b0)
         read_select = 1'b0;
      else if (usb_rdn == 1'b0)
         read_select = 1'b1;
   end

   `include "tb_cw305_reg_tasks.sv"
   // `include "tb_tasks.sv"

   always #(pUSB_CLOCK_PERIOD/2) usb_clk = !usb_clk;
   always #(pPLL_CLOCK_PERIOD/2) pll_clk1 = !pll_clk1;

   wire #1 usb_rdn_out = usb_rdn;
   wire #1 usb_wrn_out = usb_wrn;
   wire #1 usb_cen_out = usb_cen;
   wire #1 usb_trigger_out = usb_trigger;

   wire trigger; // TODO: use it?

   cw310_mldsa_top #(
      .pBYTECNT_SIZE            (pBYTECNT_SIZE),
      .pADDR_WIDTH              (pADDR_WIDTH),
      .AHB_ADDR_WIDTH           (12),
      .AHB_DATA_WIDTH           (64)
   ) U_dut (
      .usb_clk                  (usb_clk & usb_clk_enable),
      .usb_data                 (usb_data),
      .usb_addr                 (usb_addr),
      .usb_rdn                  (usb_rdn_out),
      .usb_wrn                  (usb_wrn_out),
      .usb_cen                  (usb_cen_out),
      .usb_trigger              (usb_trigger_out),
      .j16_sel                  (j16_sel),
      .k16_sel                  (k16_sel),
      .pushbutton               (pushbutton),
      .led1                     (led0),
      .led2                     (led1),
      .led3                     (led2),
      .pll_clk1                 (pll_clk1),
      .tio_trigger              (trigger),
      .tio_clkin                (tio_clkin),
      .tio_clkout               ()
   );




endmodule

`default_nettype wire