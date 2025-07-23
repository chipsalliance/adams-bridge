// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

`default_nettype none
`timescale 1ns / 1ps
module CW305_top_tb 
#(
    parameter   TEST_VECTOR_NUM = 10,
    parameter pBYTECNT_SIZE     = 7,
    parameter pADDR_WIDTH       = 20
)
();

  string      ecc_test_vector_file; // Input test vector file
  string      ecc_test_to_run;      // ECC tests - default, ECC_normal_test, ECC_otf_reset_test

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
  
  
  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  localparam DEBUG           = 0;

  localparam USB_CLK_HALF_PERIOD = 1;
  localparam USB_CLK_PERIOD = 2 * USB_CLK_HALF_PERIOD;
  localparam CLK_HALF_PERIOD = 1;
  localparam CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

  localparam REG_SIZE      = 384;
  localparam PRIME         = 384'hfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff;
  localparam ADD_NUM_ADDS  = 1;
  localparam ADD_BASE_SZ   = 384;

  localparam AHB_HTRANS_IDLE     = 0;
  localparam AHB_HTRANS_BUSY     = 1;
  localparam AHB_HTRANS_NONSEQ   = 2;
  localparam AHB_HTRANS_SEQ      = 3;

  localparam AHB_ADDR_WIDTH       = 32;
  localparam AHB_DATA_WIDTH       = 32;

  localparam REG_CRYPT_WR                   = 6;
  localparam REG_CRYPT_RD                   = 7;
  localparam REG_CRYPT_ADDR                 = 8;
  localparam REG_CRYPT_CTRL                 = 9;
    
  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0]  cycle_ctr;
  reg [31 : 0]  error_ctr;
  reg [31 : 0]  tc_ctr;

  reg           clk_tb;
  reg           reset_n_tb;
  
  reg                           usb_clk;
  logic [pADDR_WIDTH-1 : 0]     reg_address;

    wire  [AHB_ADDR_WIDTH-1:0]  haddr_i;
    wire  [AHB_DATA_WIDTH-1:0]  hwdata_i;
    wire                        hsel_i;
    wire                        hwrite_i;
    wire                        hready_i;
    wire  [1:0]                 htrans_i;
    wire  [2:0]                 hsize_i;
    wire                        hresp_o;
    wire                        hreadyout_o;
    wire [AHB_DATA_WIDTH-1:0]   hrdata_o;


  reg [7 : 0]  tc_number;
  reg [31 : 0]  read_data;

  int                   test_vector_cnt;


  logic [7 : 0] usb_read_data;
  logic [7 : 0] usb_write_data;
  logic usb_reg_read;
  logic usb_reg_write;
  logic usb_reg_addrvalid;

  //================== TRIGGERS =======================
  
  wire NTT_trigger;
  wire PWM_trigger;
  wire PWA_trigger;
  wire INTT_trigger;
  wire error_intr;
  wire notif_intr;


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
  
    ahb_interface    #(
       .pBYTECNT_SIZE           (pBYTECNT_SIZE),
       .pADDR_WIDTH             (pADDR_WIDTH),
       .AHB_ADDR_WIDTH          (AHB_ADDR_WIDTH),
       .AHB_DATA_WIDTH          (AHB_DATA_WIDTH)
    )
    ahb_interface
    (
       .usb_clk                 (usb_clk), 
       .crypto_clk              (clk_tb),
       .reset_i                 (!reset_n_tb),
       .reg_address             (reg_address[pADDR_WIDTH-1:pBYTECNT_SIZE]), 
       .reg_bytecnt             (reg_address[pBYTECNT_SIZE-1:0]), 
       .read_data               (usb_read_data), 
       .write_data              (usb_write_data),
       .reg_read                (usb_reg_read), 
       .reg_write               (usb_reg_write), 
       .reg_addrvalid           (usb_reg_addrvalid),

       .exttrigger_in           (1'b0),
       
       .O_clksettings           (),
       .O_user_led              (),
       
        //AHB Lite Interface
        .haddr                  (haddr_i),
        .hwdata                 (hwdata_i),
        .hsel                   (hsel_i),
        .hwrite                 (hwrite_i),
        .hready                 (hready_i),
        .htrans                 (htrans_i),
        .hsize                  (hsize_i),
        .hresp                  (hresp_o),
        .hreadyout              (hreadyout_o),
        .hrdata                 (hrdata_o)
    );
    
  
    mldsa_top #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32)
            )
            dut (
             .clk(clk_tb),
             .rst_b(reset_n_tb),

             
  .NTT_trigger(NTT_trigger),
  .PWM_trigger(PWM_trigger),
  .PWA_trigger(PWA_trigger),
  .INTT_trigger(INTT_trigger),

             .haddr_i(haddr_i),
             .hwdata_i(hwdata_i),
             .hsel_i(hsel_i),
             .hwrite_i(hwrite_i),
             .hready_i(hready_i),
             .htrans_i(htrans_i),
             .hsize_i(hsize_i),

             .hresp_o(hresp_o),
             .hreadyout_o(hreadyout_o),
             
             .error_intr(error_intr),
             .notif_intr(notif_intr),

             .hrdata_o(hrdata_o)
            );


  //----------------------------------------------------------------
  // clk_gen
  //
  // Always running clock generator process.
  //----------------------------------------------------------------
  always
    begin : clk_gen
      #CLK_HALF_PERIOD;
      clk_tb = !clk_tb;
    end // clk_gen

  always
    begin : usb_clk_gen
      #USB_CLK_HALF_PERIOD;
      usb_clk = !usb_clk;
    end // clk_gen

  //----------------------------------------------------------------
  // sys_monitor()
  //
  // An always running process that creates a cycle counter and
  // conditionally displays information about the DUT.
  //----------------------------------------------------------------
  always
    begin : sys_monitor
      #(CLK_PERIOD);
      cycle_ctr = cycle_ctr + 1;
    end


  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      cycle_ctr = 32'h00000000;
      error_ctr = 32'h00000000;
      tc_ctr    = 32'h00000000;
      tc_number = 'h0;

      clk_tb        = 0;
      reset_n_tb    = 0;
        
      usb_clk = 0;
      reg_address = 0;
      usb_write_data = 0;
      usb_reg_read = 0;
      usb_reg_write = 0;
      usb_reg_addrvalid = 0;
    end
  endtask // init_dut


  `include "tb_tasks.sv"

  //----------------------------------------------------------------
  // main
  //
  // The main test functionality.
  //----------------------------------------------------------------
  initial
    begin : main
      
      string fname;

      $display("   -= Testbench for MLDSA started =-");
      $display("    ==============================");
      $display("");


      init_sim();
      reset_dut();

      mldsa_keygen_and_signing_test(); 

      display_test_results();
      
      $display("");
      $display("*** MLDSA simulation done. ***");
      $finish;
    end // main


endmodule // CW305_top_tb