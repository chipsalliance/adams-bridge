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
//======================================================================
//
// adamsbridge_top_tb.sv
// --------
//
//======================================================================

import "DPI-C" function string getenv(input string env_name);

`include "config_defines.svh"

module adamsbridge_top_tb
  import abr_params_pkg::*;
  import abr_prim_alert_pkg::*;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  `ifndef VERILATOR
  int MAX_CYCLES;
  int VEC_CNT;
  int TEST_CMD;

  initial begin
    // To use this from the command line, add "+MAX_CYCLES=<value>"
    // to override the sim timeout
    if ($value$plusargs("MAX_CYCLES=%d", MAX_CYCLES)) begin
      $info("Received argument +MAX_CYCLES, with value %d", MAX_CYCLES);
    end else begin
      MAX_CYCLES = 20_0000;
      $info("No argument provided for MAX_CYCLES, defaulting to %d", MAX_CYCLES);
    end
    if ($value$plusargs("VEC_CNT=%d", VEC_CNT)) begin
      $info("Received argument +VEC_CNT, with value %d", VEC_CNT);
    end else begin
      VEC_CNT = 10;
      $info("No argument provided for VEC_CNT, defaulting to %d", VEC_CNT);
    end
    if ($value$plusargs("TEST_CMD=%d", TEST_CMD)) begin
      $info("Received argument +TEST_CMD, with value %d", TEST_CMD);
    end else begin
      TEST_CMD = 'd1;
      $info("No argument provided for TEST_CMD, defaulting to %d", TEST_CMD);
    end
  end
  `else
  parameter MAX_CYCLES = 20_0000;
  `endif

  parameter AHB_ADDR_WIDTH = 32;
  parameter AHB_DATA_WIDTH = 32;

  parameter DEBUG = 0;

  parameter CLK_HALF_PERIOD = 5;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0] cycle_ctr;
  reg [31 : 0] error_ctr;
  reg [31 : 0] tc_ctr;

`ifndef VERILATOR
  reg clk_tb;
`endif
  reg clk_i;
  reg reset_n_tb;
  reg rst_b;
  reg [31 : 0] read_data;

  reg [AHB_ADDR_WIDTH-1:0]  haddr_i_tb;
  reg [AHB_DATA_WIDTH-1:0]  hwdata_i_tb;
  reg           hsel_i_tb;
  reg           hwrite_i_tb; 
  reg           hready_i_tb;
  reg [1:0]     htrans_i_tb;
  reg [2:0]     hsize_i_tb;

  wire          hresp_o_tb;
  wire          hreadyout_o_tb;
  wire [AHB_DATA_WIDTH-1:0] hrdata_o_tb;

  assign clk_i = clk_tb;
  assign rst_b = reset_n_tb;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  
  assign hready_i_tb = hreadyout_o_tb;

  adamsbridge_top 
  dut (
  .clk(clk_i),
  .rst_b(rst_b),
  .haddr_i(haddr_i_tb),
  .hready_i(hready_i_tb),
  .hsel_i(hsel_i_tb),
  .hsize_i(hsize_i_tb),
  .htrans_i(htrans_i_tb),
  .hwdata_i(hwdata_i_tb),
  .hwrite_i(hwrite_i_tb),

  .hresp_o(hresp_o_tb),
  .hrdata_o(hrdata_o_tb),
  .hreadyout_o(hreadyout_o_tb)
  );

  //----------------------------------------------------------------
  // clk_gen
  //
  // Clock generator process.
  //----------------------------------------------------------------
`ifndef VERILATOR
  always
    begin : clk_gen
      #CLK_HALF_PERIOD
      clk_tb = !clk_tb;
    end // clk_gen
`endif

  //----------------------------------------------------------------
  // sys_monitor
  //
  // Generates a cycle counter and displays information about
  // the dut as needed.
  //----------------------------------------------------------------
  always @(posedge clk_tb) begin : sys_monitor
      cycle_ctr = (!reset_n_tb) ? 32'h0 : cycle_ctr + 1;

      // Test timeout monitor
      if(cycle_ctr == MAX_CYCLES) begin
        $error("Hit max cycle count (%0d) .. stopping",cycle_ctr);
        $finish;
      end
    end

  //----------------------------------------------------------------
  // reset_dut()
  //
  // Toggles reset to force the DUT into a well defined state.
  //----------------------------------------------------------------
  task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;

      repeat (2) @(posedge clk_tb);
      reset_n_tb = 1;

      repeat (2) @(posedge clk_tb);

      $display("");
    end
  endtask // reset_dut

  //----------------------------------------------------------------
  // init_sim()
  //
  // Initialize all counters and testbed functionality as well
  // as setting the DUT inputs to defined values.
  //----------------------------------------------------------------
  task init_sim;
    begin
      error_ctr     = '0;
      tc_ctr        = '0;
`ifndef VERILATOR
      clk_tb        = 0;
`endif
      reset_n_tb    = 0;

      haddr_i_tb      = 'Z;
      hwdata_i_tb     = 'Z;
      hsel_i_tb       = 0;
      hwrite_i_tb     = 0;
      htrans_i_tb     = 0;
      hsize_i_tb      = 3'b011;

    end
  endtask // init_dut

  //----------------------------------------------------------------
  // display_test_result()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  task display_test_result;
    begin
      if (error_ctr == 0)
        begin
          $display("*** All %02d test cases completed successfully.", tc_ctr);
          $display("* TESTCASE PASSED");
        end
      else
        begin
          $display("*** %02d test cases completed.", tc_ctr);
          $display("*** %02d errors detected during testing.", error_ctr);
          $display("* TESTCASE FAILED");
        end
    end
  endtask // display_test_result

  //----------------------------------------------------------------
  // write_single_msg()
  //
  // Write the given msg to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_word_ahb(input [31 : 0]  address, input [31 : 0] word);
    begin
    hsel_i_tb       <= 1;
    haddr_i_tb      <= address;
    hwrite_i_tb     <= 1;
    htrans_i_tb     <= 2;
    hsize_i_tb      <= 3'b010;

    @(posedge clk_tb);
    haddr_i_tb      <= 'Z;
    hwdata_i_tb     <= address[2] ? {word, 32'h0}: {32'h0, word}; 
    hwrite_i_tb     <= 0;
    htrans_i_tb     <= 0;
    wait(hreadyout_o_tb == 1'b1);

    @(posedge clk_tb);
    hsel_i_tb       <= 0;

    end
  endtask // write_single_word_ahb

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------

  initial
    begin : main
      $write("PLAYBOOK_RANDOM_SEED = %s\n", getenv("PLAYBOOK_RANDOM_SEED"));
      $display("   -- Testbench for ADAMSBRIDGE started --");

      init_sim();
      reset_dut();

      write_single_word_ahb('h10, TEST_CMD);

      $display("   -- Testbench for ADAMSBRIDGE done. --");

      wait(0)

      $finish;
    end // main

    abr_prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o;

    `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3FsmCheck_A,
      dut.sampler_top_inst.sha3_inst.u_state_regs, alert_tx_o[1])
  
    `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KeccakRoundFsmCheck_A,
      dut.sampler_top_inst.sha3_inst.u_keccak.u_state_regs, alert_tx_o[1])
  
    `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3padFsmCheck_A,
      dut.sampler_top_inst.sha3_inst.u_pad.u_state_regs, alert_tx_o[1])
  
    `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WrMsgCountCheck_A,
      dut.sampler_top_inst.sha3_inst.u_pad.u_wrmsg_count, alert_tx_o[1])
  
    `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RoundCountCheck_A,
      dut.sampler_top_inst.sha3_inst.u_keccak.u_round_count, alert_tx_o[1])

endmodule // adamsbridge_tb

//======================================================================
// EOF adamsbridge_tb.sv
//======================================================================
