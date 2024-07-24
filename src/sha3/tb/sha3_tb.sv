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
// sha3_tb.sv
// --------
//
//======================================================================

import "DPI-C" function string getenv(input string env_name);

module sha3_tb
  import sha3_pkg::*;
  import sha3_tb_pkg::*;
  import abr_prim_alert_pkg::*;
  import sampler_pkg::*;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  //-----------------------
  // SHA3parameters
  //-----------------------
  // Keccak Rounds per clock
  localparam int RoundsPerClock = 2;
  // Do not enable masking
  localparam bit Sha3EnMasking = 0;
  // derived parameter
  localparam int Sha3Share = (Sha3EnMasking) ? 2 : 1;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  `ifndef VERILATOR
  int MAX_CYCLES;
  int VEC_CNT;
  string sha3_testname; 

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
  end
  `else
  parameter MAX_CYCLES = 20_0000;
  `endif

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
  reg [31 : 0]  read_data;

  logic                    msg_start;
  logic                    msg_valid;
  logic [MsgStrbW-1:0]     msg_strobe;
  logic [MsgWidth-1:0]     msg_data[Sha3Share];
  logic                    sha3_msg_rdy;
  logic                    sha3_start;
  logic                    sha3_process;
  logic                    sha3_run;

  abr_prim_mubi_pkg::mubi4_t    sha3_done;
  abr_prim_mubi_pkg::mubi4_t    sha3_absorbed;

  logic sha3_squeezing;

  logic sha3_block_processed;

  sha3_pkg::sha3_st_e sha3_fsm;
  sha3_pkg::err_t sha3_err;

  sha3_pkg::sha3_mode_e mode;
  sha3_pkg::keccak_strength_e strength;

  logic sha3_state_vld;
  logic [sha3_pkg::StateW-1:0] sha3_state[Sha3Share];

  logic sha3_state_error;
  logic sha3_count_error;
  logic sha3_rst_storage_err;

  assign clk_i = clk_tb;
  assign rst_b = reset_n_tb;


  string vector_filename,exp_res_filename;
  assign exp_res_filename = "exp_results.txt";
  assign vector_filename = "input_vectors.txt";

  keccak_test_vector_t test_vector_q[$]; 
  exp_results_u exp_result;
  string exp_strength, exp_mode;
  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------

  // SHA3 hashing engine
  sha3 #(
    .RoundsPerClock(RoundsPerClock),
    .EnMasking (Sha3EnMasking)
  ) dut (
    .clk_i (clk_tb),
    .rst_b (reset_n_tb),

    // MSG_FIFO interface
    .msg_start_i (msg_start),
    .msg_valid_i (msg_valid),
    .msg_data_i  (msg_data),
    .msg_strb_i  (msg_strobe),
    .msg_ready_o (sha3_msg_rdy),

    // Entropy interface - not using
    .rand_valid_i    (1'b0),
    .rand_early_i    (1'b0),
    .rand_data_i     ('0),
    .rand_aux_i      ('0),
    .rand_consumed_o (),

    // N, S: Used in cSHAKE mode
    .ns_data_i       ('0), // ns_prefix),

    // Configurations
    .mode_i     (mode), 
    .strength_i (strength), 

    // Controls (CMD register)
    .start_i    (sha3_start       ),
    .process_i  (sha3_process     ),
    .run_i      (sha3_run         ), // For squeeze
    .done_i     (sha3_done        ),

    .absorbed_o (sha3_absorbed),
    .squeezing_o (sha3_squeezing),

    .block_processed_o (sha3_block_processed),

    .sha3_fsm_o (sha3_fsm),

    .state_valid_o (sha3_state_vld),
    .state_valid_hold_i('0),
    .state_o       (sha3_state),

    .error_o (sha3_err),
    .sparse_fsm_error_o (sha3_state_error),
    .count_error_o  (sha3_count_error),
    .keccak_storage_rst_error_o (sha3_rst_storage_err)
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
      error_ctr    = '0;
      tc_ctr       = '0;
`ifndef VERILATOR
      clk_tb       = 0;
`endif
      reset_n_tb   = 0;

      mode = sha3_pkg::Shake;
      strength = sha3_pkg::L256;

      msg_start = 0;
      msg_valid = 0;
      msg_strobe = '0;
      msg_data[0] = '0;

      sha3_start = 0;
      sha3_process = 0;
      sha3_done = abr_prim_mubi_pkg::MuBi4False;
      sha3_run = 0;
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
  task write_single_msg(input [MsgWidth-1:0] msg_i, input [MsgStrbW-1:0] msg_strobe_i);
    begin
      //$display("[%t] write_single_msg(msg=0x%x)", $time, msg_i);
      //$display("[%t] write_single_msg(msg_strobe=0x%x)", $time, msg_strobe_i);

      msg_valid       <= 1;
      msg_data[0]     <= msg_i;
      msg_strobe      <= msg_strobe_i;

      //don't like this, but solves the timing issue
      @(negedge clk_tb);
      //Wait until msg rdy gets asserted 
      wait (sha3_msg_rdy == 1);

      @(posedge clk_tb);
      msg_valid       <= 0;
      msg_data[0]     <= 'x;
      msg_strobe      <= 'x;

    end
  endtask // write_single_msg

  //----------------------------------------------------------------
  // gen_rand_test_vectors()
  //----------------------------------------------------------------
  task gen_rand_test_vectors;
    int fd_w;

    test test0;
    test0 = new();

    fd_w = $fopen(vector_filename, "a");
    if (fd_w == 0) $error("Cannot open file %s for writing", vector_filename);
    
    for (int i = 0; i < VEC_CNT; i++) begin
      assert(test0.randomize());

      test0.vector.input_valid = '1 >> (MAX_MSG_WR*(MsgWidth/8)-test0.vector_length);

      test_vector_q.push_back(test0.vector);

      //Write vectors to the file
      $fwrite(fd_w, "%s ", test0.vector.mode.name());
      $fwrite(fd_w, "%s ", test0.vector.strength.name());
      $fwrite(fd_w, "%h ", test0.vector.input_valid);
      $fwrite(fd_w, "%0h \n", test0.vector.input_vector);
    end
    $fclose(fd_w);

    $system($sformatf("python sha3.py"));

  endtask

  //----------------------------------------------------------------
  // gen_five_squeeze_test_vectors()
  //----------------------------------------------------------------
  task gen_five_squeeze_test_vectors;
    int fd_w;

    test test0;
    test0 = new();

    fd_w = $fopen(vector_filename, "a");
    if (fd_w == 0) $error("Cannot open file %s for writing", vector_filename);
    
    for (int i = 0; i < VEC_CNT; i++) begin
      assert(test0.randomize() with { vector.mode == sha3_pkg::Shake;
      });

      test0.vector.input_valid = '1 >> (MAX_MSG_WR*(MsgWidth/8)-test0.vector_length);

      test_vector_q.push_back(test0.vector);

      //Write vectors to the file
      $fwrite(fd_w, "%s ", test0.vector.mode.name());
      $fwrite(fd_w, "%s ", test0.vector.strength.name());
      $fwrite(fd_w, "%h ", test0.vector.input_valid);
      $fwrite(fd_w, "%0h \n", test0.vector.input_vector);
    end
    $fclose(fd_w);

    $system($sformatf("python sha3.py"));

  endtask


  //----------------------------------------------------------------
  // check_results()
  //----------------------------------------------------------------
  task check_results(input logic squeeze=0, input int squeeze_iter=0);

    //strength and mode fields determine how many valid bits we need to check from output
    if (exp_mode == "Shake") begin
      if (squeeze == 1'b1) begin
        if (exp_strength == "L256") begin
          if (exp_result.shake256.squeeze[squeeze_iter] != sha3_state[0][1088-1:0]) begin
            $display("[%t] Checking Squeeze Iter %d for %s %s", $time, squeeze_iter, exp_mode, exp_strength);
            $display("[%t] Actual:   %x", $time,sha3_state[0][1088-1:0]);
            $display("[%t] Expected: %x", $time,exp_result.shake256.squeeze[squeeze_iter]);
            error_ctr += 1;
          end
        end else if (exp_strength == "L128" ) begin
          if (exp_result.shake128.squeeze[squeeze_iter] != sha3_state[0][1344-1:0]) begin
            $display("[%t] Checking Squeeze Iter %d for %s %s", $time, squeeze_iter, exp_mode, exp_strength);
            $display("[%t] Checking %s %s", $time, exp_mode, exp_strength);
            $display("[%t] Actual:   %x", $time,sha3_state[0][1344-1:0]);
            $display("[%t] Expected: %x", $time,exp_result.shake128.squeeze[squeeze_iter]);
            error_ctr += 1;
          end
        end else begin
          $display("[%t] Invalid strength field %s not supported in Shake mode", $time, exp_strength);
          error_ctr += 1;
        end
      end else begin
        if (exp_strength == "L256") begin
          if (exp_result.shake256.absorb != sha3_state[0][1088-1:0]) begin
            $display("[%t] Checking Absorb for %s %s", $time, exp_mode, exp_strength);
            $display("[%t] Actual:   %x", $time,sha3_state[0][1088-1:0]);
            $display("[%t] Expected: %x", $time,exp_result.shake256.absorb);
            error_ctr += 1;
          end
        end else if (exp_strength == "L128" ) begin
          if (exp_result.shake128.absorb != sha3_state[0][1344-1:0]) begin
            $display("[%t] Checking Absorb for %s %s", $time, exp_mode, exp_strength);
            $display("[%t] Actual:   %x", $time,sha3_state[0][1344-1:0]);
            $display("[%t] Expected: %x", $time,exp_result.shake128.absorb);
            error_ctr += 1;
          end
        end else begin
          $display("[%t] Invalid strength field %s not supported in Shake mode", $time, exp_strength);
          error_ctr += 1;
        end
      end
    end else if (exp_mode == "Sha3") begin
      if (exp_strength == "L512") begin
        if (exp_result.sha3_512.digest != sha3_state[0][512-1:0]) begin
          $display("[%t] Checking %s %s", $time, exp_mode, exp_strength);
          $display("[%t] Actual:   %x", $time,sha3_state[0][512-1:0]);
          $display("[%t] Expected: %x", $time,exp_result.sha3_512.digest);
          error_ctr += 1;
        end
      end else if (exp_strength == "L256" ) begin
        if (exp_result.sha3_256.digest != sha3_state[0][256-1:0]) begin
          $display("[%t] Checking %s %s", $time, exp_mode, exp_strength);
          $display("[%t] Actual:   %x", $time,sha3_state[0][256-1:0]);
          $display("[%t] Expected: %x", $time,exp_result.sha3_256.digest);
          error_ctr += 1;
        end
      end else begin
        $display("[%t] Invalid strength field %s not supported in Sha3 mode", $time, exp_strength);
        error_ctr += 1;
      end
    end 

  endtask
  //----------------------------------------------------------------
  // run_rand_test()
  //----------------------------------------------------------------

  task run_rand_test;
    int fd_r_exp;
    string line_read;

    //open expected results files
    fd_r_exp = $fopen(exp_res_filename, "r");
    if (fd_r_exp == 0) begin
      $error("Cannot open file %s for reading", exp_res_filename);
      error_ctr++;
    end

    for (int iter = 0; iter < VEC_CNT; iter++) begin
      //get the next exp result
      if (!($fgets(line_read, fd_r_exp))) begin
        $error("Failed to read a new line");
        error_ctr++;
      end
      void'($sscanf(line_read, "%s %s %h", exp_mode, exp_strength, exp_result));

      mode <= test_vector_q[0].mode;
      strength <= test_vector_q[0].strength;
      
      //start keccak
      @(posedge clk_tb);
      sha3_start <= 1;
      @(posedge clk_tb);
      sha3_start <= 0;

      //new message start
      @(posedge clk_tb);
      msg_start <= 1;
      @(posedge clk_tb);
      msg_start <= 0;

      //send the input vector
      for (int i = 0; i < MAX_MSG_WR; i++) begin
        if ( |test_vector_q[0].input_valid[i] ) begin
          write_single_msg(test_vector_q[0].input_vector[i], test_vector_q[0].input_valid[i]);
        end
      end

      //process the block
      sha3_process <= 1;
      @(posedge clk_tb);
      sha3_process <= 0;

      //$display("[%t] Waiting for state valid)", $time);

      wait (sha3_state_vld == 1'b1);
      
      //check absorb
      @(negedge clk_tb);
      check_results(1'b0, 0);

      //Do a squeeze for Shake
      if (test_vector_q[0].mode == sha3_pkg::Shake) begin
        sha3_run <= 1'b1;
        @(posedge clk_tb);
        sha3_run <= 1'b0;
        @(posedge clk_tb);

        wait (sha3_state_vld == 1'b1);

        //check squeeze
        @(negedge clk_tb);
        check_results(1'b1);
      end

      @(posedge clk_tb);
      sha3_done = abr_prim_mubi_pkg::MuBi4True;
      @(posedge clk_tb);
      sha3_done = abr_prim_mubi_pkg::MuBi4False;

      test_vector_q.pop_front();
      tc_ctr++;
    end

    $fclose(fd_r_exp);

  endtask // run_hw_if_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------
  `include "five_squeeze_test.svh"

  initial
    begin : main
      $write("PLAYBOOK_RANDOM_SEED = %s\n", getenv("PLAYBOOK_RANDOM_SEED"));
      $display("   -- Testbench for SHA3 started --");

      init_sim();
      reset_dut();

      if ($value$plusargs("SHA3_TEST=%s", sha3_testname)) begin : alternate_test
        $display("    =================================================================");
        $display("    Running SHA3_TEST = %s", sha3_testname);
        $display("    =================================================================");

        if (sha3_testname == "five_squeeze_test") begin 
          gen_five_squeeze_test_vectors();
          five_squeeze_test();
        end else begin
        //default rand test
          gen_rand_test_vectors();
          run_rand_test();
        end
      //default rand test
      end else begin
        gen_rand_test_vectors();
        run_rand_test();
      end

      @(posedge clk_tb);
      display_test_result();

      $display("   -- Testbench for SHA3 done. --");
      $finish;
    end // main

  abr_prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o;

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3FsmCheck_A,
    dut.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KeccakRoundFsmCheck_A,
    dut.u_keccak.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3padFsmCheck_A,
    dut.u_pad.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WrMsgCountCheck_A,
    dut.u_pad.u_wrmsg_count, alert_tx_o[1])

  `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RoundCountCheck_A,
    dut.u_keccak.u_round_count, alert_tx_o[1])

endmodule // sha3_tb

//======================================================================
// EOF sha3_tb.sv
//======================================================================
