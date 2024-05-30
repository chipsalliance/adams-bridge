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
// rej_sampler_tb.sv
// --------
//
//======================================================================

import "DPI-C" function string getenv(input string env_name);

module rej_sampler_tb
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

  parameter REJ_NUM_SAMPLERS = 5;
  parameter REJ_SAMPLE_W     = 24;
  parameter REJ_VLD_SAMPLES  = 4;
  parameter PISO_BUFFER_W    = 1440;
  parameter PISO_INPUT_RATE  = 1344;
  parameter PISO_OUTPUT_RATE = 120;
  parameter DILITHIUM_Q = 8380417;
  parameter DILITHIUM_Q_W = $clog2(DILITHIUM_Q) + 1;
  parameter DILITHIUM_N = 256;


  `ifndef VERILATOR
  int MAX_CYCLES;
  int VEC_CNT;

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

  //input data to piso
  logic                                          data_valid_i;
  logic                                          data_hold_o;
  logic [PISO_INPUT_RATE-1:0]                    data_i;

  //input data
  logic                                          piso_valid;
  logic                                          piso_hold;
  logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0] piso_data;

  //output data
  logic                                         data_valid_o;
  logic [REJ_VLD_SAMPLES-1:0][DILITHIUM_Q_W-1:0] data_o;

  logic zeroize;

  //----------------------------------------------------------------
  // Register and Wire declarations.
  //----------------------------------------------------------------
  reg [31 : 0] cycle_ctr;
  reg [31 : 0] error_ctr;
  reg [31 : 0] vld_coeff_ctr;
  reg [31 : 0] tc_ctr;

`ifndef VERILATOR
  reg clk_tb;
`endif
  reg clk_i;
  reg reset_n_tb;
  reg rst_ni;
  reg [31 : 0] read_data;

  assign clk_i = clk_tb;
  assign rst_ni = reset_n_tb;

  logic [DILITHIUM_Q_W-1:0] exp_result;
  logic [DILITHIUM_Q_W-1:0] expected_results[$];  // queue of results

  string seed_filename, vector_filename, exp_res_filename;
  assign exp_res_filename = "exp_results.txt";
  assign seed_filename = "input_seeds.txt";
  assign vector_filename = "input_vectors.txt";

  int fd_r_exp;

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  abr_piso #(
    .PISO_BUFFER_W(PISO_BUFFER_W),
    .PISO_INPUT_RATE(PISO_INPUT_RATE),
    .PISO_OUTPUT_RATE(PISO_OUTPUT_RATE)
 ) piso_i (
 .clk(clk_i),
 .rst_b(rst_ni),
 .zeroize(zeroize),
 .valid_i(data_valid_i),
 .hold_o(data_hold_o),
 .data_i(data_i),
 .valid_o(piso_valid),
 .hold_i(piso_hold),
 .data_o(piso_data)
 );

  rej_sampler_ctrl#(
    .REJ_NUM_SAMPLERS(REJ_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJ_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJ_VLD_SAMPLES),
    .REJ_VALUE(DILITHIUM_Q)
  ) dut (
  .clk(clk_i),
  .rst_b(rst_ni),
  .zeroize(zeroize), 
  //input data
  .data_valid_i(piso_valid),
  .data_hold_o(piso_hold),
  .data_i(piso_data),

  //output data
  .data_valid_o(data_valid_o),
  .data_o(data_o)
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
      vld_coeff_ctr = '0;
`ifndef VERILATOR
      clk_tb        = 0;
`endif
      reset_n_tb    = 0;

      zeroize       = 0;
      data_valid_i  = '0;
      data_i        = '0;

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
  // Scoreboard 
  //----------------------------------------------------------------
  initial begin
    forever begin
      @(posedge clk_tb)
      if (data_valid_o) begin
        if (expected_results.size() >= 4) begin
          for (int i = 0; i < REJ_VLD_SAMPLES; i++) begin
            vld_coeff_ctr += 1; //increment vld coeff ctr
            if (expected_results[0] != data_o[i]) begin
              //ERROR
              $display("[%t] Expected results mismatch for output index %d", $time, i);
              $display("[%t] Actual:   %x", $time,data_o[i]);
              $display("[%t] Expected: %x", $time,expected_results[0]);
              error_ctr += 1;
            end
            expected_results.pop_front();
          end
        end else begin
          //ERROR
          $display("[%t] Not enough valid samples in the queue", $time);
          error_ctr += 1;
        end
      end
    end

  end

  initial begin
    forever begin
      @(posedge clk_tb)
      if (vld_coeff_ctr == 256) begin
        zeroize <= 1;
        @(posedge clk_tb)
        zeroize <= 0;
      end
    end
  end

  initial begin
    forever begin
      @(posedge zeroize)
          vld_coeff_ctr = '0;
          expected_results = {};
    end
  end

  //----------------------------------------------------------------
  // write_single_msg()
  //
  // Write the given msg to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_msg(logic [PISO_INPUT_RATE-1:0] rand_samples);
    begin
      data_valid_i <= 1;
      data_i       <= rand_samples;

      //don't like this, but solves the timing issue
      @(posedge clk_tb);
      //Make sure no hold
      //drop this transaction if zeroize is set
      while ((data_hold_o == 1) & (zeroize == 0)) @(posedge clk_tb);

      //@(posedge clk_tb);
      data_valid_i <= 0;
      data_i       <= 'x;

    end
  endtask // write_single_msg

  //----------------------------------------------------------------
  // gen_rand_test_vectors()
  //----------------------------------------------------------------
  task gen_rand_test_vectors;
    int fd_w;

    fd_w = $fopen(seed_filename, "a");
    if (fd_w == 0) $error("Cannot open file %s for writing", seed_filename);
    
    for (int i = 0; i < VEC_CNT; i++) begin
      //Write random_ eeds
      $fwrite(fd_w, "%0d \n", $urandom());
    end
    $fclose(fd_w);
    //generate input vectors and expected results
    $system($sformatf("python rej_sampler.py"));


    //open expected results files
    fd_r_exp = $fopen(exp_res_filename, "r");
    if (fd_r_exp == 0) begin
      $error("Cannot open file %s for reading", exp_res_filename);
      error_ctr++;
    end

  endtask


  //----------------------------------------------------------------
  // run_rand_test()
  //----------------------------------------------------------------
  parameter PISO_INPUT_CHARS = PISO_INPUT_RATE/4;
  parameter PISO_INPUT_DWORDS = PISO_INPUT_RATE/32;
  task run_rand_test;
    int fd_r_inp;
    string line_read;
    string line_substr;
    int num_states;
    logic [PISO_INPUT_DWORDS-1:0][31:0] test_data;

    //open input vectors
    fd_r_inp = $fopen(vector_filename, "r");
    if (fd_r_inp == 0) begin
      $error("Cannot open file %s for reading", vector_filename);
      error_ctr++;
    end

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
      for (int res = 0; res < DILITHIUM_N; res++) begin
        exp_result = line_read.substr(res*7, res*7 + 7-2).atohex();
        expected_results.push_back(exp_result);
      end

      //get the next input vector
      if (!($fgets(line_read, fd_r_inp))) begin
        $error("Failed to read a new line");
        error_ctr++;
      end

      num_states = (line_read.len()/PISO_INPUT_CHARS);
      //$display("Vector Length: %d", line_read.len());
      //$display("Number of states: %d", num_states);
      for (int state = 0; state < num_states; state++) begin
          line_substr = line_read.substr(state*PISO_INPUT_CHARS , (state*PISO_INPUT_CHARS)+PISO_INPUT_CHARS-1);
          //$display("State: %s", line_substr);
          for (int dword = 0; dword < PISO_INPUT_DWORDS; dword++) begin
            test_data[dword] = line_substr.substr((PISO_INPUT_CHARS - dword*8 - 8), (PISO_INPUT_CHARS - dword*8 - 1)).atohex();
            //$display("Dword: %d - %h", dword, test_data[dword]);
          end
          write_single_msg(test_data);
      end

      wait (zeroize == 1);
      wait (zeroize == 0);

      tc_ctr++;

    end

    $fclose(fd_r_inp);

  endtask // run_hw_if_test

  //----------------------------------------------------------------
  // The main test functionality.
  //----------------------------------------------------------------

  initial
    begin : main
      $write("PLAYBOOK_RANDOM_SEED = %s\n", getenv("PLAYBOOK_RANDOM_SEED"));
      $display("   -- Testbench for REJ_SAMPLER started --");

      init_sim();
      reset_dut();

      gen_rand_test_vectors();
      run_rand_test();

      @(posedge clk_tb);
      display_test_result();

      $display("   -- Testbench for REJ_SAMPLER done. --");
      $finish;
    end // main

endmodule // rej_sampler_tb

//======================================================================
// EOF rej_sampler_tb.sv
//======================================================================
