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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either sibress or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
//======================================================================
//
// sample_in_ball_tb.sv
// --------
//
//======================================================================

import "DPI-C" function string getenv(input string env_name);

module sample_in_ball_tb
  import sampler_pkg::*;
  import abr_params_pkg::*;
(
`ifdef VERILATOR
  input bit clk_tb
`endif
  );

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
  logic [SIB_PISO_INPUT_RATE-1:0]                data_i;

  //input data to sample in ball
  logic                                          piso_valid;
  logic                                          piso_hold;
  logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] piso_data;

  logic                                          sib_done;
  //memory if 
  logic [1:0]                                    cs;
  logic [1:0]                                    we;
  logic [1:0][7:2]                               addr;
  logic [1:0][3:0][MLDSA_Q_WIDTH-2:0]            wrdata;
  logic [1:0][3:0][MLDSA_Q_WIDTH-2:0]            rddata;

  logic zeroize;

  string seed_filename, vector_filename, exp_res_filename;
  assign exp_res_filename = "exp_results.txt";
  assign seed_filename = "input_seeds.txt";
  assign vector_filename = "input_vectors.txt";

  int fd_r_exp;

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

  assign clk_i = clk_tb;
  assign rst_ni = reset_n_tb;
  
  //SRAM
  sib_mem
  #(
      .DATA_WIDTH((MLDSA_Q_WIDTH-1)*4),
      .DEPTH     (MLDSA_N/4  ),
      .NUM_PORTS (2              )
  )
  sib_mem_inst
  (
      .clk_i(clk_i),
      .zeroize(zeroize),

      .cs_i(cs),
      .we_i(we),
      .addr_i(addr),
      .wdata_i(wrdata),
  
      .rdata_o(rddata)
  );

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
  abr_piso #(
     .PISO_BUFFER_W(SIB_PISO_BUFFER_W),
     .PISO_INPUT_RATE(SIB_PISO_INPUT_RATE),
     .PISO_OUTPUT_RATE(SIB_PISO_OUTPUT_RATE)
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

  sample_in_ball_ctrl #(
    .SIB_NUM_SAMPLERS(SIB_NUM_SAMPLERS),
    .SIB_SAMPLE_W(SIB_SAMPLE_W),
    .SIB_TAU(SIB_TAU)
  ) dut (
  .clk(clk_i),
  .rst_b(rst_ni),
  .zeroize(zeroize), 
  //input data
  .data_valid_i(piso_valid),
  .data_hold_o(piso_hold),
  .data_i(piso_data),
  .sib_done_o(sib_done),

  //memory_if
  .cs_o(cs),
  .we_o(we),
  .addr_o(addr),
  .wrdata_o(wrdata),
  .rddata_i(rddata)
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
      zeroize = 0;

      repeat (2) @(posedge clk_tb);
      reset_n_tb = 1;
      zeroize = 1;

      repeat (1) @(posedge clk_tb);
      zeroize = 0;

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

  task clear_sram;
    // Variables
    bit [6:0] clear_addr;
    int byt;

    // Slam
    $display("SRAM clear from %h to %h", 0, MLDSA_N/4);
    for (clear_addr = 0; clear_addr < (MLDSA_N/4); clear_addr++) begin
        sib_mem_inst.mem[clear_addr[5:0]] = '0;
    end
    $display("SRAM clear completed");
  endtask

  //----------------------------------------------------------------
  // Scoreboard 
  //----------------------------------------------------------------
  
  initial begin
    string exp_res_read;
  
    logic [MLDSA_Q_WIDTH-2:0] exp_result;
    logic [3:0][MLDSA_Q_WIDTH-2:0] actual_result;
    

    forever begin
      @(posedge clk_tb)
      if (sib_done & ~zeroize) begin
        //get the next exp result
        if (!($fgets(exp_res_read, fd_r_exp))) begin
          $error("Failed to read a new line");
          error_ctr++;
        end
        //check each coefficient
        for (int coeff = 0; coeff < MLDSA_N; coeff++) begin
            //parse line for expected result
            exp_result = exp_res_read.substr(coeff*7, coeff*7+6).atohex();

            actual_result = sib_mem_inst.mem[coeff/4];
          
          if (exp_result != actual_result[coeff%4]) begin
            //ERROR
            $display("[%t] Expected results mismatch", $time);
            $display("[%t] Coefficient entry: %x", $time, coeff);
            $display("[%t] Actual:   %x", $time,actual_result[coeff%4]);
            $display("[%t] Expected: %x", $time,exp_result);
            error_ctr += 1;
          end
        end
      end
    end
    $fclose(fd_r_exp);
  end



  initial begin
    forever begin
      @(posedge clk_tb)
      if (sib_done == 1) begin
        zeroize <= 1;
        @(posedge clk_tb)
        zeroize <= 0;
      end
    end
  end


  //----------------------------------------------------------------
  // write_single_msg()
  //
  // Write the given msg to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_msg(logic [SIB_PISO_INPUT_RATE-1:0] rand_samples);
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
    $system($sformatf("python sample_in_ball.py"));


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
  parameter PISO_INPUT_CHARS = SIB_PISO_INPUT_RATE/4;
  parameter PISO_INPUT_DWORDS = SIB_PISO_INPUT_RATE/32;
  task run_rand_test;
    int fd_r_inp;
    string line_read;
    string line_substr;
    logic [PISO_INPUT_DWORDS-1:0][31:0] test_data;

    //open input vectors
    fd_r_inp = $fopen(vector_filename, "r");
    if (fd_r_inp == 0) begin
      $error("Cannot open file %s for reading", vector_filename);
      error_ctr++;
    end

    for (int iter = 0; iter < VEC_CNT; iter++) begin

      //get the next input vector
      if (!($fgets(line_read, fd_r_inp))) begin
        $error("Failed to read a new line");
        error_ctr++;
      end


      for (int dword = 0; dword < PISO_INPUT_DWORDS; dword++) begin
        test_data[dword] = line_read.substr((PISO_INPUT_CHARS - dword*8 - 8), (PISO_INPUT_CHARS - 1 - dword*8)).atohex();
      end
      write_single_msg(test_data);


      wait (sib_done == 1);
      wait (sib_done == 0);

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
      $display("   -- Testbench for SAMPLE_IN_BALL started --");

      init_sim();
      reset_dut();

      gen_rand_test_vectors();
      run_rand_test();

      @(posedge clk_tb);
      display_test_result();

      $display("   -- Testbench for SAMPLE_IN_BALL done. --");
      $finish;
    end // main

endmodule // sample_in_ball_tb

//======================================================================
// EOF sample_in_ball_tb.sv
//======================================================================
