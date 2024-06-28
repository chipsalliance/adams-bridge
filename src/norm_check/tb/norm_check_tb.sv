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
// norm_check_tb.sv
// --------
// 
//
//
//======================================================================

`default_nettype none
`include "caliptra_reg_defines.svh"

module norm_check_tb
    import norm_check_defines_pkg::*;
#(
    parameter NUM_WR = 4, //TODO: sample_buffer needs more writes than reads?
    parameter NUM_RD = 4,
    parameter BUFFER_DATA_W = 8,
    parameter REG_SIZE = 24,
    parameter MEM_ADDR_WIDTH = 15
) 
();

parameter CLK_HALF_PERIOD = 5;
parameter CLK_PERIOD      = 2 * CLK_HALF_PERIOD;

parameter DILITHIUM_Q = 8380417;
parameter DILITHIUM_ETA = 2;
parameter DILITHIUM_TAU = 60;
parameter DILITHIUM_GAMMA1 = 2**19;
parameter DILITHIUM_GAMMA2 = (DILITHIUM_Q -1)/32;
parameter DILITHIUM_BETA = DILITHIUM_TAU * DILITHIUM_ETA;

parameter Z_BOUND = DILITHIUM_GAMMA1 - DILITHIUM_BETA;
parameter R0_BOUND = DILITHIUM_GAMMA2 - DILITHIUM_BETA;
parameter CT0_BOUND = DILITHIUM_GAMMA2;


//----------------------------------------------------------------
// Register and Wire declarations.
//----------------------------------------------------------------
reg           clk_tb;
reg           reset_n_tb;
reg           cptra_pwrgood_tb;
reg           zeroize_tb;
reg           en_tb;
reg [4*REG_SIZE-1:0] coeff_tb, mem_wr_data_o, coeff_a_tb, coeff_b_tb;
reg [MEM_ADDR_WIDTH-1:0] src_base_tb;
reg r0_rdy_tb;
logic [255:0][REG_SIZE-1:0] coeff_array, coeff_high, coeff_low;
logic [3:0][3:0] coeff_high_tb;
logic kdone_tb;
chk_norm_mode_t mode_tb;

norm_check_top dut(
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .norm_check_enable(en_tb),
    .mode(mode_tb),
    .mem_base_addr(src_base_tb),
    .mem_a_rd_req(),
    .mem_b_rd_req(),
    .mem_a_rd_data(coeff_a_tb),
    .mem_b_rd_data(coeff_b_tb),
    .invalid(),
    .norm_check_ready(),
    .norm_check_done()
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

task init_sim;
    begin
        $display("Start of init\n");
        clk_tb = 0;
        reset_n_tb = 0;
        cptra_pwrgood_tb = 0;
        // hint_4bit_tb = 0;
        // index_tb = 0;
        zeroize_tb = 0;
        en_tb = 0;
        coeff_tb = 0;
        src_base_tb = 'h0;
        coeff_a_tb = 0;
        coeff_b_tb = 0;
        // dest_base_tb = 'h0;
        // r0_rdy_tb = 'b0;
        // coeff_high_tb = 'h0;
        // kdone_tb = 'b0;
    end
endtask

//----------------------------------------------------------------
// reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task reset_dut;
    begin
      $display("*** Toggle reset.");
    //   cptra_pwrgood_tb = '0;
      reset_n_tb = 0;
    
    //   #(2 * CLK_PERIOD);
    //   cptra_pwrgood_tb = 1;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut



task norm_check_test;
    $display("Starting check norm ctrl test\n");
    @(posedge clk_tb);
    $display("Z bound mode\n");
    mode_tb = z_bound;
    en_tb = 1'b1;
    
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h0;
    @(posedge clk_tb);
    for (int poly = 0; poly < 7; poly++) begin
      $display("Starting poly %0d", poly);
      for (int i = 0; i < 32; i++) begin
        coeff_a_tb = {REG_SIZE'($urandom_range(0,Z_BOUND-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-Z_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(0,Z_BOUND)), REG_SIZE'($urandom_range(0,Z_BOUND))};
        coeff_b_tb = {REG_SIZE'($urandom_range(0,Z_BOUND-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-Z_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(0,Z_BOUND)), REG_SIZE'($urandom_range(0,Z_BOUND))};
        @(posedge clk_tb);
      end
    end
    @(posedge clk_tb);

    while (!dut.norm_check_done) @(posedge clk_tb);
    if (dut.invalid) $error("Expected z check to be valid, received invalid\n");
    else $display("Norm check for z is successful\n");

    $display("r0 bound mode\n");
    mode_tb = r0_bound;
    en_tb = 1'b1;
    
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h40;
    for (int poly = 0; poly < 8; poly++) begin
      $display("Starting poly %0d", poly);
      for (int i = 0; i < 32; i++) begin
        coeff_a_tb = {REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1))};
        coeff_b_tb = {REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1)), REG_SIZE'($urandom_range(DILITHIUM_Q-R0_BOUND, DILITHIUM_Q-1))};
        @(posedge clk_tb);
      end
    end
    @(posedge clk_tb);

    while (!dut.norm_check_done) @(posedge clk_tb);
    if (dut.invalid) $error("Expected r0 check to be valid, received invalid\n");
    else $display("Norm check for r0 is successful\n");

    $display("ct0 bound mode\n");
    mode_tb = ct0_bound;
    en_tb = 1'b1;
    
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h80;
    for (int poly = 0; poly < 8; poly++) begin
      $display("Starting poly %0d", poly);
      for (int i = 0; i < 32; i++) begin
        coeff_a_tb = {REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1))};
        coeff_b_tb = {REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1))};
        @(posedge clk_tb);
      end
    end
    @(posedge clk_tb);

    while (!dut.norm_check_done) @(posedge clk_tb);
    if (dut.invalid) $error("Expected ct0 check to be valid, received invalid\n");
    else $display("Norm check for ct0 is successful\n");

    //Rejected test
    $display("ct0 bound mode\n");
    mode_tb = ct0_bound;
    en_tb = 1'b1;
    
    @(posedge clk_tb);
    en_tb = 1'b0;
    src_base_tb = 'h80;
    for (int poly = 0; poly < 8; poly++) begin
      $display("Starting poly %0d", poly);
      for (int i = 0; i < 32; i++) begin
        coeff_a_tb = {REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(CT0_BOUND,DILITHIUM_Q-1))};
        coeff_b_tb = {REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(0,CT0_BOUND-1)), REG_SIZE'($urandom_range(CT0_BOUND,DILITHIUM_Q-1))};
        @(posedge clk_tb);
      end
    end
    @(posedge clk_tb);

    while (!dut.norm_check_done) @(posedge clk_tb);
    if (dut.invalid) $display("Norm check for ct0 is rejected\n");
    else $display("Norm check for ct0 is successful\n");

    // while (!dut.norm_check_done) @(posedge clk_tb);
    $display("Ctrl test done\n");

endtask


initial begin
    init_sim();
    reset_dut();
    norm_check_test();
    repeat(1000) @(posedge clk_tb);
    $finish;
end
endmodule