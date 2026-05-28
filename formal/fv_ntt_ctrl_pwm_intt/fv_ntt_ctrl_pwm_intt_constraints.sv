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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_ntt_ctrl_pwm_intt_constraints
  import mldsa_ctrl_pkg::*;
  import mldsa_params_pkg::*;
  import ntt_defines_pkg::*;
  import fv_ntt_ctrl_pwm_intt_pkg::*; 
#(
  parameter REG_SIZE         = 23,
  parameter RADIX            = 23,
  parameter MLDSA_Q          = 23'd8380417,
  parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
  parameter MLDSA_N          = 256,
  parameter MLDSA_LOGN       = 8,
  parameter MEM_ADDR_WIDTH   = 15
)
(
  //#$ports
  input                            pi_clk,
  input                            pi_reset_n,
  input                            pi_zeroize,
  input mode_t                     pi_ntt_mode,
  input                            pi_ntt_enable,
  input                            pi_butterfly_ready,
  input                            pi_buf0_valid,
  input                            pi_sampler_valid,
  input                            pi_accumulate,
  input ntt_mem_addr_t             pi_ntt_mem_base_addr,
  input pwo_mem_addr_t             pi_pwo_mem_base_addr,
  input                            pi_shuffle_en,
  input [5:0]                      pi_random,
  input logic                      po_bf_enable,
  input logic [2:0]                po_opcode,
  input logic                      po_masking_en_ctrl,
  input logic                      po_buf_wren,
  input logic                      po_buf_rden,
  input logic [1:0]                po_buf_wrptr,
  input logic [1:0]                po_buf_rdptr,
  input logic [6:0]                po_twiddle_addr,
  input logic [MEM_ADDR_WIDTH-1:0] po_mem_rd_addr,
  input logic [MEM_ADDR_WIDTH-1:0] po_mem_wr_addr,
  input logic                      po_mem_rd_en,
  input logic                      po_mem_wr_en,
  input logic                      po_buf_wr_rst_count,
  input logic                      po_buf_rd_rst_count,
  input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_a,
  input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_b,
  input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_c,
  input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_wr_addr_c,
  input logic                      po_pw_rden,
  input logic                      po_pw_wren,
  input logic                      po_busy,
  input logic                      po_done
  //$#//
);

  //#$localparams
  localparam NTT_NUM_ROUNDS = 4;
  localparam PWO_NUM_ROUNDS = 1;
  localparam NTT_READ_ADDR_STEP = 16;
  localparam NTT_WRITE_ADDR_STEP = 1;
  localparam INTT_READ_ADDR_STEP = 1;
  localparam INTT_WRITE_ADDR_STEP = 16;
  localparam PWO_READ_ADDR_STEP = 1;
  localparam PWO_WRITE_ADDR_STEP = 1;
  localparam MEM_LAST_ADDR = 63;
  //$#//


  default clocking default_clk @(posedge pi_clk); endclocking


  logic [12:0] fv_butterflylatancy; 

  always_ff @(posedge pi_clk, negedge pi_reset_n) begin
    if(!pi_reset_n || pi_zeroize)
      fv_butterflylatancy <= '0;
    else if (ntt_ctrl.rounds_count == 0) begin
      fv_butterflylatancy <= { po_bf_enable, fv_butterflylatancy[12:1] };
    end else begin
      fv_butterflylatancy <= { 8'd0, po_bf_enable, fv_butterflylatancy[4:1] };
    end
  end


  logic aux_mode;

  always_ff@(posedge pi_clk or negedge pi_reset_n) begin
    if(!pi_reset_n || pi_zeroize)
      aux_mode <= 1'b0;
    else if(pi_ntt_enable)
      aux_mode <= 1'b1;
    else if(po_done)
      aux_mode <= 1'b0;
  end


  logic [1:0] count;
  logic [1:0] count_reg;
 
  always_ff @(posedge pi_clk or negedge pi_reset_n) begin
    if (!pi_reset_n || pi_zeroize || po_buf_wr_rst_count) begin
      count <= '0;
      count_reg <= '0;
    end else if (po_buf_wren) begin
      count <= count + 1;
      count_reg <= count;
    end
  end
  

  logic [6:0] sampler_valid_counter;

  always_ff @(posedge pi_clk) begin
    if (!pi_reset_n || pi_zeroize || po_done) begin
      sampler_valid_counter <= 7'd0;
    end else if (pi_sampler_valid && (ntt_ctrl.read_fsm_state_ps == RD_EXEC || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)) begin
      sampler_valid_counter <= sampler_valid_counter + 7'd1;
    end
  end


  property wip_ntt_mode;
    pi_ntt_mode == pwm_intt;
  endproperty
  assume_ntt_mode: assume property (wip_ntt_mode);


  property wip_butterfly_ready;
    pi_butterfly_ready == fv_butterflylatancy[0];
  endproperty
  assume_wip_butterfly_ready: assume property(wip_butterfly_ready);


  stable_pwo_mem_base_addr: assume property (
    ##1
    aux_mode
  |->
    $stable(pi_pwo_mem_base_addr)
  );


  stable_shuffle_en: assume property (
    ##1
    aux_mode
  |->
    $stable(pi_shuffle_en)
  );


  property buf0_valid_constraint;
    count_reg == 3
  |-> 
    pi_buf0_valid;
  endproperty
  assume_buf0_valid_constraint: assume property (buf0_valid_constraint);


  property No_buf0_valid_constraint;
    (count_reg != 3) 
  |->
    !pi_buf0_valid;
  endproperty
  assume_No_buf0_valid_constraint: assume property (No_buf0_valid_constraint);


  assume_64_sampler_valid: assume property(
    sampler_valid_counter < 7'd64
  |=>
    s_eventually(pi_sampler_valid)
  );


  assume_not_more_64_sampler_valid: assume property(
    sampler_valid_counter == 7'd64
  |->
    !pi_sampler_valid
  );
endmodule


bind ntt_ctrl fv_ntt_ctrl_pwm_intt_constraints constraints_inst(
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_ntt_mode (ntt_mode),
    .pi_ntt_enable (ntt_enable),
    .pi_butterfly_ready (butterfly_ready),
    .pi_buf0_valid (buf0_valid),
    .pi_sampler_valid (sampler_valid),
    .pi_accumulate (accumulate),
    .pi_ntt_mem_base_addr (ntt_mem_base_addr),
    .pi_pwo_mem_base_addr (pwo_mem_base_addr),
    .pi_shuffle_en (shuffle_en),
    .pi_random (random),
    .po_bf_enable (bf_enable),
    .po_opcode (opcode),
    .po_masking_en_ctrl (masking_en_ctrl),
    .po_buf_wren (buf_wren),
    .po_buf_rden (buf_rden),
    .po_buf_wrptr (buf_wrptr),
    .po_buf_rdptr (buf_rdptr),
    .po_twiddle_addr (twiddle_addr),
    .po_mem_rd_addr (mem_rd_addr),
    .po_mem_wr_addr (mem_wr_addr),
    .po_mem_rd_en (mem_rd_en),
    .po_mem_wr_en (mem_wr_en),
    .po_buf_wr_rst_count (buf_wr_rst_count),
    .po_buf_rd_rst_count (buf_rd_rst_count),
    .po_pw_mem_rd_addr_a (pw_mem_rd_addr_a),
    .po_pw_mem_rd_addr_b (pw_mem_rd_addr_b),
    .po_pw_mem_rd_addr_c (pw_mem_rd_addr_c),
    .po_pw_mem_wr_addr_c (pw_mem_wr_addr_c),
    .po_pw_rden (pw_rden),
    .po_pw_wren (pw_wren),
    .po_busy (busy),
    .po_done (done)
);
