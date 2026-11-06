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


module fv_ntt_ctrl_pwo_constraints
  //import mldsa_ctrl_pkg::*;
  //import mldsa_params_pkg::*;
  import ntt_defines_pkg::*;
  //import fv_ntt_ctrl_pwo_pkg::*;
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
  input                            pi_mlkem,
  input logic                      po_bf_enable,
  input logic [2:0]                po_opcode,
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


  logic [9:0] fv_butterflylatancy;

  always_ff @(posedge pi_clk, negedge pi_reset_n) begin
    if(!pi_reset_n || pi_zeroize) begin
      fv_butterflylatancy <= '0;
    end else begin
      fv_butterflylatancy <= {po_bf_enable,fv_butterflylatancy[9:1]};
    end
  end


  logic fv_aux_mode;

  always_ff@(posedge pi_clk or negedge pi_reset_n) begin
    if(!pi_reset_n || pi_zeroize) begin
      fv_aux_mode <= 1'b0;
    end else if(pi_ntt_enable) begin
      fv_aux_mode <= 1'b1;
    end else if(po_done) begin
      fv_aux_mode <= 1'b0;
    end
  end


  logic [1:0] fv_count;
  logic [1:0] fv_count_reg;

  always_ff @(posedge pi_clk or negedge pi_reset_n) begin
    if (!pi_reset_n || pi_zeroize || po_buf_wr_rst_count) begin
      fv_count <= '0;
      fv_count_reg <= '0;
    end else if (po_buf_wren) begin
      fv_count <= fv_count + 1;
      fv_count_reg <= fv_count;
    end
  end

  logic [6:0] fv_sampler_valid_counter;

  always_ff @(posedge pi_clk) begin
    if (!pi_reset_n || pi_zeroize || po_done) begin
      fv_sampler_valid_counter <= 7'd0;
    end else if (pi_sampler_valid && (ntt_ctrl.read_fsm_state_ps == RD_EXEC || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)) begin
      fv_sampler_valid_counter <= fv_sampler_valid_counter + 7'd1;
    end
  end


  property wip_ntt_mode;
    (pi_ntt_mode == pwm || pi_ntt_mode == pwa || pi_ntt_mode == pws ||(pi_mlkem && pi_ntt_mode == pairwm)) ;
  endproperty
  assume_ntt_mode: assume property (wip_ntt_mode);


  property wip_butterfly_ready;
    pi_butterfly_ready == fv_butterflylatancy[0];
  endproperty
  assume_wip_butterfly_ready: assume property(wip_butterfly_ready);


  property stable_mode;
    ##1
    fv_aux_mode
  |->
    $stable(pi_ntt_mode);
  endproperty
  assume_stable_mode : assume property(stable_mode);


  property stable_pwo_mem_base_addr_p;
    ##1
    fv_aux_mode
  |->
    $stable(pi_pwo_mem_base_addr);
  endproperty
  assume_stable_pwo_mem_base_addr: assume property (stable_pwo_mem_base_addr_p);

  assume_pwo_mem_base_addr: assume property (

    pi_pwo_mem_base_addr.pw_base_addr_a <'d16320 &&
    pi_pwo_mem_base_addr.pw_base_addr_b <'d16320 &&
    pi_pwo_mem_base_addr.pw_base_addr_c <'d16320

  );


  property stable_shuffle_en_p;
    ##1
    fv_aux_mode
  |->
    $stable(pi_shuffle_en);
  endproperty
  assume_stable_shuffle_en: assume property (stable_shuffle_en_p);


  property assume_buf0_valid_p;
    !pi_buf0_valid;
  endproperty
  assume_buf0_valid: assume property (assume_buf0_valid_p);


  property sampler_valid_max_64_p;
    fv_sampler_valid_counter < 7'd64
  |=>
    s_eventually(pi_sampler_valid);
  endproperty
  assume_sampler_valid_max_64: assume property (sampler_valid_max_64_p);


  property not_more_64_sampler_valid_p;
    fv_sampler_valid_counter == 7'd64
  |->
    !pi_sampler_valid;
  endproperty
  assume_not_more_64_sampler_valid: assume property (not_more_64_sampler_valid_p);
endmodule


bind ntt_ctrl fv_ntt_ctrl_pwo_constraints fv_ntt_ctrl_pwo_constraints_i(
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
    .pi_mlkem (mlkem),
    .po_bf_enable (bf_enable),
    .po_opcode (opcode),
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
