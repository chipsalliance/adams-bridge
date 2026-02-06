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
//#$includes

//$#

module fv_ntt_ctrl_constraints
    //#$imports
    import ntt_defines_pkg::*;
    //$#
#(
    parameter REG_SIZE         = 23,
    parameter RADIX            = 23,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = 8,
    parameter MEM_ADDR_WIDTH   = 15,
    //#$localparams
    localparam NTT_NUM_ROUNDS       = 4,
    localparam PWO_NUM_ROUNDS       = 1,
    localparam NTT_READ_ADDR_STEP   = 16,
    localparam NTT_WRITE_ADDR_STEP  = 1,
    localparam INTT_READ_ADDR_STEP  = 1,
    localparam INTT_WRITE_ADDR_STEP = 16,
    localparam PWO_READ_ADDR_STEP   = 1,
    localparam PWO_WRITE_ADDR_STEP  = 1,
    localparam MEM_LAST_ADDR        = 63
    //$#//
) (
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
    input                            pi_masking_en,
    input                            pi_mlkem,
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
    input logic                      po_pw_share_mem_rden,
    input logic                      po_busy,
    input logic                      po_done,
    input logic                      po_ntt_passthrough,
    input logic                      po_intt_passthrough
    //$#//
);
default clocking default_clk @(posedge pi_clk); endclocking


  logic [9:0] fv_butterflylatancy; 

  always_ff @(posedge pi_clk, negedge pi_reset_n) begin
    if(!pi_reset_n || pi_zeroize)
      fv_butterflylatancy <= '0;
    else  begin
      fv_butterflylatancy <= {po_bf_enable,fv_butterflylatancy[9:1]};
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


  logic [6:0] sampler_valid_counter;

  always_ff @(posedge pi_clk) begin
    if (!pi_reset_n || pi_zeroize || po_done) begin
      sampler_valid_counter <= 7'd0;
    end else if (pi_sampler_valid && (ntt_ctrl.read_fsm_state_ps == RD_EXEC || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)) begin
      sampler_valid_counter <= sampler_valid_counter + 7'd1;
    end
  end

  property assume_buf0_valid_p;
    !pi_buf0_valid;
  endproperty
  assume_buf0_valid: assume property (assume_buf0_valid_p);


  property wip_ntt_mode;
    (pi_ntt_mode == pwm || pi_ntt_mode == pwa || pi_ntt_mode == pws || (pi_mlkem && pi_ntt_mode == pairwm)) ;
  endproperty
  assume_ntt_mode: assume property (wip_ntt_mode);

   property assume_pairwm_p;
    (pi_ntt_mode != pairwm)
  |->
    !pi_mlkem;
  endproperty
  assume_pairwm: assume property (assume_pairwm_p);


  property assume_accumulate_p;
    (pi_ntt_mode == pwa || pi_ntt_mode == pws)
  |->
    !pi_accumulate;
  endproperty
  assume_accumulate: assume property (assume_accumulate_p);


  property assume_masking_en_p;
    (pi_ntt_mode == pwa || pi_ntt_mode == pws)
  |->
    !pi_masking_en;
  endproperty
  assume_masking_en: assume property (assume_masking_en_p);


  property wip_butterfly_ready;
    pi_butterfly_ready == fv_butterflylatancy[0];
  endproperty
  assume_wip_butterfly_ready: assume property(wip_butterfly_ready);


  property stable_mode;
    ##1 
    aux_mode 
  |->
    $stable(pi_ntt_mode);
  endproperty
  assume_stable_mode : assume property(stable_mode);


  property assume_stable_accumulate_p;
    ##1
    aux_mode
  |->
    $stable(pi_accumulate);
  endproperty
  assume_stable_accumulate: assume property(assume_stable_accumulate_p);


  property assume_stable_masking_en_p;
    ##1
    aux_mode
  |->
    $stable(pi_masking_en);
  endproperty
  assume_stable_masking_en: assume property(assume_stable_masking_en_p);


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

  stable_mlkem: assume property (
    ##1
    aux_mode
  |->
    $stable(pi_mlkem)
  );

  assume_ntt_enable: assume property ( //this constraint added for read_idle_eventually_left assertion
    s_eventually(pi_ntt_enable)
  );


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

