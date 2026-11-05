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

//$#//

module fv_sampler_top
    //#$imports
    import fv_sampler_top_pkg::*;
    import abr_sampler_pkg::*;
    import abr_sha3_pkg::*;
    import abr_params_pkg::*;
    import abr_prim_alert_pkg::*;
    import fv_sampler_top_pkg::*;
    //$#//
#(
    //#$localparams
    parameter bit SHA3_EN_MASKING = 1,
    localparam int SHA3_SHARE = (SHA3_EN_MASKING) ? 2 : 1,
    parameter SRAM_LATENCY = 1,
    parameter int ABR_NUM_NTT = 1
    //$#//
) (
    //#$ports
    input logic                                        pi_clk,
    input logic                                        pi_rst_b,
    input logic                                        pi_zeroize,
    input abr_sampler_mode_e                           pi_sampler_mode_i,
    input logic                                        pi_sha3_start_i,
    input logic                                        pi_msg_start_i,
    input logic                                        pi_msg_valid_i,
    input logic                                        po_msg_rdy_o,
    input logic [MsgStrbW-1:0]                         pi_msg_strobe_i,
    input logic [MsgWidth-1:0]                         pi_msg_data_i[SHA3_SHARE],
    input logic                                        pi_sampler_start_i,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_dest_base_addr_i,
    input mem_if_t                                     pi_sib_mem_rd_req_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               po_sib_mem_rd_data_o,
    input logic                                        po_sampler_busy_o,
    input logic                                        po_sampler_ntt_dv_o,
    input logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] po_sampler_ntt_data_o,
    input logic                                        po_sampler_mem_dv_o,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               po_sampler_mem_data_o[ABR_NUM_NTT],//[COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH]
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_sampler_mem_addr_o,
    input logic                                        pi_split_en_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               pi_rand_i,
    input logic                                        pi_sha3_masked_i,
    input logic                                        pi_keccak_rand_valid_i,
    input logic                                        pi_keccak_rand_early_i,
    input logic [abr_sha3_pkg::StateW/2-1:0]           pi_keccak_rand_data_i,
    input logic                                        pi_keccak_rand_aux_i,
    input logic                                        po_sampler_state_dv_o,
    input logic [abr_sha3_pkg::StateW-1:0]             po_sampler_state_data_o//[SHA3_SHARE]
    //$#//
);

    //#$instances
    fv_sampler_top_constraints #(
    .SHA3_EN_MASKING(SHA3_EN_MASKING),
    .SRAM_LATENCY (SRAM_LATENCY),
    .ABR_NUM_NTT (ABR_NUM_NTT)
    ) fv_sampler_top_constraints_i (.*);

    fv_sampler_top_whitebox #(
    .SHA3_EN_MASKING(SHA3_EN_MASKING),
    .SRAM_LATENCY (SRAM_LATENCY),
    .ABR_NUM_NTT (ABR_NUM_NTT)
    ) fv_sampler_top_whitebox_i (.*);

    //$#//



    endmodule


bind abr_sampler_top fv_sampler_top #(
    .SHA3_EN_MASKING(Sha3EnMasking),
    .SRAM_LATENCY (SRAM_LATENCY),
    .ABR_NUM_NTT (ABR_NUM_NTT)
) fv_sampler_top_i (
    .pi_clk (clk),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_sampler_mode_i (sampler_mode_i),
    .pi_sha3_start_i (sha3_start_i),
    .pi_msg_start_i (msg_start_i),
    .pi_msg_valid_i (msg_valid_i),
    .po_msg_rdy_o (msg_rdy_o),
    .pi_msg_strobe_i (msg_strobe_i),
    .pi_msg_data_i (msg_data_i),
    .pi_sampler_start_i (sampler_start_i),
    .pi_dest_base_addr_i (dest_base_addr_i),
    .pi_sib_mem_rd_req_i (sib_mem_rd_req_i),
    .po_sib_mem_rd_data_o (sib_mem_rd_data_o),
    .po_sampler_busy_o (sampler_busy_o),
    .po_sampler_ntt_dv_o (sampler_ntt_dv_o),
    .po_sampler_ntt_data_o (sampler_ntt_data_o),
    .po_sampler_mem_dv_o (sampler_mem_dv_o),
    .po_sampler_mem_data_o (sampler_mem_data_o),
    .po_sampler_mem_addr_o (sampler_mem_addr_o),
    .pi_split_en_i(split_en_i),
    .pi_rand_i(rand_i),
    .pi_sha3_masked_i(sha3_masked_i),
    .pi_keccak_rand_valid_i(keccak_rand_valid_i),
    .pi_keccak_rand_early_i(keccak_rand_early_i),
    .pi_keccak_rand_data_i(keccak_rand_data_i),
    .pi_keccak_rand_aux_i(keccak_rand_aux_i),
    .po_sampler_state_dv_o (sampler_state_dv_o),
    .po_sampler_state_data_o (sampler_state_data_o)
    //$#//
);

bind abr_sampler_top fv_sampler_top_m fv_sampler_top_fsm_i(
  .rst(!abr_sampler_top.rst_b || abr_sampler_top.zeroize),
  .clk(abr_sampler_top.clk),
  // Ports

  .sampler_done(abr_sampler_top.sampler_done),

  .sampler_start_i(abr_sampler_top.sampler_start_i),

  .sha3_fsm(),

  .sha3_squeezing(abr_sampler_top.sha3_squeezing),

  .sha3_state_dv(abr_sampler_top.sha3_state_dv),

  .sha3_state_hold(abr_sampler_top.sha3_state_hold),


  .sha3_process_vld(1'b1),
  .sha3_process(abr_sampler_top.sha3_process),


  .sha3_run_vld(1'b1),
  .sha3_run(abr_sampler_top.sha3_run),

   // Registers
  .cur_st(abr_sampler_top.sampler_fsm_ps),
  .sampler_done_temp(abr_sampler_top.sampler_done),
  .sampler_start_i_temp(abr_sampler_top.sampler_start_i),
  .sha3_squeezing_temp(abr_sampler_top.sha3_squeezing),
  .sha3_state_dv_temp(abr_sampler_top.sha3_state_dv),
  .sha3_state_hold_temp(abr_sampler_top.sha3_state_hold),

// States
  .DONE(abr_sampler_top.sampler_fsm_ps ==  ABR_SAMPLER_DONE),
  .IDLE(abr_sampler_top.sampler_fsm_ps ==  ABR_SAMPLER_IDLE),
  .PROC(abr_sampler_top.sampler_fsm_ps == ABR_SAMPLER_PROC),
  .RUN(abr_sampler_top.sampler_fsm_ps == ABR_SAMPLER_RUN),
  .WAIT(abr_sampler_top.sampler_fsm_ps == ABR_SAMPLER_WAIT)
);
