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


module fv_ntt_top_mlkem_top
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE         = 24,
    parameter NTT_REG_SIZE     = REG_SIZE-1,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = $clog2(MLDSA_N),
    parameter MEM_ADDR_WIDTH   = 15,
    parameter MEM_DATA_WIDTH   = 4*REG_SIZE,
    parameter WIDTH            = 46
    //#$localparams
    //$#//
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input mode_t                     pi_mode,
    input                            pi_ntt_enable,
    input ntt_mem_addr_t             pi_ntt_mem_base_addr,
    input pwo_mem_addr_t             pi_pwo_mem_base_addr,
    input                            pi_accumulate,
    input                            pi_sampler_valid,
    input                            pi_shuffle_en,
    input                            pi_mlkem,
    input                            pi_masking_en,
    input [5:0]                      pi_random,
    input [4:0][WIDTH-1:0]           pi_rnd_i,
    input mem_if_t                   po_mem_wr_req,
    input mem_if_t                   po_mem_rd_req,
    input logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] po_mem_wr_data,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_mem_rd_data,
    input mem_if_t                   po_pwm_a_rd_req,
    input mem_if_t                   po_pwm_b_rd_req,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
    input [ABR_MEM_MASKED_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
    input logic                      po_ntt_busy,
    input logic                      po_ntt_done
    //$#//
);

    
    fv_ntt_top_mlkem_constraints #(
        .REG_SIZE(REG_SIZE),
        .NTT_REG_SIZE(NTT_REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_Q_DIV2_ODD(MLDSA_Q_DIV2_ODD),
        .MLDSA_N(MLDSA_N),
        .MLDSA_LOGN(MLDSA_LOGN),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
        .MEM_DATA_WIDTH(MEM_DATA_WIDTH),
        .WIDTH(WIDTH)
    ) fv_constraints_i (.*);
    
    fv_ntt_top_mlkem #(
        .REG_SIZE(REG_SIZE),
        .NTT_REG_SIZE(NTT_REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_Q_DIV2_ODD(MLDSA_Q_DIV2_ODD),
        .MLDSA_N(MLDSA_N),
        .MLDSA_LOGN(MLDSA_LOGN),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
        .MEM_DATA_WIDTH(MEM_DATA_WIDTH),
        .WIDTH(WIDTH)
    ) fv_ntt_top_mlkem_i (.*);
    
   fv_ntt_top_mlkem_internal #(
        .REG_SIZE(REG_SIZE),
        .NTT_REG_SIZE(NTT_REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_Q_DIV2_ODD(MLDSA_Q_DIV2_ODD),
        .MLDSA_N(MLDSA_N),
        .MLDSA_LOGN(MLDSA_LOGN),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
        .MEM_DATA_WIDTH(MEM_DATA_WIDTH),
        .WIDTH(WIDTH)
    ) fv_ntt_top_mlkem_internal_i (.*);
endmodule


bind ntt_top fv_ntt_top_mlkem_top ntt_ctrl_aip_i(
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n), 
    .pi_zeroize (zeroize),
    .pi_mode (mode),
    .pi_ntt_enable (ntt_enable),
    .pi_ntt_mem_base_addr (ntt_mem_base_addr),
    .pi_pwo_mem_base_addr (pwo_mem_base_addr),
    .pi_accumulate (accumulate),
    .pi_sampler_valid (sampler_valid),
    .pi_shuffle_en (shuffle_en),
    .pi_mlkem(mlkem),
    .pi_masking_en (masking_en),
    .pi_random (random),
    .pi_rnd_i (rnd_i),
    .po_mem_wr_req (mem_wr_req),
    .po_mem_rd_req (mem_rd_req),
    .po_mem_wr_data (mem_wr_data),
    .pi_mem_rd_data (mem_rd_data),
    .po_pwm_a_rd_req (pwm_a_rd_req),
    .po_pwm_b_rd_req (pwm_b_rd_req),
    .pi_pwm_a_rd_data (pwm_a_rd_data),
    .pi_pwm_b_rd_data (pwm_b_rd_data),
    .po_ntt_busy (ntt_busy),
    .po_ntt_done (ntt_done)
    //$#//
);