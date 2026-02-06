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

module fv_ntt_ctrl_masked_gs_top
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

    fv_ntt_ctrl_masked_gs_constraints #(
        .REG_SIZE(REG_SIZE),
        .RADIX(RADIX),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_Q_DIV2_ODD(MLDSA_Q_DIV2_ODD),
        .MLDSA_N(MLDSA_N),
        .MLDSA_LOGN(MLDSA_LOGN),
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH)
    ) fv_ntt_ctrl_masked_gs_constraints_i (.*);

    
endmodule


bind ntt_ctrl fv_ntt_ctrl_masked_gs_top #(
    //#$bind
    .REG_SIZE (REG_SIZE),
    .RADIX (RADIX),
    .MLDSA_Q (MLDSA_Q),
    .MLDSA_Q_DIV2_ODD (MLDSA_Q_DIV2_ODD),
    .MLDSA_N (MLDSA_N),
    .MLDSA_LOGN (MLDSA_LOGN),
    .MEM_ADDR_WIDTH (MEM_ADDR_WIDTH)
) fv_ntt_ctrl_masked_gs_top_i (
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
    .pi_masking_en (masking_en),
    .pi_mlkem (mlkem),
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
    .po_pw_share_mem_rden (pw_share_mem_rden),
    .po_busy (busy),
    .po_done (done),
    .po_ntt_passthrough (ntt_passthrough),
    .po_intt_passthrough (intt_passthrough)
    //$#//
);