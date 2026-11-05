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


module fv_ntt_ctrl_gs_mldsa_constraints
  import abr_params_pkg::*;
  import ntt_defines_pkg::*;
  import fv_ntt_ctrl_gs_mldsa_pkg::*;
(
  //#$ports
  input                                pi_clk,
  input                                pi_reset_n,
  input                                pi_zeroize,
  input mode_t                         pi_ntt_mode,
  input                                pi_ntt_enable,
  input                                pi_butterfly_ready,
  input                                pi_buf0_valid,
  input                                pi_sampler_valid,
  input                                pi_accumulate,
  input ntt_mem_addr_t                 pi_ntt_mem_base_addr,
  input pwo_mem_addr_t                 pi_pwo_mem_base_addr,
  input                                pi_shuffle_en,
  input [5:0]                          pi_random,
  input                                pi_mlkem,
  input logic                          pi_mem_rd_data_valid,
  input logic                          po_bf_enable,
  input logic [2:0]                    po_opcode,
  input logic                          po_buf_wren,
  input logic                          po_buf_rden,
  input logic [1:0]                    po_buf_wrptr,
  input logic [1:0]                    po_buf_rdptr,
  input logic [6:0]                    po_twiddle_addr,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_mem_rd_addr,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_mem_wr_addr,
  input logic                          po_mem_rd_en,
  input logic                          po_mem_wr_en,
  input logic                          po_buf_wr_rst_count,
  input logic                          po_buf_rd_rst_count,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_a,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_b,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_c,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] po_pw_mem_wr_addr_c,
  input logic                          po_pw_rden,
  input logic                          po_pw_wren,
  input logic                          po_busy,
  input logic                          po_done
  //$#//
);

  //#$localparams
  // localparam NTT_NUM_ROUNDS = 4;
  // localparam PWO_NUM_ROUNDS = 1;
  // localparam NTT_READ_ADDR_STEP = 16;
  // localparam NTT_WRITE_ADDR_STEP = 1;
  // localparam INTT_READ_ADDR_STEP = 1;
  // localparam INTT_WRITE_ADDR_STEP = 16;
  // localparam PWO_READ_ADDR_STEP = 1;
  // localparam PWO_WRITE_ADDR_STEP = 1;
  // localparam MEM_LAST_ADDR = 63;

  // When testing SRAM_LATENCY != 1, changing SRAM_LATENCY here + script_builder.rb is not enough. model/ntt_ctrl_gs_mldsa.h: bf_enable_reg must be manually resized (using literal sc_uint widths/indices, not SRAM_DELAY expressions) and its .luref refinement updated to match; also update SRAM_LATENCY in additional AIPs file. Regenerate after.
  localparam SRAM_LATENCY = 1;
  //$#//


  default clocking default_clk @(posedge pi_clk); endclocking

  // Constraint to force GS mode
  property gs_mode_only;
    (pi_ntt_mode == gs)
  ;endproperty
  assume_gs_mode_only : assume property (gs_mode_only);

  // Constraint to force ML-DSA
  property gs_mldsa_only;
    pi_mlkem == 0
  ;endproperty
  assume_gs_mldsa_only : assume property (gs_mldsa_only);

  // Aux logic for butterfly latency: response `butterfly_ready` is the requested `bf_enable` delayed by BF_LATENCY cycles
  logic [BF_LATENCY-1:0] fv_butterfly_latency;
  always_ff@(posedge pi_clk, negedge pi_reset_n) begin
    if (!pi_reset_n || pi_zeroize)
    begin
      fv_butterfly_latency <= '0;
    end
    else
    begin
      fv_butterfly_latency <= {po_bf_enable, fv_butterfly_latency} >> 1;
    end
  end

  property butterfly_ready_latency;
    pi_butterfly_ready == fv_butterfly_latency[0]
  ;endproperty
  assume_butterfly_ready_latency : assume property(butterfly_ready_latency);

  // Aux logic for ongoing operation
  logic fv_aux_mode;
  always_ff@(posedge pi_clk or negedge pi_reset_n) begin
    if (!pi_reset_n || pi_zeroize)
    begin
      fv_aux_mode <= 1'b0;
    end
    else if (pi_ntt_enable)
    begin
      fv_aux_mode <= 1'b1;
    end
    else if (po_done)
    begin
      fv_aux_mode <= 1'b0;
    end
  end

  // Constraint to have stable `shuffle_en` during operation
  property stable_shuffle_en;
    ##1
    fv_aux_mode
  |->
    $stable(pi_shuffle_en)
  ;endproperty
  assume_stable_shuffle_en : assume property (stable_shuffle_en);

  // Constraint to have stable base address during operation
  property stable_base_address;
    ##1 fv_aux_mode
  |->
    $stable(pi_ntt_mem_base_addr)
  ;endproperty
  assume_stable_base_address : assume property (stable_base_address);

  logic signed [ABR_MEM_ADDR_WIDTH:0] fv_src_addr;
  assign fv_src_addr = pi_ntt_mem_base_addr.src_base_addr;
  logic signed [ABR_MEM_ADDR_WIDTH:0] fv_interim_addr;
  assign fv_interim_addr = pi_ntt_mem_base_addr.interim_base_addr;
  logic signed [ABR_MEM_ADDR_WIDTH:0] fv_dest_addr;
  assign fv_dest_addr = pi_ntt_mem_base_addr.dest_base_addr;

  // Constraint for base addresses
  // Base addresses should be aligned and distant enough so that they don't invade another memory space
  // Furthermore, they should also be distant enough from the upper bound (2**ABR_MEM_ADDR_WIDTH) so that they don't wrap around and mess up the address computation
  property valid_base_address;
    fv_aux_mode
  |->
    (fv_dest_addr == fv_src_addr || fv_dest_addr >= fv_src_addr + 64 || fv_dest_addr <= fv_src_addr - 64) &&
    (fv_interim_addr <= fv_src_addr - 64 || fv_interim_addr >= fv_src_addr + 64) &&
    (fv_interim_addr <= fv_dest_addr - 64 || fv_interim_addr >= fv_dest_addr + 64) &&
    (fv_src_addr <= 2**ABR_MEM_ADDR_WIDTH - 64) &&
    (fv_interim_addr <= 2**ABR_MEM_ADDR_WIDTH - 64) &&
    (fv_dest_addr <= 2**ABR_MEM_ADDR_WIDTH - 64)
  ;endproperty
  assume_valid_base_address : assume property (valid_base_address);

  // Aux logic implementing a mod-4 counter for `buf0_valid` assertion
  // This mimics the logic implemented in `ntt_shuffle_buffer.sv` and ensures that `buf0_valid` is asserted every 4th cycle
  logic [1:0] fv_buf_count;
  logic [1:0] fv_buf_count_reg;
  always_ff@(posedge pi_clk or negedge pi_reset_n) begin
    if (!pi_reset_n || pi_zeroize || po_buf_wr_rst_count) begin
      fv_buf_count <= '0;
      fv_buf_count_reg <= '0;
    end else if (po_buf_wren) begin
      fv_buf_count <= fv_buf_count + 1;
      fv_buf_count_reg <= fv_buf_count;
    end
  end

  property buf0_valid_pulse;
    pi_buf0_valid == (fv_buf_count_reg == 3)
  ;endproperty
  assume_buf0_valid_pulse : assume property (buf0_valid_pulse);

endmodule

bind ntt_ctrl fv_ntt_ctrl_gs_mldsa_constraints constraints_gs_mldsa_inst(
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
    .pi_mem_rd_data_valid (mem_rd_data_valid),
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
