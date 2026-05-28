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


module fv_makehint
    import mldsa_params_pkg::*;
#(
    parameter REG_SIZE      = 24,
    parameter MLDSA_Q       = 23'd8380417,
    parameter MLDSA_N       = 256,
    parameter MLDSA_K       = 8,
    parameter OMEGA         = 75,
    parameter BUFFER_DATA_W = 8
    //#$localparams
    //$#//
) (
    //#$ports
    input                                  pi_clk,
    input                                  pi_reset_n,
    input                                  pi_zeroize,
    input                                  pi_makehint_enable,
    input [(4*REG_SIZE)-1:0]               pi_r,
    input [3:0]                            pi_z,
    input [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_mem_base_addr,
    input [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input logic                            po_invalid_h,
    input mem_if_t                         po_mem_rd_req,
    input mem_if_t                         po_z_rd_req,
    input logic                            po_makehint_done,
    input logic                            po_reg_wren,
    input logic [3:0][7:0]                 po_reg_wrdata,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_reg_wr_addr,
    //$#//

    input logic [3:0]                                           fifo_valid_i,
    input logic [3:0][7:0]                                      fifo_data_i,

    input logic                                                 fifo_valid_o,
    input logic [3:0][BUFFER_DATA_W-1:0]                        fifo_data_o,
    input logic                                                 pi_flush_buffer
);

    fv_makehint_constraints #(
        .REG_SIZE(REG_SIZE),
        .MLDSA_Q(MLDSA_Q),
        .MLDSA_N(MLDSA_N),
        .MLDSA_K(MLDSA_K),
        .OMEGA(OMEGA),
        .BUFFER_DATA_W(BUFFER_DATA_W)
    ) fv_constraints_i (.*);

    fv_makehint_scoreboard fv_makehint_scoreboard_i (.*);

endmodule



bind makehint fv_makehint fv_makehint_i(
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_makehint_enable (makehint_enable),
    .pi_r (r),
    .pi_z (z),
    .pi_mem_base_addr (mem_base_addr),
    .pi_dest_base_addr (dest_base_addr),
    .po_invalid_h (invalid_h),
    .po_mem_rd_req (mem_rd_req),
    .po_z_rd_req (z_rd_req),
    .po_makehint_done (makehint_done),
    .po_reg_wren (reg_wren),
    .po_reg_wrdata (reg_wrdata),
    .po_reg_wr_addr (reg_wr_addr),
    //$#//

    .fifo_valid_i(makehint.hint),
    .fifo_data_i(makehint.index),
    .fifo_valid_o(makehint.sample_valid),
    .fifo_data_o(makehint.sample_data),
    .pi_flush_buffer(makehint.flush_buffer)
);