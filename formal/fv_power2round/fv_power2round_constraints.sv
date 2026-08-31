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


module fv_power2round_constraints
    import abr_params_pkg::*;
    import power2round_defines_pkg::*;
#(
    parameter REG_SIZE       = 24,
    parameter MLDSA_Q        = 23'd8380417,
    parameter MLDSA_N        = 256,
    parameter MLDSA_K        = 8,
    parameter MLDSA_D        = 13,
    parameter AHB_DATA_WIDTH = 32
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input                            pi_enable,
    input [ABR_MEM_ADDR_WIDTH-1:0] pi_src_base_addr,
    input [ABR_MEM_ADDR_WIDTH-1:0] pi_skmem_dest_base_addr,
    input mem_if_t                   po_mem_a_rd_req,
    input mem_if_t                   po_mem_b_rd_req,
    input [(4*REG_SIZE)-1:0]         pi_mem_rd_data_a,
    input [(4*REG_SIZE)-1:0]         pi_mem_rd_data_b,
    input mem_if_t                   po_skmem_a_wr_req,
    input mem_if_t                   po_skmem_b_wr_req,
    input logic [AHB_DATA_WIDTH-1:0] po_skmem_wr_data_a,
    input logic [AHB_DATA_WIDTH-1:0] po_skmem_wr_data_b,
    input logic                      po_pk_t1_wren,
    input logic [7:0][9:0]           po_pk_t1_wrdata,
    input logic [7:0]                po_pk_t1_wr_addr,
    input logic                      po_done
    //$#//
);

    //#$localparams
    localparam T_RD_IDLE = 3'b000;
    localparam READ = 3'b001;
    //$#//

    default clocking default_clk @(posedge pi_clk); endclocking

    logic fv_ongoing_computation;
    always_ff @(posedge pi_clk) begin
        if(!pi_reset_n) begin
            fv_ongoing_computation <= 1'b0;
        end else if(!fv_ongoing_computation || po_done) begin
            fv_ongoing_computation <= pi_enable;
        end
    end

    // Set enable only when it is not busy
    assume_only_enable_when_idle : assume property (
        pi_enable
    |->
        !fv_ongoing_computation || po_done
    );

    assume_const_base_address: assume property (
        ( power2round_top.src_base_addr == 'd960 && power2round_top.skmem_dest_base_addr == 'd0 )
    );

endmodule

bind power2round_top fv_power2round_constraints #(
    .REG_SIZE(REG_SIZE),
    .MLDSA_Q(MLDSA_Q),
    .MLDSA_N(MLDSA_N),
    .MLDSA_K(MLDSA_K),
    .MLDSA_D(MLDSA_D),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
 ) fv_power2round_constraints_i (
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_enable (enable),
    .pi_src_base_addr (src_base_addr),
    .pi_skmem_dest_base_addr (skmem_dest_base_addr),
    .po_mem_a_rd_req (mem_a_rd_req),
    .po_mem_b_rd_req (mem_b_rd_req),
    .pi_mem_rd_data_a (mem_rd_data_a),
    .pi_mem_rd_data_b (mem_rd_data_b),
    .po_skmem_a_wr_req (skmem_a_wr_req),
    .po_skmem_b_wr_req (skmem_b_wr_req),
    .po_skmem_wr_data_a (skmem_wr_data_a),
    .po_skmem_wr_data_b (skmem_wr_data_b),
    .po_pk_t1_wren (pk_t1_wren),
    .po_pk_t1_wrdata (pk_t1_wrdata),
    .po_pk_t1_wr_addr (pk_t1_wr_addr),
    .po_done (done)
    //$#//
);

