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


module fv_sigencode_z_top_constraints
    import abr_params_pkg::*;
    import sigencode_z_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = MLDSA_MEM_ADDR_WIDTH,
    parameter REG_SIZE       = 24,
    parameter GAMMA1         = 19
) (
    //#$ports
    input                       pi_clk,
    input                       pi_reset_n,
    input                       pi_zeroize,
    input [MEM_ADDR_WIDTH-1:0]  pi_src_base_addr,
    input mem_if_t              po_mem_a_rd_req,
    input mem_if_t              po_mem_b_rd_req,
    input [3:0][REG_SIZE-1:0]   pi_mem_a_rd_data,
    input [3:0][REG_SIZE-1:0]   pi_mem_b_rd_data,
    input [MEM_ADDR_WIDTH-1:0]  pi_sigmem_dest_base_addr,
    input sig_mem_if_t          po_sigmem_a_wr_req,
    input sig_mem_if_t          po_sigmem_b_wr_req,
    input logic [3:0][GAMMA1:0] po_sigmem_a_wr_data,
    input logic [3:0][GAMMA1:0] po_sigmem_b_wr_data,
    input                       pi_sigencode_z_enable,
    input logic                 po_sigencode_z_done
    //$#//
);

    //#$localparams
    localparam THE_LAST_ADDR = ((MLDSA_N)/4)-1;
    localparam IDLE = 3'b000;
    localparam READ = 3'b001;
    localparam READ_and_EXEC = 3'b010;
    localparam READ_EXEC_and_WRITE = 3'b011;
    localparam EXEC_and_WRITE = 3'b100;
    localparam WRITE = 3'b101;
    localparam DONE = 3'b110;
    //$#//

    default clocking default_clk @(posedge pi_clk); endclocking

    logic fv_ongoing_computation;
    always_ff @(posedge pi_clk) begin
        if(!pi_reset_n) begin
            fv_ongoing_computation <= 1'b0;
        end else if(!fv_ongoing_computation || po_sigencode_z_done) begin
            fv_ongoing_computation <= pi_sigencode_z_enable;
        end
    end

    // Set enable only when it is not busy
    assume_only_enable_when_idle : assume property (
        pi_sigencode_z_enable
    |->
        !fv_ongoing_computation || po_sigencode_z_done
    );

endmodule

bind sigencode_z_top fv_sigencode_z_top_constraints #(
    .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH),
    .REG_SIZE(REG_SIZE),
    .GAMMA1(GAMMA1)
 ) fv_sigencode_z_constraints_i (    
    //#$bind
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_src_base_addr (src_base_addr),
    .po_mem_a_rd_req (mem_a_rd_req),
    .po_mem_b_rd_req (mem_b_rd_req),
    .pi_mem_a_rd_data (mem_a_rd_data),
    .pi_mem_b_rd_data (mem_b_rd_data),
    .pi_sigmem_dest_base_addr (sigmem_dest_base_addr),
    .po_sigmem_a_wr_req (sigmem_a_wr_req),
    .po_sigmem_b_wr_req (sigmem_b_wr_req),
    .po_sigmem_a_wr_data (sigmem_a_wr_data),
    .po_sigmem_b_wr_data (sigmem_b_wr_data),
    .pi_sigencode_z_enable (sigencode_z_enable),
    .po_sigencode_z_done (sigencode_z_done)
    //$#//
);