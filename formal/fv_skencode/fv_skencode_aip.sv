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

module fv_skencode_aip 
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = 15,
    parameter MLDSA_Q        = 23'd8380417,
    parameter MLDSA_L        = 'h7,
    parameter MLDSA_K        = 'h8,
    parameter MLDSA_N        = 'd256,
    parameter REG_SIZE       = 24,
    parameter AHB_DATA_WIDTH = 32
) (
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input                            pi_skencode_enable,
    input [MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input [MEM_ADDR_WIDTH-1:0]       pi_src_base_addr,
    input [3:0][REG_SIZE-1:0]        pi_mem_a_rd_data,
    input [3:0][REG_SIZE-1:0]        pi_mem_b_rd_data,
    input mem_if_t                   po_keymem_a_wr_req,
    input mem_if_t                   po_mem_a_rd_req,
    input mem_if_t                   po_mem_b_rd_req,
    input logic [AHB_DATA_WIDTH-1:0] po_keymem_a_wr_data,
    input logic                      po_skencode_error,
    input logic                      po_skencode_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking
   
    fv_skencode_constraints fv_skencode_constraints_i(.*);
    

endmodule

// Connect this verification module with the DUV
bind skencode fv_skencode_aip skencode_aip_i(
    .pi_clk (clk),
    .pi_reset_n (reset_n && !zeroize),
    .pi_skencode_enable (skencode_enable),
    .po_skencode_done (skencode_done)
);
