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


module fv_pkdecode_constraints
    import abr_params_pkg::*;
#(
    parameter MLDSA_K          = 'h8,
    parameter MLDSA_N          = 'd256,
    parameter REG_SIZE         = 24,
    parameter INPUT_COEFF_SIZE = 10,
    parameter API_ADDR_WIDTH   = 16,
    //#$localparams
    localparam COEFF_WIDTH          = 10,
    localparam SHIFT_LEFT           = 13,
    localparam NUM_COEFFS_PER_CYCLE = 8,
    localparam THE_LAST_ADDR        = (MLDSA_K*MLDSA_N)/8,
    localparam IDLE                 = 3'b000,
    localparam READ                 = 3'b001,
    localparam READ_and_EXEC        = 3'b010,
    localparam READ_and_WRITE       = 3'b011,
    localparam WRITE                = 3'b100,
    localparam DONE                 = 3'b101
    //$#//
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input                            pi_pkdecode_enable,
    input [ABR_MEM_ADDR_WIDTH-1:0]   pi_dest_base_addr,
    input [API_ADDR_WIDTH-1:0]       pi_src_base_addr,
    input [8*INPUT_COEFF_SIZE-1:0]   pi_API_rd_data,
    input logic [API_ADDR_WIDTH-1:0] po_API_rd_address,
    input logic [3:0][REG_SIZE-1:0]  po_mem_a_wr_data,
    input logic [3:0][REG_SIZE-1:0]  po_mem_b_wr_data,
    input mem_if_t                   po_mem_a_wr_req,
    input mem_if_t                   po_mem_b_wr_req,
    input logic                      po_pkdecode_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    //  assume_const_base_address_1: assume property (
        //  ( pi_src_base_addr == 'd0 && pi_dest_base_addr == 'd960 )
    //  );

    assume_const_base_address: assume property (
        $stable(( pi_src_base_addr)) &&  $stable(pi_dest_base_addr )
     );


endmodule
