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


module fv_makehint_constraints
    import mldsa_params_pkg::*;
    import mldsa_ctrl_pkg::*;
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

    input logic [3:0]                                           fifo_valid_i,
    input logic [3:0][7:0]                                      fifo_data_i,

    input logic                                                 fifo_valid_o,
    input logic [3:0][BUFFER_DATA_W-1:0]                        fifo_data_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

property base_address_constraint; 
  	  ##0 pi_mem_base_addr  == MLDSA_HINT_R_0_BASE
      &&  pi_dest_base_addr == 0;
endproperty
assume_base_address_constraint: assume property(disable iff (!pi_reset_n) base_address_constraint);


endmodule

