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


module fv_sample_in_ball_ctrl_top
    import abr_params_pkg::*;
    import sib_pkg::*;
#(
    parameter SIB_NUM_SAMPLERS = 4,
    parameter SIB_SAMPLE_W     = 8,
    parameter SIB_TAU          = 60,
    parameter SIB_NUM_COEFF    = 256,
    //#$localparams
    localparam MLDSA_Q_WIDTH     = $clog2(8380417)
    //$#//
) (
    //#$ports
    input logic                                          pi_clk,
    input logic                                          pi_rst_b,
    input logic                                          pi_zeroize,
    input logic                                          pi_data_valid_i,
    input logic                                          po_data_hold_o,
    input logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] pi_data_i,
    input logic                                          po_sib_done_o,
    input logic [1:0]                                    po_cs_o,
    input logic [1:0]                                    po_we_o,
    input logic [1:0][7:2]                               po_addr_o,
    input logic [1:0][3:0][MLDSA_Q_WIDTH-1:0]            po_wrdata_o,
    input logic [1:0][3:0][MLDSA_Q_WIDTH-1:0]            pi_rddata_i
    //$#//
);

    fv_sample_in_ball_ctrl_constraints #(
        .SIB_NUM_SAMPLERS(SIB_NUM_SAMPLERS),
        .SIB_SAMPLE_W(SIB_SAMPLE_W),
        .SIB_TAU(SIB_TAU),
        .SIB_NUM_COEFF(SIB_NUM_COEFF)
    ) fv_constraints_i (.*);
    
endmodule


bind sample_in_ball_ctrl fv_sample_in_ball_ctrl_top fv_sample_in_ball_ctrl_i(
    //#$bind
    .pi_clk (clk),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_data_valid_i (data_valid_i),
    .po_data_hold_o (data_hold_o),
    .pi_data_i (data_i),
    .po_sib_done_o (sib_done_o),
    .po_cs_o (cs_o),
    .po_we_o (we_o),
    .po_addr_o (addr_o),
    .po_wrdata_o (wrdata_o),
    .pi_rddata_i (rddata_i)
    //$#//
);