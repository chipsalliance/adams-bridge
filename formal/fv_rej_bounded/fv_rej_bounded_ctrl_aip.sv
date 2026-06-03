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

module fv_rej_bounded_ctrl_aip 
    import abr_params_pkg::*;
#(
   parameter REJ_NUM_SAMPLERS = 8
  ,parameter REJ_SAMPLE_W     = 4
  ,parameter REJ_VLD_SAMPLES  = 4
  ,parameter REJ_VLD_SAMPLES_W = 24
  ,parameter REJ_VALUE = 15
  ,parameter REJ_BUFFER_W = 3
) (
     ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic                                                     pi_clock,
    input logic                                                     pi_reset_n,
    input logic                                                     pi_data_valid_i,
    input                                                           po_data_hold_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0]            pi_data_i,
    input                                                           po_data_valid_o,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0]        po_data_o,

    input logic [REJ_NUM_SAMPLERS-1:0]                              fifo_valid_i,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_BUFFER_W-1:0]             fifo_data_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_BUFFER_W-1:0]            fifo_data_i,
    input                                                           fifo_valid_o

);


    // AIP Modules
    fv_rej_bounded_ctrl_constraints fv_rej_bounded_ctrl_constraints_i(.*);
    fv_rej_bounded_ctrl_scoreboard fv_rej_bounded_ctrl_scoreboard_i (.*);
 
endmodule

// Connect this verification module with the DUV
bind rej_bounded_ctrl fv_rej_bounded_ctrl_aip rej_bounded_ctrl_aip_i(
    .pi_clock(clk),
    .pi_reset_n(!rst_b || zeroize),
    .pi_data_valid_i(data_valid_i),
    .pi_data_i(data_i),
    .po_data_hold_o(data_hold_o),
    .po_data_valid_o(data_valid_o),
    .po_data_o(data_o),
    .fifo_data_o(rej_bounded_ctrl.rej_buffer),
    .fifo_valid_i(rej_bounded_ctrl.sample_valid),
    .fifo_data_i(rej_bounded_ctrl.buffer_data),
    .fifo_valid_o(rej_bounded_ctrl.rej_buffer_valid)
);


