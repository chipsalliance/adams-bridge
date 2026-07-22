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


module fv_rej_bounded_ctrl_constraints
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


assume_hold_data_stable: assume property (pi_data_valid_i && po_data_hold_o |=> $stable(pi_data_i) && $stable(pi_data_valid_i));



endmodule