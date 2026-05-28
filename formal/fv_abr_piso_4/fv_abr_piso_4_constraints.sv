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


module fv_abr_piso_4_constraints
#(
    parameter PISO_BUFFER_W        = 1344,
    parameter PISO_PTR_W           = $clog2(PISO_BUFFER_W),
    parameter PISO_INPUT_RATE0     = 1088,
    parameter PISO_INPUT_RATE1     = 1088,
    parameter PISO_INPUT_RATE2     = 1088,
    parameter PISO_INPUT_RATE3     = 1088,
    parameter PISO_OUTPUT_RATE0    = 80,
    parameter PISO_OUTPUT_RATE1    = 80,
    parameter PISO_OUTPUT_RATE2    = 80,
    parameter PISO_OUTPUT_RATE3    = 80,
    parameter PISO_ACT_INPUT_RATE  = 1088,
    parameter PISO_ACT_OUTPUT_RATE = 80,
    parameter BUFFER_W_DELTA       = PISO_BUFFER_W-PISO_ACT_INPUT_RATE
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                            pi_clk,
    input logic                            pi_rst_b,
    input logic                            pi_zeroize,
    input logic [1:0]                      pi_mode,
    input logic                            pi_valid_i,
    input logic                            po_hold_o,
    input logic [PISO_ACT_INPUT_RATE-1:0]  pi_data_i,
    input logic                            po_valid_o,
    input logic                            pi_hold_i,
    input logic [PISO_ACT_OUTPUT_RATE-1:0] po_data_o
    //$#//
);

    assume_stable_mode  : assume property(##1 $stable(pi_mode));

endmodule

