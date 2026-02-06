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


module fv_cbd_sampler_constraints
    import abr_params_pkg::*;
#(
    //#$localparams
    localparam CBD_NUM_SAMPLERS  = COEFF_PER_CLK,
    localparam CBD_SAMPLE_W      = 2*MLKEM_ETA,
    localparam CBD_VLD_SAMPLES   = CBD_NUM_SAMPLERS,
    localparam CBD_VLD_SAMPLES_W = MLKEM_Q_WIDTH
    //$#//
) (
    //#$ports
    input logic                                              pi_clk,
    input logic                                              pi_rst_b,
    input logic                                              pi_zeroize,
    input logic                                              pi_data_valid_i,
    input logic                                              po_data_hold_o,
    input logic [CBD_NUM_SAMPLERS-1:0][CBD_SAMPLE_W-1:0]     pi_data_i,
    input logic                                              po_data_valid_o,
    input logic [CBD_VLD_SAMPLES-1:0][CBD_VLD_SAMPLES_W-1:0] po_data_o
    //$#//
);

// assume that the input data is stable when data_valid is high

// disabling the constraint as data_hold is fixed at 0
default clocking default_clk @(posedge pi_clk); endclocking
property stable_data_valid;
    pi_data_valid_i && po_data_hold_o 
|=> 
    $stable(pi_data_i) && $stable(pi_data_valid_i);
endproperty
//assume_stable_data_valid: assume property(disable iff (!pi_rst_b) stable_data_valid);
endmodule

