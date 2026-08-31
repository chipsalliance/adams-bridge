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
//#$includes

//$#//

module fv_rej_sampler_constraints
    //#$imports
    import abr_params_pkg::*;
    //$#//
#(
    parameter REJ_NUM_SAMPLERS     = 5,
    parameter REJ_SAMPLE_W         = 24,
    parameter REJ_VLD_SAMPLES      = 4,
    parameter REJ_VLD_SAMPLES_W    = 24,
    parameter REJ_VALUE            = 8380417,
    parameter OPT_REJ_BUFFER_DEPTH = 0,
    parameter REJ_BUFFER_W         = $clog2(REJ_VALUE)
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                                              pi_clk,
    input logic                                              pi_rst_b,
    input logic                                              pi_zeroize,
    input logic                                              pi_data_valid_i,
    input logic                                              po_data_hold_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0]     pi_data_i,
    input logic                                              po_data_valid_o,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0] po_data_o
    //$#//
);

    //#$instances
    //$#/
default clocking default_clk @(posedge pi_clk); endclocking
// assume that the input data is stable when data_valid is high
property stable_data_valid;
    pi_data_valid_i && po_data_hold_o 
|=> 
    $stable(pi_data_i) && $stable(pi_data_valid_i);
endproperty
assume_stable_data_valid: assume property(disable iff (!pi_rst_b) stable_data_valid);
endmodule

