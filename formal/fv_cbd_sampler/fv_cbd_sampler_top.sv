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


module fv_cbd_sampler_top
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
//////// INSTANCES //////////
/////////////////////////////
    fv_cbd_sampler_constraints #(
    ) fv_cbd_sampler_constraints_i (.*);
/////// DEFAULT CLOCK ///////
//////////////////////////// 
default clocking default_clk @(posedge pi_clk); endclocking
logic reset;
assign reset = !pi_rst_b || pi_zeroize;
////// FV VARIABLES //////
//////////////////////////

logic [$clog2(CBD_NUM_SAMPLERS)-1:0] fv_random_sample_data_i ;
logic [CBD_VLD_SAMPLES_W-1:0] fv_sampled_data;
logic [$clog2(2*CBD_SAMPLE_W)-1:0] fv_cbd_data;
logic  signed [$clog2(2*CBD_SAMPLE_W)-1:0] fv_cbd_data_signed;
// function to compute CBD for 4 bits
function bit signed [$clog2(2*CBD_SAMPLE_W)-1:0] cbd( logic [CBD_SAMPLE_W-1:0] data);
    logic [MLKEM_ETA-1:0] b,c;
    b = $countones(data[MLKEM_ETA-1:0]);                                // number of 1 in lower half
    c = $countones(data[2*MLKEM_ETA-1:MLKEM_ETA]);                      // number of 1 in upper half
    return b - c;                                                       // return the difference
endfunction

//function for computing modulo mux
function logic [CBD_VLD_SAMPLES_W-1:0] mod_mux(bit signed [$clog2(2*CBD_SAMPLE_W)-1:0] sampled_data);
    logic [CBD_VLD_SAMPLES_W-1:0] output_data;
    unique case (sampled_data)
        3'd0 : output_data = 0;
        3'd1 : output_data = 1;
        3'd2 : output_data = 2;
        3'd6 : output_data = MLKEM_Q - 2;                               // assuming MLKEM_Q holds Q e
        3'd7 : output_data = MLKEM_Q - 1;                               // assuming MLKEM_Q holds Q
        default: output_data = 12'hDED;                                 // to ensure that we are not hitting default case
    endcase
    return output_data; 
endfunction

////// AUX LOGIC /////
//////////////////////
assign fv_sampled_data  = mod_mux(cbd(pi_data_i[fv_random_sample_data_i]));
assign fv_cbd_data_signed = cbd(pi_data_i[fv_random_sample_data_i]);

/// ASSUMPTIONS ///
//////////////////
// create assumption for symbolic index 
property stable_random_sample_index;
    disable iff (pi_zeroize)
    ##1 $stable(fv_random_sample_data_i)
;endproperty
symbolic_random_index_id: assume property(stable_random_sample_index);

////// PROPERTIES /////
///////////////////////
property reset_property;
    pi_zeroize 
|->
    !po_data_valid_o 
;endproperty
check_reset: assert property(reset_property);

// check valid output
property correct_output;
    pi_data_valid_i
|-> 
    po_data_o[fv_random_sample_data_i] ==  fv_sampled_data
;endproperty
check_if_the_result_is_correct : assert property(correct_output);


// when input data stable then output should not change.
property data_o_stable_if_valid_is;
    pi_data_valid_i ##1 pi_data_valid_i && $stable(pi_data_i)
|->
    $stable(po_data_o)
;endproperty
check_the_data_doesnt_change_if_data_valid_o_is_stable : assert property(data_o_stable_if_valid_is);


// Data out should be valid when data in is valid and no zeroize
property data_out_valid_when_data_in_valid;
    disable iff(pi_zeroize)
    po_data_valid_o  == pi_data_valid_i
;endproperty
check_data_in_valid_implies_data_out_valid: assert property (data_out_valid_when_data_in_valid);

// hold is always 0
property hold_is_always_zero;
    !po_data_hold_o
;endproperty
check_hold_is_always_zero: assert property (hold_is_always_zero);

endmodule

////// BIND ///////
///////////////////
bind cbd_sampler_ctrl fv_cbd_sampler_top #(
    //#$bind
) fv_cbd_sampler_top_i (
    .pi_clk (clk),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_data_valid_i (data_valid_i),
    .po_data_hold_o (data_hold_o),
    .pi_data_i (data_i),
    .po_data_valid_o (data_valid_o),
    .po_data_o (data_o)
    //$#//
);
