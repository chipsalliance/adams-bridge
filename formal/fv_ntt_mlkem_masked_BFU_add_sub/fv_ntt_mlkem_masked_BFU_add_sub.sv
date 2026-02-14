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


module fv_ntt_mlkem_masked_BFU_add_sub
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH      = 24,
    parameter HALF_WIDTH = WIDTH/2
    //#$localparams
    //$#//
) (
    //#$ports
    input                        pi_clk,
    input                        pi_reset_n,
    input                        pi_zeroize,
    input                        pi_sub,
    input [1:0][WIDTH-1:0]       pi_u,
    input [1:0][WIDTH-1:0]       pi_v,
    input [3:0][13:0]            pi_rnd,
    input [WIDTH-1:0]            pi_rnd_24bit,
    input logic [1:0][WIDTH-1:0] po_res
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking


sequence reset_sequence;
  !pi_reset_n ##1 pi_reset_n;
endsequence

property run_reset_p;
  $past(!pi_reset_n || pi_zeroize) |->
  po_res == 0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the output of module in sub mode (sub == 1)
property run_sub_p;
  pi_sub
|->
  ##MLKEM_MASKED_ADD_SUB_LATENCY
  WIDTH'(po_res[0] + po_res[1]) == ($past(pi_u[0] + pi_u[1], MLKEM_MASKED_ADD_SUB_LATENCY) >= $past(pi_v[0] + pi_v[1], MLKEM_MASKED_ADD_SUB_LATENCY)) ? 
      $past((pi_u[0] + pi_u[1] - pi_v[0] - pi_v[1]) , MLKEM_MASKED_ADD_SUB_LATENCY) : $past((pi_u[0] + pi_u[1] - pi_v[0] - pi_v[1]) + MLKEM_Q, MLKEM_MASKED_ADD_SUB_LATENCY);
endproperty
run_sub_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_sub_p);


//Property to check the output of module in add mode (sub == 0)
property run_add_p;
  !pi_sub
|->
  ##MLKEM_MASKED_ADD_SUB_LATENCY
  WIDTH'(po_res[0] + po_res[1])  == $past((pi_u[0] + pi_u[1] + pi_v[0] + pi_v[1]) % MLKEM_Q, MLKEM_MASKED_ADD_SUB_LATENCY);
endproperty
run_add_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_add_p);

endmodule

