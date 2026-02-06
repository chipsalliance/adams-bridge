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


module fv_ntt_mlkem_masked_gs_butterfly
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH = 24,
    parameter MLKEM_MASKED_GS_BFU_LATENCY = 15
    //#$localparams
    //$#//
) (
    //#$ports
    input                        pi_clk,
    input                        pi_reset_n,
    input                        pi_zeroize,
    input [1:0][WIDTH-1:0]       pi_opu_i,
    input [1:0][WIDTH-1:0]       pi_opv_i,
    input [1:0][WIDTH-1:0]       pi_opw_i,
    input [4:0][13:0]            pi_rnd_i,
    input logic [1:0][WIDTH-1:0] po_u_o,
    input logic [1:0][WIDTH-1:0] po_v_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking


sequence reset_sequence;
  !pi_reset_n ##1 pi_reset_n;
endsequence

property run_reset_p;
  $past(!pi_reset_n) |->
  po_u_o == 0 && po_v_o == 0;
endproperty
run_reset_a: assert property (run_reset_p);

//Property to check the output of ntt_masked_gs_butterfly module output u
property run_gs_butterfly_u_p;
  ##MLKEM_MASKED_GS_BFU_LATENCY
  WIDTH'(po_u_o[0] + po_u_o[1]) == $past(((pi_opu_i[0] + pi_opu_i[1] + pi_opv_i[0] + pi_opv_i[1]) % MLKEM_Q), MLKEM_MASKED_GS_BFU_LATENCY);
endproperty
run_gs_butterfly_u_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_gs_butterfly_u_p);

//Property to check the output of ntt_masked_gs_butterfly module output v
property run_gs_butterfly_v_p;
  ##MLKEM_MASKED_GS_BFU_LATENCY
  WIDTH'(po_v_o[0] + po_v_o[1]) == ($past((pi_opu_i[0] + pi_opu_i[1]) >= (pi_opv_i[0] + pi_opv_i[1]), MLKEM_MASKED_GS_BFU_LATENCY) ?
    $past((((pi_opu_i[0] + pi_opu_i[1] - pi_opv_i[0] - pi_opv_i[1]) * (pi_opw_i[0] + pi_opw_i[1])) % MLKEM_Q), MLKEM_MASKED_GS_BFU_LATENCY) :
    $past((((pi_opu_i[0] + pi_opu_i[1] - pi_opv_i[0] - pi_opv_i[1] + MLKEM_Q) * (pi_opw_i[0] + pi_opw_i[1])) % MLKEM_Q), MLKEM_MASKED_GS_BFU_LATENCY));

endproperty
run_gs_butterfly_v_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_gs_butterfly_v_p);



endmodule

