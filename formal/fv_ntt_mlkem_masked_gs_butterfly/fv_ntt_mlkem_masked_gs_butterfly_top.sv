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


module fv_ntt_mlkem_masked_gs_butterfly_top
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH = 24
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

    fv_ntt_mlkem_masked_gs_butterfly_constraints #(
        .WIDTH(WIDTH)
    ) fv_ntt_mlkem_masked_gs_butterfly_constraints_i (.*);
    
    fv_ntt_mlkem_masked_gs_butterfly #(
        .WIDTH(WIDTH)
    ) fv_ntt_mlkem_masked_gs_butterfly_i (.*);
    
endmodule


bind ntt_mlkem_masked_gs_butterfly fv_ntt_mlkem_masked_gs_butterfly_top #(
    //#$bind
    .WIDTH (WIDTH)
) fv_ntt_mlkem_masked_gs_butterfly_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_opu_i (opu_i),
    .pi_opv_i (opv_i),
    .pi_opw_i (opw_i),
    .pi_rnd_i (rnd_i),
    .po_u_o (u_o),
    .po_v_o (v_o)
    //$#//
);