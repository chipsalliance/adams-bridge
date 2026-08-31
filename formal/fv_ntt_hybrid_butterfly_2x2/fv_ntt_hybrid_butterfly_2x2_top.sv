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


module fv_ntt_hybrid_butterfly_2x2_top
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH      = 46,
    parameter HALF_WIDTH = WIDTH/2
    //#$localparams
    //$#//
) (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input mode_t                            pi_mode,
    input                                   pi_enable,
    input                                   pi_masking_en,
    input                                   pi_shuffle_en,
    input                                   pi_mlkem,
    input bf_uvwi_t                         pi_uvw_i,
    input pwo_uvwi_t                        pi_pw_uvw_i,
    input pwm_shares_uvwi_t                 pi_pwm_shares_uvw_i,
    input [4:0][WIDTH-1:0]                  pi_rnd_i,
    input                                   pi_accumulate,
    input masked_intt_uvwi_t                pi_bf_shares_uvw_i,
    input mlkem_pairwm_zeta_t               pi_mlkem_pairwm_zeta13_i,
    input mlkem_masked_pairwm_zeta_shares_t pi_mlkem_shares_pairwm_zeta13_i,
    input                                   pi_ntt_passthrough,
    input                                   pi_intt_passthrough,
    input bf_uvo_t                          po_uv_o,
    input pwo_t                             po_pwo_uv_o,
    input pwm_shares_uvo_t                  po_pwm_shares_uvo,
    input logic                             po_ready_o
    //$#//
);

    fv_ntt_hybrid_butterfly_2x2_constraints #(
        .WIDTH(WIDTH),
        .HALF_WIDTH(HALF_WIDTH)
    ) fv_ntt_hybrid_butterfly_2x2_constraints_i (.*);
    
    fv_ntt_hybrid_butterfly_2x2 #(
        .WIDTH(WIDTH),
        .HALF_WIDTH(HALF_WIDTH)
    ) fv_ntt_hybrid_butterfly_2x2_i (.*);
    
endmodule


bind ntt_hybrid_butterfly_2x2 fv_ntt_hybrid_butterfly_2x2_top #(
    //#$bind
    .WIDTH (WIDTH),
    .HALF_WIDTH (HALF_WIDTH)
) fv_ntt_hybrid_butterfly_2x2_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_mode (mode),
    .pi_enable (enable),
    .pi_masking_en (masking_en),
    .pi_shuffle_en (shuffle_en),
    .pi_mlkem (mlkem),
    .pi_uvw_i (uvw_i),
    .pi_pw_uvw_i (pw_uvw_i),
    .pi_pwm_shares_uvw_i (pwm_shares_uvw_i),
    .pi_rnd_i (rnd_i),
    .pi_accumulate (accumulate),
    .pi_bf_shares_uvw_i (bf_shares_uvw_i),
    .pi_mlkem_pairwm_zeta13_i (mlkem_pairwm_zeta13_i),
    .pi_mlkem_shares_pairwm_zeta13_i (mlkem_shares_pairwm_zeta13_i),
    .pi_ntt_passthrough (ntt_passthrough),
    .pi_intt_passthrough (intt_passthrough),
    .po_uv_o (uv_o),
    .po_pwo_uv_o (pwo_uv_o),
    .po_pwm_shares_uvo (pwm_shares_uvo),
    .po_ready_o (ready_o)
    //$#//
);