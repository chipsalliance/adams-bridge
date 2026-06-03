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


module fv_ntt_hybrid_butterfly_2x2_constraints
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

default clocking default_clk @(posedge pi_clk); endclocking

//Constraint to make accumulate mode signal input stable
property stable_acc;
    $stable(pi_accumulate);
endproperty
assume_stable_acc: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_acc);

//Constraint to make masking enable signal input stable
property stable_mask;
    $stable(pi_masking_en);
endproperty
assume_stable_mask: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_mask);

//Constraint to make mode selection signal input stable
property stable_mode;
    $stable(pi_mode);
endproperty
assume_stable_mode: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_mode);

//Constraint to make mlkem signal input stable
property stable_mlkem;
    $stable(pi_mlkem);
endproperty
assume_stable_mlkem: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_mlkem);

//Constraint to make intt_passthrough signal input stable
property stable_intt_passthrough;
    $stable(pi_intt_passthrough);
endproperty
assume_stable_intt_passthrough: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_intt_passthrough);

//Constraint to make ntt_passthrough signal input stable
property stable_ntt_passthrough;
    $stable(pi_ntt_passthrough);
endproperty
assume_stable_ntt_passthrough: assume property(disable iff (!pi_reset_n | pi_zeroize) stable_ntt_passthrough);

//Constraint to assume pw_uvw_i is zero during reset / zeroize
property pw_uvw_i;
    !pi_reset_n | pi_zeroize
    |->
    ##1 pi_pw_uvw_i == 0;
endproperty
pw_uvw_i_a: assume property(pw_uvw_i);

//Constraint to limit the input value to MLKEM_Q (3329) when in MLKEM mode
property q_mlkem;
    pi_mlkem == 1'd1
    |->
    pi_uvw_i.u00_i < MLKEM_Q &&
    pi_uvw_i.u01_i < MLKEM_Q &&
    pi_uvw_i.v00_i < MLKEM_Q &&
    pi_uvw_i.v01_i < MLKEM_Q &&
    pi_uvw_i.w00_i < MLKEM_Q &&
    pi_uvw_i.w01_i < MLKEM_Q &&
    pi_uvw_i.w10_i < MLKEM_Q &&
    pi_uvw_i.w11_i < MLKEM_Q &&
    pi_pw_uvw_i.u0_i  < MLKEM_Q &&
    pi_pw_uvw_i.v0_i < MLKEM_Q &&
    pi_pw_uvw_i.w0_i < MLKEM_Q &&
    pi_pw_uvw_i.u1_i  < MLKEM_Q &&
    pi_pw_uvw_i.v1_i < MLKEM_Q &&
    pi_pw_uvw_i.w1_i < MLKEM_Q &&
    pi_pw_uvw_i.u2_i  < MLKEM_Q &&
    pi_pw_uvw_i.v2_i < MLKEM_Q &&
    pi_pw_uvw_i.w2_i < MLKEM_Q &&
    pi_pw_uvw_i.u3_i  < MLKEM_Q &&
    pi_pw_uvw_i.v3_i < MLKEM_Q &&
    pi_pw_uvw_i.w3_i < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o < MLKEM_Q &&  //cut output signals also must be constrained now
    ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_uv0_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv0_share[1] < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_uv1_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv1_share[1] < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_uv2_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv2_share[1] < MLKEM_Q &&
    ntt_hybrid_butterfly_2x2.mlkem_uv3_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv3_share[1] < MLKEM_Q &&
    pi_bf_shares_uvw_i.w10_i < MLKEM_Q
    ;
endproperty
assume_q_mlkem: assume property(q_mlkem);

//Constraint to limit the input value to MLDSA_Q ('h7FE001) when in MLDSA mode
property q_mldsa;

    pi_mlkem == 1'd0
    |->
    pi_uvw_i.u00_i < MLDSA_Q &&
    pi_uvw_i.u01_i < MLDSA_Q &&
    pi_uvw_i.v00_i < MLDSA_Q &&
    pi_uvw_i.v01_i < MLDSA_Q &&
    pi_uvw_i.w00_i < MLDSA_Q &&
    pi_uvw_i.w01_i < MLDSA_Q &&
    pi_uvw_i.w10_i < MLDSA_Q &&
    pi_uvw_i.w11_i < MLDSA_Q &&
    pi_pw_uvw_i.u0_i  < MLDSA_Q &&
    pi_pw_uvw_i.v0_i < MLDSA_Q &&
    pi_pw_uvw_i.w0_i < MLDSA_Q &&
    pi_pw_uvw_i.u1_i  < MLDSA_Q &&
    pi_pw_uvw_i.v1_i < MLDSA_Q &&
    pi_pw_uvw_i.w1_i < MLDSA_Q &&
    pi_pw_uvw_i.u2_i  < MLDSA_Q &&
    pi_pw_uvw_i.v2_i < MLDSA_Q &&
    pi_pw_uvw_i.w2_i < MLDSA_Q &&
    pi_pw_uvw_i.u3_i  < MLDSA_Q &&
    pi_pw_uvw_i.v3_i < MLDSA_Q &&
    pi_pw_uvw_i.w3_i < MLDSA_Q &&
    pi_pwm_shares_uvw_i.u0_i[0] + pi_pwm_shares_uvw_i.u0_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.u1_i[0] + pi_pwm_shares_uvw_i.u1_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.u2_i[0] + pi_pwm_shares_uvw_i.u2_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.u3_i[0] + pi_pwm_shares_uvw_i.u3_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.v0_i[0] + pi_pwm_shares_uvw_i.v0_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.v1_i[0] + pi_pwm_shares_uvw_i.v1_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.v2_i[0] + pi_pwm_shares_uvw_i.v2_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.v3_i[0] + pi_pwm_shares_uvw_i.v3_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.w0_i[0] + pi_pwm_shares_uvw_i.w0_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.w1_i[0] + pi_pwm_shares_uvw_i.w1_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.w2_i[0] + pi_pwm_shares_uvw_i.w2_i[1] < MLDSA_Q &&
    pi_pwm_shares_uvw_i.w3_i[0] + pi_pwm_shares_uvw_i.w3_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.u00_i[0] + pi_bf_shares_uvw_i.u00_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.u01_i[0] + pi_bf_shares_uvw_i.u01_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.v00_i[0] + pi_bf_shares_uvw_i.v00_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.v01_i[0] + pi_bf_shares_uvw_i.v01_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.w00_i[0] + pi_bf_shares_uvw_i.w00_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.w01_i[0] + pi_bf_shares_uvw_i.w01_i[1] < MLDSA_Q &&
    pi_bf_shares_uvw_i.w10_i < MLDSA_Q &&
    pi_bf_shares_uvw_i.w11_i < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o < MLDSA_Q &&  //cut output signals also must be constrained now
    ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv0[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv0[1] < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv1[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv1[1] < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[1] < MLDSA_Q &&
    ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[1] < MLDSA_Q
    ;
endproperty
assume_q_mldsa: assume property(q_mldsa);


endmodule

