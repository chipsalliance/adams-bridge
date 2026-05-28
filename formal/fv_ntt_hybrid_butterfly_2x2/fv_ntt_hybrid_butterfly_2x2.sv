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


module fv_ntt_hybrid_butterfly_2x2
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

function logic unsigned [22:0] compute_a_min_b(logic unsigned [22:0] a, logic unsigned [22:0] b, logic mlkem);
  logic unsigned [22:0] result;

  result = 23'd0;

  if (a >= b) begin
    result = a - b;
  end else begin
    if (mlkem) begin
      result = (a - b) + MLKEM_Q;
    end else begin
      result = (a - b) + MLDSA_Q;
    end
  end

  return result;
endfunction

function logic unsigned [22:0] div2(logic unsigned [22:0] data);
  logic unsigned [22:0] result; // @ ntt_hybrid_butterfly_2x2.h:74:5

  result = 23'd0;

  if (data[32'd0] != 64'd0) begin
    result = (data >> 32'd1) + unsigned'(23'((32'(MLDSA_Q) + 32'd1) / 32'd2));
  end else begin
    result = data >> 32'd1;
  end

  return result;
endfunction

function logic unsigned [22:0] div2_mlkem(logic unsigned [22:0] data);
  logic unsigned [22:0] result;
  result = 23'd0;

  if (data[0] != 'd0) begin
    result = ((data >> 'd1) + ((MLKEM_Q + 'd1) / 'd2));
  end else begin
    result = data >> 'd1;
  end

  return result;
endfunction

function logic unsigned [22:0] compute_u_CT(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  return 23'((u + 23'((v * w) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
endfunction

function logic unsigned [22:0] compute_u_CT_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  return 23'((u + 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q)) % MLKEM_Q);
endfunction

function logic unsigned [22:0] compute_v_CT(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; 

  result = 23'((v * w) % 64'(MLDSA_Q));
  return compute_a_min_b(u, result, 1'b0);
endfunction

function logic unsigned [22:0] compute_v_CT_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; 

  result = 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q);
  return compute_a_min_b(u, result, 1'b1);
endfunction

function logic unsigned [22:0] compute_u_GS(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; // @ ntt_hybrid_butterfly_2x2.h:117:5

  result = 23'((u + v) % 64'(MLDSA_Q));
  return 23'(div2(result) % 64'(MLDSA_Q));
endfunction

function logic unsigned [22:0] compute_u_GS_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; // @ ntt_hybrid_butterfly_2x2.h:117:5

  result = 23'((u + v) % MLKEM_Q);
  return 23'(div2_mlkem(result) % MLKEM_Q);
endfunction


function logic unsigned [22:0] compute_v_GS(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; // @ ntt_hybrid_butterfly_2x2.h:123:5

  result = compute_a_min_b(u, v, 1'b0);
  return 23'((div2(result) * w) % 64'(MLDSA_Q));
endfunction

function logic unsigned [22:0] compute_v_GS_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] result; // @ ntt_hybrid_butterfly_2x2.h:123:5

  result = compute_a_min_b(u, v, 1'b1);
  return 23'(((2*MLKEM_REG_SIZE)'(div2_mlkem(result) * w)) % MLKEM_Q);
endfunction


function logic unsigned [22:0] compute_PWM(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [0:0] acc);
  if (acc != 64'd0) begin
    return 23'((w + 23'((u * v) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
  end else begin
    return 23'((u * v) % 64'(MLDSA_Q));
  end
endfunction


function logic unsigned [22:0] compute_PWA(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return 23'((u + v) % 64'(MLDSA_Q));
endfunction

function logic unsigned [22:0] compute_PWA_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return 23'((u + v) % MLKEM_Q);
endfunction


function logic unsigned [22:0] compute_PWS(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return compute_a_min_b(u, v, 1'b0);
endfunction

function logic unsigned [22:0] compute_PWS_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return compute_a_min_b(u, v, 1'b1);
endfunction


logic unsigned [22:0] compute_u_CT_0_i;
assign compute_u_CT_0_i = compute_u_CT(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_u_CT_0_intt_passthrough_i;
assign compute_u_CT_0_intt_passthrough_i = compute_u_CT(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_u_CT_1_i;
assign compute_u_CT_1_i = compute_u_CT(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_u_CT_1_intt_passthrough_i;
assign compute_u_CT_1_intt_passthrough_i = compute_u_CT(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_CT_2_i;
assign compute_u_CT_2_i = compute_u_CT(compute_u_CT_0_i, compute_u_CT_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_u_CT_0_mlkem_i;
assign compute_u_CT_0_mlkem_i = compute_u_CT_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_u_CT_0_mlkem_intt_passthrough_i;
assign compute_u_CT_0_mlkem_intt_passthrough_i = compute_u_CT_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_u_CT_1_mlkem_i;
assign compute_u_CT_1_mlkem_i = compute_u_CT_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_u_CT_1_mlkem_intt_passthrough_i;
assign compute_u_CT_1_mlkem_intt_passthrough_i = compute_u_CT_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_CT_2_mlkem_i;
assign compute_u_CT_2_mlkem_i = compute_u_CT_mlkem(compute_u_CT_0_mlkem_i, compute_u_CT_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_CT_0_i;
assign compute_v_CT_0_i = compute_v_CT(compute_u_CT_0_i, compute_u_CT_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_CT_0_mlkem_i;
assign compute_v_CT_0_mlkem_i = compute_v_CT_mlkem(compute_u_CT_0_mlkem_i, compute_u_CT_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_CT_1_i;
assign compute_v_CT_1_i = compute_v_CT(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_v_CT_1_intt_passthrough_i;
assign compute_v_CT_1_intt_passthrough_i = compute_v_CT(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_v_CT_2_i;
assign compute_v_CT_2_i = compute_v_CT(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_v_CT_2_intt_passthrough_i;
assign compute_v_CT_2_intt_passthrough_i = compute_v_CT(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_CT_3_i;
assign compute_u_CT_3_i = compute_u_CT(compute_v_CT_1_i, compute_v_CT_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_CT_1_mlkem_i;
assign compute_v_CT_1_mlkem_i = compute_v_CT_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_v_CT_1_mlkem_intt_passthrough_i;
assign compute_v_CT_1_mlkem_intt_passthrough_i = compute_v_CT_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_v_CT_2_mlkem_i;
assign compute_v_CT_2_mlkem_i = compute_v_CT_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_v_CT_2_mlkem_intt_passthrough_i;
assign compute_v_CT_2_mlkem_intt_passthrough_i = compute_v_CT_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_CT_3_mlkem_i;
assign compute_u_CT_3_mlkem_i = compute_u_CT_mlkem(compute_v_CT_1_mlkem_i, compute_v_CT_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_CT_3_i;
assign compute_v_CT_3_i = compute_v_CT(compute_v_CT_1_i, compute_v_CT_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_CT_3_mlkem_i;
assign compute_v_CT_3_mlkem_i = compute_v_CT_mlkem(compute_v_CT_1_mlkem_i, compute_v_CT_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_u_GS_0_i;
assign compute_u_GS_0_i = compute_u_GS(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_u_GS_0_intt_passthrough_i;
assign compute_u_GS_0_intt_passthrough_i = compute_u_GS(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_u_GS_1_i;
assign compute_u_GS_1_i = compute_u_GS(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_u_GS_1_intt_passthrough_i;
assign compute_u_GS_1_intt_passthrough_i = compute_u_GS(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_GS_2_i;
assign compute_u_GS_2_i = compute_u_GS(compute_u_GS_0_i, compute_u_GS_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_u_GS_0_mlkem_i;
assign compute_u_GS_0_mlkem_i = compute_u_GS_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_u_GS_0_mlkem_intt_passthrough_i;
assign compute_u_GS_0_mlkem_intt_passthrough_i = compute_u_GS_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_u_GS_1_mlkem_i;
assign compute_u_GS_1_mlkem_i = compute_u_GS_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_u_GS_1_mlkem_intt_passthrough_i;
assign compute_u_GS_1_mlkem_intt_passthrough_i = compute_u_GS_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_GS_2_mlkem_i;
assign compute_u_GS_2_mlkem_i = compute_u_GS_mlkem(compute_u_GS_0_mlkem_i, compute_u_GS_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_GS_0_i;
assign compute_v_GS_0_i = compute_v_GS(compute_u_GS_0_i, compute_u_GS_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_GS_0_mlkem_i;
assign compute_v_GS_0_mlkem_i = compute_v_GS_mlkem(compute_u_GS_0_mlkem_i, compute_u_GS_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] compute_v_GS_1_i;
assign compute_v_GS_1_i = compute_v_GS(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_v_GS_1_intt_passthrough_i;
assign compute_v_GS_1_intt_passthrough_i = compute_v_GS(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_v_GS_2_i;
assign compute_v_GS_2_i = compute_v_GS(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_v_GS_2_intt_passthrough_i;
assign compute_v_GS_2_intt_passthrough_i = compute_v_GS(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_GS_3_i;
assign compute_u_GS_3_i = compute_u_GS(compute_v_GS_1_i, compute_v_GS_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_GS_1_mlkem_i;
assign compute_v_GS_1_mlkem_i = compute_v_GS_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] compute_v_GS_1_mlkem_intt_passthrough_i;
assign compute_v_GS_1_mlkem_intt_passthrough_i = compute_v_GS_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] compute_v_GS_2_mlkem_i;
assign compute_v_GS_2_mlkem_i = compute_v_GS_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] compute_v_GS_2_mlkem_intt_passthrough_i;
assign compute_v_GS_2_mlkem_intt_passthrough_i = compute_v_GS_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] compute_u_GS_3_mlkem_i;
assign compute_u_GS_3_mlkem_i = compute_u_GS_mlkem(compute_v_GS_1_mlkem_i, compute_v_GS_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_GS_3_i;
assign compute_v_GS_3_i = compute_v_GS(compute_v_GS_1_i, compute_v_GS_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_v_GS_3_mlkem_i;
assign compute_v_GS_3_mlkem_i = compute_v_GS_mlkem(compute_v_GS_1_mlkem_i, compute_v_GS_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] compute_PWM_0_i;
assign compute_PWM_0_i = compute_PWM(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i, pi_pw_uvw_i.w2_i, pi_accumulate);

logic unsigned [22:0] compute_PWM_1_i;
assign compute_PWM_1_i = compute_PWM(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i, pi_pw_uvw_i.w3_i, pi_accumulate);

logic unsigned [22:0] compute_PWM_2_i;
assign compute_PWM_2_i = compute_PWM(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i, pi_pw_uvw_i.w0_i, pi_accumulate);

logic unsigned [22:0] compute_PWM_3_i;
assign compute_PWM_3_i = compute_PWM(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i, pi_pw_uvw_i.w1_i, pi_accumulate);

logic unsigned [22:0] compute_PWA_0_i;
assign compute_PWA_0_i = compute_PWA(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] compute_PWA_1_i;
assign compute_PWA_1_i = compute_PWA(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] compute_PWA_2_i;
assign compute_PWA_2_i = compute_PWA(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] compute_PWA_3_i;
assign compute_PWA_3_i = compute_PWA(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] compute_PWA_0_mlkem_i;
assign compute_PWA_0_mlkem_i = compute_PWA_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] compute_PWA_1_mlkem_i;
assign compute_PWA_1_mlkem_i = compute_PWA_mlkem(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] compute_PWA_2_mlkem_i;
assign compute_PWA_2_mlkem_i = compute_PWA_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] compute_PWA_3_mlkem_i;
assign compute_PWA_3_mlkem_i = compute_PWA_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] compute_PWS_0_i;
assign compute_PWS_0_i = compute_PWS(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] compute_PWS_1_i;
assign compute_PWS_1_i = compute_PWS(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] compute_PWS_2_i;
assign compute_PWS_2_i = compute_PWS(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] compute_PWS_3_i;
assign compute_PWS_3_i = compute_PWS(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] compute_PWS_0_mlkem_i;
assign compute_PWS_0_mlkem_i = compute_PWS_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] compute_PWS_1_mlkem_i;
assign compute_PWS_1_mlkem_i = compute_PWS_mlkem(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] compute_PWS_2_mlkem_i;
assign compute_PWS_2_mlkem_i = compute_PWS_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] compute_PWS_3_mlkem_i;
assign compute_PWS_3_mlkem_i = compute_PWS_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

sequence reset_sequence;
  !pi_reset_n ##1 pi_reset_n;
endsequence

//Reset property
property run_reset_p;
  reset_sequence 
  |->
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == 1'd0 &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0 &&
  (po_pwm_shares_uvo.uv0[0] + po_pwm_shares_uvo.uv0[1]) == '0 &&
  (po_pwm_shares_uvo.uv1[0] + po_pwm_shares_uvo.uv1[1]) == '0 &&
  (po_pwm_shares_uvo.uv2[0] + po_pwm_shares_uvo.uv2[1]) == '0 &&
  (po_pwm_shares_uvo.uv3[0] + po_pwm_shares_uvo.uv3[1]) == '0;
endproperty
run_reset_a: assert property (run_reset_p);

//property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode with ntt_passthrough and mlkem (Holds)
property run_CT_ntt_passthrough_mlkem_p;
  (pi_mode == 3'd0) &&
  pi_mlkem &&
  pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  !pi_masking_en
|->
  ##MLKEM_UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == $past(compute_u_CT_0_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  //po_uv_o.u21_o == $past(compute_u_CT_1_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) && //intended bug introduction
  po_uv_o.u21_o == $past(compute_v_CT_1_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  //po_uv_o.v20_o == $past(compute_v_CT_1_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) && //intended bug introduction
  po_uv_o.v20_o == $past(compute_u_CT_1_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_CT_2_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_BF_LATENCY)
  ;
  endproperty
run_CT_ntt_passthrough_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_ntt_passthrough_mlkem_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT unmasked mode (HB witness 11 bound 10)
property run_CT_unmasked_p;
  (pi_mode == 3'd0) &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, UNMASKED_BF_LATENCY) &&
  po_uv_o.u20_o == $past(compute_u_CT_2_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.u21_o == $past(compute_u_CT_3_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.v20_o == $past(compute_v_CT_0_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_CT_3_i, UNMASKED_BF_LATENCY)
  ;
endproperty
run_CT_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_unmasked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT unmasked mlkem mode (HB witness 7 bound 6)
property run_CT_unmasked_mlkem_p;
  (pi_mode == 3'd0) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.u20_o == $past(compute_u_CT_2_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.u21_o == $past(compute_u_CT_3_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v20_o == $past(compute_v_CT_0_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_CT_3_mlkem_i, MLKEM_UNMASKED_BF_LATENCY)
  ;
endproperty
run_CT_unmasked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_unmasked_mlkem_p);

/*
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode with masking_en (with outputs of ntt_masked_bfu1x2 cut) (HB witness 272 bound 271)
//Not applicable in the current design: CT mode is always unmasked.
property run_CT_masked_p;
  (pi_mode == 3'd0) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_BF_LATENCY
  po_ready_o == $past(pi_enable, UNMASKED_BF_LATENCY)
  ##(MASKED_INTT_LATENCY-UNMASKED_BF_LATENCY)
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == compute_u_CT($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, UNMASKED_BF_STAGE1_LATENCY),  //output of ntt_masked_bfu1x2 is cut so only 1 stage BFU delay remains
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) && //taken from primary input so it takes the full masked intt latency (266 + 5)
  po_uv_o.u21_o == compute_u_CT($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) &&
  po_uv_o.v20_o == compute_v_CT($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) &&
  po_uv_o.v21_o == compute_v_CT($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY));
endproperty
run_CT_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_masked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT masked mlkem mode (with outputs of ntt_mlkem_masked_bfu1x2 cut) (HB witness 20 bound 19)
//Not applicable in the current design: CT mode is always unmasked.
property run_CT_masked_mlkem_p;
  (pi_mode == 3'd0) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_BF_LATENCY
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_BF_LATENCY)
  ##(MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY-MLKEM_UNMASKED_BF_LATENCY) //(16+3-6=13)
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == compute_u_CT_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), //output of ntt_mlkem_masked_bfu1x2 is cut so only 1 stage BFU delay remains
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) && //taken from primary input so it takes the full masked intt latency (16 + 3)
  po_uv_o.u21_o == compute_u_CT_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) &&
  po_uv_o.v20_o == compute_v_CT_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) &&
  po_uv_o.v21_o == compute_v_CT_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY)))
  ;
  endproperty
run_CT_masked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_masked_mlkem_p);
*/

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS unmasked mode (HB witness 11 bound 10)
property run_GS_unmasked_p;
  (pi_mode == 3'd1) &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, UNMASKED_BF_LATENCY) &&
  po_uv_o.u20_o == $past(compute_u_GS_2_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.u21_o == $past(compute_u_GS_3_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.v20_o == $past(compute_v_GS_0_i, UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_GS_3_i, UNMASKED_BF_LATENCY);
endproperty
run_GS_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_unmasked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mlkem unmasked mode (HB witness 7 bound 6)
property run_GS_unmasked_mlkem_p;
  (pi_mode == 3'd1) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.u20_o == $past(compute_u_GS_2_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.u21_o == $past(compute_u_GS_3_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v20_o == $past(compute_v_GS_0_mlkem_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_GS_3_mlkem_i, MLKEM_UNMASKED_BF_LATENCY)
  ;
endproperty
run_GS_unmasked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_unmasked_mlkem_p);


//property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mode with intt_passthrough mlkem (HB witness 7 bound 6)
property run_GS_mlkem_intt_passthrough_p;
  (pi_mode == 3'd1) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == $past(compute_u_GS_0_mlkem_intt_passthrough_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.u21_o == $past(compute_u_GS_1_mlkem_intt_passthrough_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v20_o == $past(compute_v_GS_1_mlkem_intt_passthrough_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_uv_o.v21_o == $past(compute_v_GS_2_mlkem_intt_passthrough_i, MLKEM_UNMASKED_BF_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_BF_LATENCY)
  ;
endproperty
run_GS_mlkem_intt_passthrough_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_mlkem_intt_passthrough_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mode (with outputs of ntt_mlkem_masked_bfu1x2 cut) (HB witness 272 bound 271)
property run_GS_masked_p;
  (pi_mode == 3'd1) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MASKED_INTT_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, MASKED_INTT_LATENCY) &&
  po_uv_o.u20_o == compute_u_GS($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, UNMASKED_BF_STAGE1_LATENCY), //output of ntt_masked_bfu1x2 is cut so only 1 stage BFU delay remains
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) &&
  po_uv_o.u21_o == compute_u_GS($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, UNMASKED_BF_STAGE1_LATENCY),
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) &&
  po_uv_o.v20_o == compute_v_GS($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY)) &&
  po_uv_o.v21_o == compute_v_GS($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, UNMASKED_BF_STAGE1_LATENCY), 
                                $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY));
endproperty
run_GS_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_masked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mlkem mode (with outputs of ntt_mlkem_masked_bfu1x2 cut) (HB witness 20 bound 19)
property run_GS_masked_mlkem_p;
  (pi_mode == 3'd1) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_MASKED_INTT_LATENCY
  po_ready_o == $past(pi_enable, MLKEM_MASKED_INTT_LATENCY)
  ##(MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY-MLKEM_MASKED_INTT_LATENCY) //(16+3-17 = 2)
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == compute_u_GS_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), //output of ntt_mlkem_masked_bfu1x2 is cut so only 1 stage BFU delay remains
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) &&
  po_uv_o.u21_o == compute_u_GS_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) &&
  po_uv_o.v20_o == compute_v_GS_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY))) &&
  po_uv_o.v21_o == compute_v_GS_mlkem($past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o, MLKEM_UNMASKED_BF_STAGE1_LATENCY), 
                                      $past(pi_bf_shares_uvw_i.w10_i, (MLKEM_MASKED_BF_STAGE1_LATENCY+MLKEM_UNMASKED_BF_STAGE1_LATENCY)));
endproperty
run_GS_masked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_masked_mlkem_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mlkem mode and intt passthrough (with outputs of ntt_mlkem_masked_bfu1x2 cut)
property run_GS_masked_mlkem_intt_passthrough_p;
  (pi_mode == 3'd1) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  pi_intt_passthrough
|->
  ##MLKEM_MASKED_INTT_LATENCY
  po_ready_o == $past(pi_enable, MLKEM_MASKED_INTT_LATENCY) &&
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o &&
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o &&
  po_uv_o.v21_o == ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o
;endproperty
run_GS_masked_mlkem_intt_passthrough_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_masked_mlkem_intt_passthrough_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM unmasked not accumulate mode (HB witness 5 bound 4)
property run_PWM_unmasked_p;
  (pi_mode == 3'd2) &&
  !pi_accumulate &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##(UNMASKED_PWM_LATENCY-1) //Unmasked PWM not accumulate case, so 1 cycle less than accumulate case
  po_pwo_uv_o.uv0 == $past(compute_PWM_2_i, (UNMASKED_PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv1 == $past(compute_PWM_3_i, (UNMASKED_PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv2 == $past(compute_PWM_0_i, (UNMASKED_PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv3 == $past(compute_PWM_1_i, (UNMASKED_PWM_LATENCY-1)) &&
  po_ready_o == $past(pi_enable, (UNMASKED_PWM_LATENCY-1)) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWM_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_unmasked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM unmasked accumulate mode (HB witness 6 bound 5)
property run_PWMA_unmasked_p;
  (pi_mode == 3'd2) &&
  pi_accumulate &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWM_LATENCY
  po_pwo_uv_o.uv0 == $past(compute_PWM_2_i, UNMASKED_PWM_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(compute_PWM_3_i, UNMASKED_PWM_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(compute_PWM_0_i, UNMASKED_PWM_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWM_1_i, UNMASKED_PWM_LATENCY) &&
  po_ready_o == $past(pi_enable, UNMASKED_PWM_LATENCY) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWMA_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWMA_unmasked_p);
/*
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM unmasked mlkem mode (hold)
//Not applicable in the current design: no PWM mode in mlkem case
property run_PWM_unmasked_mlkem_p;
  (pi_mode == 3'd2) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == 1'd0 &&
  po_uv_o.u20_o == 23'd0 && 
  po_uv_o.u21_o == 23'd0 && 
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWM_unmasked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_unmasked_mlkem_p);
*/
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM masked mode
property run_PWM_masked_p;
  (pi_mode == 3'd2) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  !pi_accumulate
|->
  ##(MASKED_PWM_LATENCY-1) //Masked PWM not accumulate case. Doubt: why MASKED_PWM_LATENCY - 2? (design line 633)
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == $past(compute_PWM(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, 
                                       ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, 
                                       pi_bf_shares_uvw_i.w10_i,
                                       pi_accumulate), (UNMASKED_PWM_LATENCY-1)) && //masked pwm outputs are cut so only one unmasked PWM stage delay remains
  po_pwo_uv_o.uv3 == $past(compute_PWM(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, 
                                       ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, 
                                       pi_bf_shares_uvw_i.w10_i,
                                       pi_accumulate), (UNMASKED_PWM_LATENCY-1)) &&
  po_ready_o == $past(pi_enable, (MASKED_PWM_LATENCY-1)) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0 &&
  (po_pwm_shares_uvo.uv0[0] + po_pwm_shares_uvo.uv0[1]) == (ntt_hybrid_butterfly_2x2.mldsa_uv0_share[0] + ntt_hybrid_butterfly_2x2.mldsa_uv0_share[1]) &&
  (po_pwm_shares_uvo.uv1[0] + po_pwm_shares_uvo.uv1[1]) == (ntt_hybrid_butterfly_2x2.mldsa_uv1_share[0] + ntt_hybrid_butterfly_2x2.mldsa_uv1_share[1]) &&
  (po_pwm_shares_uvo.uv2[0] + po_pwm_shares_uvo.uv2[1]) == (ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[1]) &&
  (po_pwm_shares_uvo.uv3[0] + po_pwm_shares_uvo.uv3[1]) == (ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[1])
  ;
endproperty
run_PWM_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_masked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM masked accumulate mode
property run_PWMA_masked_p;
  (pi_mode == 3'd2) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_accumulate
|->
  ##MASKED_PWM_ACC_LATENCY
  po_ready_o == $past(pi_enable, MASKED_PWM_ACC_LATENCY) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0 &&
  (po_pwm_shares_uvo.uv0[0] + po_pwm_shares_uvo.uv0[1]) == (ntt_hybrid_butterfly_2x2.mldsa_uv0_share[0] + ntt_hybrid_butterfly_2x2.mldsa_uv0_share[1]) &&
  (po_pwm_shares_uvo.uv1[0] + po_pwm_shares_uvo.uv1[1]) == (ntt_hybrid_butterfly_2x2.mldsa_uv1_share[0] + ntt_hybrid_butterfly_2x2.mldsa_uv1_share[1]) &&
  (po_pwm_shares_uvo.uv2[0] + po_pwm_shares_uvo.uv2[1]) == (ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv2[1]) &&
  (po_pwm_shares_uvo.uv3[0] + po_pwm_shares_uvo.uv3[1]) == (ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[0] + ntt_hybrid_butterfly_2x2.bf_pwm_shares_uvo.uv3[1])
  ##(MASKED_INTT_LATENCY-MASKED_PWM_ACC_LATENCY)
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == compute_PWM($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, UNMASKED_PWM_LATENCY), 
                              $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o, UNMASKED_PWM_LATENCY), 
                              $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY), pi_accumulate) &&
  po_pwo_uv_o.uv3 == compute_PWM($past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, UNMASKED_PWM_LATENCY), 
                              $past(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o, UNMASKED_PWM_LATENCY), 
                              $past(pi_bf_shares_uvw_i.w10_i, MASKED_INTT_LATENCY), pi_accumulate)
  ;
endproperty
run_PWMA_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWMA_masked_p);
/*
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM masked mlkem mode (hold)
//Not applicable in the current design: no PWM mode in mlkem case
property run_PWM_masked_mlkem_p;
  (pi_mode == 3'd2) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == 1'd0 &&
  po_uv_o.u20_o == 23'd0 && 
  po_uv_o.u21_o == 23'd0 && 
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWM_masked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_masked_mlkem_p);
*/
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA unmasked mode (hold)
property run_PWA_unmasked_p;
  (pi_mode == 3'd3) &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWA_LATENCY
  po_pwo_uv_o.uv0 == $past(compute_PWA_2_i, UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(compute_PWA_3_i, UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(compute_PWA_0_i, UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWA_1_i, UNMASKED_PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, UNMASKED_PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWA_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_unmasked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA unmasked mlkem mode (hold)
property run_PWA_unmasked_mlkem_p;
  (pi_mode == 3'd3) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_PWA_LATENCY
  po_pwo_uv_o.uv0 == $past(compute_PWA_2_mlkem_i, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(compute_PWA_3_mlkem_i, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(compute_PWA_0_mlkem_i, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWA_1_mlkem_i, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWA_unmasked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_unmasked_mlkem_p);
/*
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA masked mode (hold)
//Not applicable in the current design: PWA mode is always unmasked
property run_PWA_masked_p;
  (pi_mode == 3'd3) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWA_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == $past(compute_PWA(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o), UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWA(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o), UNMASKED_PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, UNMASKED_PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWA_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_masked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA masked mlkem mode (hold)
//Not applicable in the current design: PWA mode is always unmasked
property run_PWA_masked_mlkem_p;
  (pi_mode == 3'd3) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_PWA_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == $past(compute_PWA_mlkem(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o), MLKEM_UNMASKED_PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWA_mlkem(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o), MLKEM_UNMASKED_PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWA_masked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_masked_mlkem_p);
*/

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS unmasked mode (hold)
property run_PWS_unmasked_p;
  (pi_mode == 3'd4) &&
  !pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWS_LATENCY
  po_pwo_uv_o.uv0 == $past(compute_PWS_2_i, UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(compute_PWS_3_i, UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(compute_PWS_0_i, UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWS_1_i, UNMASKED_PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, UNMASKED_PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWS_unmasked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_unmasked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS unmasked mlkem mode (hold)
property run_PWS_unmasked_mlkem_p;
  (pi_mode == 3'd4) &&
  !pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_PWS_LATENCY
  po_pwo_uv_o.uv0 == $past(compute_PWS_2_mlkem_i, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(compute_PWS_3_mlkem_i, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(compute_PWS_0_mlkem_i, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWS_1_mlkem_i, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWS_unmasked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_unmasked_mlkem_p);
/*
//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS masked mode (hold)
//Not applicable in the current design: PWS mode is always unmasked
property run_PWS_masked_p;
  (pi_mode == 3'd4) &&
  pi_masking_en &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWS_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == $past(compute_PWS(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u20_o, ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v20_o), UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWS(ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.u21_o, ntt_hybrid_butterfly_2x2.mldsa_masked_gs_stage1_uvo.v21_o), UNMASKED_PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, UNMASKED_PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWS_masked_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_masked_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS masked mlkem mode (hold)
//Not applicable in the current design: PWS mode is always unmasked
property run_PWS_masked_mlkem_p;
  (pi_mode == 3'd4) &&
  pi_masking_en &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##MLKEM_UNMASKED_PWS_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == $past(compute_PWS_mlkem(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u20_o, ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v20_o), MLKEM_UNMASKED_PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(compute_PWS_mlkem(ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.u21_o, ntt_hybrid_butterfly_2x2.mlkem_masked_gs_stage1_uvo.v21_o), MLKEM_UNMASKED_PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, MLKEM_UNMASKED_PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
run_PWS_masked_mlkem_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_masked_mlkem_p);
*/
//Property to check the outputs of ntt_hybrid_butterfly_2x2 in pairwm mode (with outputs of ntt_karatsuba & ntt_masked_pairwm blocks are cut) (hold)
property run_pairwm_p;
  (pi_mode == 3'd5) &&
  !pi_masking_en &&
  !pi_accumulate &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  po_pwo_uv_o.uv0 == ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv0_o &&
  po_pwo_uv_o.uv1 == ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv1_o &&
  po_pwo_uv_o.uv2 == ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv0_o &&
  po_pwo_uv_o.uv3 == ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv1_o &&
  (po_pwm_shares_uvo.uv0[0] + po_pwm_shares_uvo.uv0[1]) == (ntt_hybrid_butterfly_2x2.mlkem_uv0_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv0_share[1]) &&
  (po_pwm_shares_uvo.uv1[0] + po_pwm_shares_uvo.uv1[1]) == (ntt_hybrid_butterfly_2x2.mlkem_uv1_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv1_share[1]) &&
  (po_pwm_shares_uvo.uv2[0] + po_pwm_shares_uvo.uv2[1]) == (ntt_hybrid_butterfly_2x2.mlkem_uv2_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv2_share[1]) &&
  (po_pwm_shares_uvo.uv3[0] + po_pwm_shares_uvo.uv3[1]) == (ntt_hybrid_butterfly_2x2.mlkem_uv3_share[0] + ntt_hybrid_butterfly_2x2.mlkem_uv3_share[1]) 
  ##(UNMASKED_PWM_LATENCY-1)
  po_ready_o == $past(pi_enable, (UNMASKED_PWM_LATENCY-1)) //because masked pairwm outputs are cut, so only 1 unmasked PWM stage delay remains
  ;
endproperty
run_pairwm_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_p);

//Property to check the ready output of ntt_hybrid_butterfly_2x2 in pairwm mode accumulate mode (hold)
property run_pairwm_accumulate_p;
  (pi_mode == 3'd5) &&
  !pi_masking_en &&
  pi_accumulate &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough
|->
  ##UNMASKED_PWM_LATENCY
  po_ready_o == $past(pi_enable, UNMASKED_PWM_LATENCY);
endproperty
run_pairwm_accumulate_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_accumulate_p);



endmodule

