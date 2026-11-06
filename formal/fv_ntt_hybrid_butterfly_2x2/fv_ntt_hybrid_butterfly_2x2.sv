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
 (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input mode_t                            pi_mode,
    input                                   pi_enable,
    input                                   pi_shuffle_en,
    input                                   pi_mlkem,
    input bf_uvwi_t                         pi_uvw_i,
    input pwo_uvwi_t                        pi_pw_uvw_i,

    input                                   pi_accumulate,

    input mlkem_pairwm_zeta_t               pi_mlkem_pairwm_zeta13_i,

    input                                   pi_ntt_passthrough,
    input                                   pi_intt_passthrough,
    input bf_uvo_t                          po_uv_o,
    input pwo_t                             po_pwo_uv_o,

    input logic                             po_ready_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

// added for the pwa/pws operations
localparam PWA_LATENCY = 1;
localparam PWS_LATENCY = 1;

function automatic logic unsigned [22:0] compute_a_min_b(logic unsigned [22:0] a, logic unsigned [22:0] b, logic mlkem);
  logic unsigned [22:0] fv_result;

  fv_result = 23'd0;

  if (a >= b) begin
    fv_result = a - b;
  end else begin
    if (mlkem) begin
      fv_result = (a - b) + MLKEM_Q;
    end else begin
      fv_result = (a - b) + MLDSA_Q;
    end
  end

  return fv_result;
endfunction

function automatic logic unsigned [22:0] div2(logic unsigned [22:0] data);
  logic unsigned [22:0] fv_result; // @ ntt_hybrid_butterfly_2x2.h:74:5

  fv_result = 23'd0;

  if (data[32'd0] != 64'd0) begin
    fv_result = (data >> 32'd1) + unsigned'(23'((32'(MLDSA_Q) + 32'd1) / 32'd2));
  end else begin
    fv_result = data >> 32'd1;
  end

  return fv_result;
endfunction

function automatic logic unsigned [22:0] div2_mlkem(logic unsigned [22:0] data);
  logic unsigned [22:0] fv_result;
  fv_result = 23'd0;

  if (data[0] != 'd0) begin
    fv_result = ((data >> 'd1) + ((MLKEM_Q + 'd1) / 'd2));
  end else begin
    fv_result = data >> 'd1;
  end

  return fv_result;
endfunction

function automatic logic unsigned [22:0] compute_u_ct(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  return 23'((u + 23'((v * w) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_u_ct_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  return 23'((u + 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q)) % MLKEM_Q);
endfunction

function automatic logic unsigned [22:0] compute_v_ct(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result;

  fv_result = 23'((v * w) % 64'(MLDSA_Q));
  return compute_a_min_b(u, fv_result, 1'b0);
endfunction

function automatic logic unsigned [22:0] compute_v_ct_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result;

  fv_result = 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q);
  return compute_a_min_b(u, fv_result, 1'b1);
endfunction

function automatic logic unsigned [22:0] compute_u_gs(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result; // @ ntt_hybrid_butterfly_2x2.h:117:5

  fv_result = 23'((u + v) % 64'(MLDSA_Q));
  return 23'(div2(fv_result) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_u_gs_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result; // @ ntt_hybrid_butterfly_2x2.h:117:5

  fv_result = 23'((u + v) % MLKEM_Q);
  return 23'(div2_mlkem(fv_result) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_v_gs(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result; // @ ntt_hybrid_butterfly_2x2.h:123:5

  fv_result = compute_a_min_b(u, v, 1'b0);
  return 23'((div2(fv_result) * w) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_v_gs_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w);
  logic unsigned [22:0] fv_result; // @ ntt_hybrid_butterfly_2x2.h:123:5

  fv_result = compute_a_min_b(u, v, 1'b1);
  return 23'(((2*MLKEM_REG_SIZE)'(div2_mlkem(fv_result) * w)) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_pwm(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [0:0] acc);
  if (acc != 64'd0) begin
    return 23'((w + 23'((u * v) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
  end else begin
    return 23'((u * v) % 64'(MLDSA_Q));
  end
endfunction


function automatic logic unsigned [22:0] compute_pwa(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return 23'((u + v) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_pwa_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return 23'((u + v) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_pws(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return compute_a_min_b(u, v, 1'b0);
endfunction

function automatic logic unsigned [22:0] compute_pws_mlkem(logic unsigned [22:0] u, logic unsigned [22:0] v);
  return compute_a_min_b(u, v, 1'b1);
endfunction

// PAIRWM-002: modular multiply helper for an independent Karatsuba pairwm
// reference model (mirrors fv_ntt_butterfly2x2.sv's compute_pairwm_mult_mlkem).
function automatic logic unsigned [22:0] compute_pairwm_mult_mlkem(logic unsigned [22:0] a, logic unsigned [22:0] b);
  return 23'((2*MLKEM_REG_SIZE)'(a * b) % MLKEM_Q);
endfunction

///////////////////////////////////////
logic unsigned [22:0] fv_compute_u_ct_0_i;
assign fv_compute_u_ct_0_i = compute_u_ct(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

//logic unsigned [22:0] compute_u_CT_0_intt_passthrough_i;
//assign compute_u_CT_0_intt_passthrough_i = compute_u_ct(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_1_i;
assign fv_compute_u_ct_1_i = compute_u_ct(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

//logic unsigned [22:0] compute_u_CT_1_intt_passthrough_i;
//assign compute_u_CT_1_intt_passthrough_i = compute_u_ct(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_2_i;
assign fv_compute_u_ct_2_i = compute_u_ct(fv_compute_u_ct_0_i, fv_compute_u_ct_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_u_ct_0_mlkem_i;
assign fv_compute_u_ct_0_mlkem_i = compute_u_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_u_ct_0_mlkem_intt_passthrough_i;
assign fv_compute_u_ct_0_mlkem_intt_passthrough_i = compute_u_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_1_mlkem_i;
assign fv_compute_u_ct_1_mlkem_i = compute_u_ct_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_ct_1_mlkem_intt_passthrough_i;
assign fv_compute_u_ct_1_mlkem_intt_passthrough_i = compute_u_ct_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_2_mlkem_i;
assign fv_compute_u_ct_2_mlkem_i = compute_u_ct_mlkem(fv_compute_u_ct_0_mlkem_i, fv_compute_u_ct_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_0_i;
assign fv_compute_v_ct_0_i = compute_v_ct(fv_compute_u_ct_0_i, fv_compute_u_ct_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_0_mlkem_i;
assign fv_compute_v_ct_0_mlkem_i = compute_v_ct_mlkem(fv_compute_u_ct_0_mlkem_i, fv_compute_u_ct_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_1_i;
assign fv_compute_v_ct_1_i = compute_v_ct(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

//logic unsigned [22:0] compute_v_CT_1_intt_passthrough_i;
//assign compute_v_CT_1_intt_passthrough_i = compute_v_ct(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_ct_2_i;
assign fv_compute_v_ct_2_i = compute_v_ct(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

//logic unsigned [22:0] compute_v_CT_2_intt_passthrough_i;
//assign compute_v_CT_2_intt_passthrough_i = compute_v_ct(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_3_i;
assign fv_compute_u_ct_3_i = compute_u_ct(fv_compute_v_ct_1_i, fv_compute_v_ct_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_1_mlkem_i;
assign fv_compute_v_ct_1_mlkem_i = compute_v_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

//logic unsigned [22:0] compute_v_CT_1_mlkem_intt_passthrough_i;
//assign compute_v_CT_1_mlkem_intt_passthrough_i = compute_v_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_ct_2_mlkem_i;
assign fv_compute_v_ct_2_mlkem_i = compute_v_ct_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

//logic unsigned [22:0] compute_v_CT_2_mlkem_intt_passthrough_i;
//assign compute_v_CT_2_mlkem_intt_passthrough_i = compute_v_ct_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_3_mlkem_i;
assign fv_compute_u_ct_3_mlkem_i = compute_u_ct_mlkem(fv_compute_v_ct_1_mlkem_i, fv_compute_v_ct_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_3_i;
assign fv_compute_v_ct_3_i = compute_v_ct(fv_compute_v_ct_1_i, fv_compute_v_ct_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_3_mlkem_i;
assign fv_compute_v_ct_3_mlkem_i = compute_v_ct_mlkem(fv_compute_v_ct_1_mlkem_i, fv_compute_v_ct_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_u_gs_0_i;
assign fv_compute_u_gs_0_i = compute_u_gs(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

//logic unsigned [22:0] compute_u_GS_0_intt_passthrough_i;
//assign compute_u_GS_0_intt_passthrough_i = compute_u_gs(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_1_i;
assign fv_compute_u_gs_1_i = compute_u_gs(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

//logic unsigned [22:0] compute_u_GS_1_intt_passthrough_i;
//assign compute_u_GS_1_intt_passthrough_i = compute_u_gs(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_2_i;
assign fv_compute_u_gs_2_i = compute_u_gs(fv_compute_u_gs_0_i, fv_compute_u_gs_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_u_gs_0_mlkem_i;
assign fv_compute_u_gs_0_mlkem_i = compute_u_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_u_gs_0_mlkem_intt_passthrough_i;
assign fv_compute_u_gs_0_mlkem_intt_passthrough_i = compute_u_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_1_mlkem_i;
assign fv_compute_u_gs_1_mlkem_i = compute_u_gs_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_gs_1_mlkem_intt_passthrough_i;
assign fv_compute_u_gs_1_mlkem_intt_passthrough_i = compute_u_gs_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_2_mlkem_i;
assign fv_compute_u_gs_2_mlkem_i = compute_u_gs_mlkem(fv_compute_u_gs_0_mlkem_i, fv_compute_u_gs_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_0_i;
assign fv_compute_v_gs_0_i = compute_v_gs(fv_compute_u_gs_0_i, fv_compute_u_gs_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_0_mlkem_i;
assign fv_compute_v_gs_0_mlkem_i = compute_v_gs_mlkem(fv_compute_u_gs_0_mlkem_i, fv_compute_u_gs_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_1_i;
assign fv_compute_v_gs_1_i = compute_v_gs(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_gs_1_intt_passthrough_i;
assign fv_compute_v_gs_1_intt_passthrough_i = compute_v_gs(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_gs_2_i;
assign fv_compute_v_gs_2_i = compute_v_gs(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_gs_2_intt_passthrough_i;
assign fv_compute_v_gs_2_intt_passthrough_i = compute_v_gs(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_3_i;
assign fv_compute_u_gs_3_i = compute_u_gs(fv_compute_v_gs_1_i, fv_compute_v_gs_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_1_mlkem_i;
assign fv_compute_v_gs_1_mlkem_i = compute_v_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_gs_1_mlkem_intt_passthrough_i;
assign fv_compute_v_gs_1_mlkem_intt_passthrough_i = compute_v_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_gs_2_mlkem_i;
assign fv_compute_v_gs_2_mlkem_i = compute_v_gs_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_gs_2_mlkem_intt_passthrough_i;
assign fv_compute_v_gs_2_mlkem_intt_passthrough_i = compute_v_gs_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_3_mlkem_i;
assign fv_compute_u_gs_3_mlkem_i = compute_u_gs_mlkem(fv_compute_v_gs_1_mlkem_i, fv_compute_v_gs_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_3_i;
assign fv_compute_v_gs_3_i = compute_v_gs(fv_compute_v_gs_1_i, fv_compute_v_gs_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_3_mlkem_i;
assign fv_compute_v_gs_3_mlkem_i = compute_v_gs_mlkem(fv_compute_v_gs_1_mlkem_i, fv_compute_v_gs_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_pwm_0_i;
assign fv_compute_pwm_0_i = compute_pwm(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i, pi_pw_uvw_i.w2_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_1_i;
assign fv_compute_pwm_1_i = compute_pwm(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i, pi_pw_uvw_i.w3_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_2_i;
assign fv_compute_pwm_2_i = compute_pwm(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i, pi_pw_uvw_i.w0_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_3_i;
assign fv_compute_pwm_3_i = compute_pwm(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i, pi_pw_uvw_i.w1_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwa_0_i;
assign fv_compute_pwa_0_i = compute_pwa(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] fv_compute_pwa_1_i;
assign fv_compute_pwa_1_i = compute_pwa(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pwa_2_i;
assign fv_compute_pwa_2_i = compute_pwa(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pwa_3_i;
assign fv_compute_pwa_3_i = compute_pwa(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pwa_0_mlkem_i;
assign fv_compute_pwa_0_mlkem_i = compute_pwa_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] fv_compute_pwa_1_mlkem_i;
assign fv_compute_pwa_1_mlkem_i = compute_pwa_mlkem(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pwa_2_mlkem_i;
assign fv_compute_pwa_2_mlkem_i = compute_pwa_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pwa_3_mlkem_i;
assign fv_compute_pwa_3_mlkem_i = compute_pwa_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pws_0_i;
assign fv_compute_pws_0_i = compute_pws(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] fv_compute_pws_1_i;
assign fv_compute_pws_1_i = compute_pws(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pws_2_i;
assign fv_compute_pws_2_i = compute_pws(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pws_3_i;
assign fv_compute_pws_3_i = compute_pws(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pws_0_mlkem_i;
assign fv_compute_pws_0_mlkem_i = compute_pws_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] fv_compute_pws_1_mlkem_i;
assign fv_compute_pws_1_mlkem_i = compute_pws_mlkem(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pws_2_mlkem_i;
assign fv_compute_pws_2_mlkem_i = compute_pws_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pws_3_mlkem_i;
assign fv_compute_pws_3_mlkem_i = compute_pws_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);


sequence reset_sequence;
  !pi_reset_n ##1 pi_reset_n;
endsequence

//Reset property
property run_reset_p;
  !$past(pi_reset_n)
|->
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == 1'd0 &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0 ;
endproperty
assert_run_reset: assert property (run_reset_p);

/****************************************************************************/
  //CT ntt_passthrough MLKEM
/****************************************************************************/

// Model the ntt_passthrough MLKEM CT behavior after stage1 BF stopat cuts.
// MLKEM_BF_STAGE1_LATENCY = 3: the cut outputs are constrained to equal
// the CT fv_result of inputs from 3 cycles ago.
// Cut outputs from bf_inst00/01 are free variables. After MLKEM_BF_STAGE1_LATENCY
// cycles the pipeline has filled; from that point the values are stable and in range.
// No arithmetic — just stability + range. Avoids reintroducing multiplication.


// CT ntt_passthrough MLKEM: shift registers u10_reg/v10_reg/u11_reg/v11_reg
// (depth = MLKEM_BF_STAGE1_LATENCY = 3) carry the stage1 cut outputs to the
// output mux. At the consequent time T+6, $past(...,3) looks back to T+3,
// which is exactly what u10_reg[0] delivers — no arithmetic required.
property run_CT_ntt_passthrough_mlkem_p;
  (pi_mode == 3'd0) &&
  pi_mlkem &&
  pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == $past(fv_compute_u_ct_0_mlkem_i, BF_LATENCY) &&

  po_uv_o.u21_o == $past(fv_compute_v_ct_1_mlkem_i, BF_LATENCY) &&

  po_uv_o.v20_o == $past(fv_compute_u_ct_1_mlkem_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_ct_2_mlkem_i, BF_LATENCY) &&
  po_ready_o == $past(pi_enable, BF_LATENCY)
  ;
endproperty
assert_run_ct_ntt_passthrough_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_ntt_passthrough_mlkem_p);




//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode (HB witness 11 bound 10)
property run_CT_p;
  (pi_mode == 3'd0) &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, BF_LATENCY) &&
  po_uv_o.u20_o == $past(fv_compute_u_ct_2_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_ct_3_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_ct_0_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_ct_3_i, BF_LATENCY)
  ;
endproperty
assert_run_ct: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_p);




//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mlkem mode (HB witness 7 bound 6)
property run_CT_mlkem_p;
  (pi_mode == 3'd0) &&

  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_uv_o.u20_o == $past(fv_compute_u_ct_2_mlkem_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_ct_3_mlkem_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_ct_0_mlkem_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_ct_3_mlkem_i, BF_LATENCY)
  ;
endproperty
assert_run_ct_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_mlkem_p);


//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM not accumulate mode (HB witness 5 bound 4)
property run_PWM_p;
  (pi_mode == 3'd2) &&
  !pi_accumulate &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##(PWM_LATENCY-1) // PWM not accumulate case, so 1 cycle less than accumulate case
  po_pwo_uv_o.uv0 == $past(fv_compute_pwm_2_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwm_3_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwm_0_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwm_1_i, (PWM_LATENCY-1)) &&
  po_ready_o == $past(pi_enable, (PWM_LATENCY-1)) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwm: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM accumulate mode (HB witness 6 bound 5)
property run_PWMA_p;
  (pi_mode == 3'd2) &&
  pi_accumulate &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##PWM_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pwm_2_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwm_3_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwm_0_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwm_1_i, PWM_LATENCY) &&
  po_ready_o == $past(pi_enable, PWM_LATENCY) &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwma: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWMA_p);



property run_GS_p;
  (pi_mode == 3'd1) &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, BF_LATENCY) &&
  po_uv_o.u20_o == $past(fv_compute_u_gs_2_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_gs_3_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_gs_0_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_gs_3_i, BF_LATENCY);
endproperty
assert_run_gs: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_p);


//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mlkem mode (HB witness 7 bound 6)
property run_GS_mlkem_p;
  (pi_mode == 3'd1) &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o == $past(pi_enable, BF_LATENCY) &&
  po_uv_o.u20_o == $past(fv_compute_u_gs_2_mlkem_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_gs_3_mlkem_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_gs_0_mlkem_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_gs_3_mlkem_i, BF_LATENCY)
  ;
endproperty
assert_run_gs_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_mlkem_p);


//property to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mode with intt_passthrough mlkem (HB witness 7 bound 6)
property run_GS_mlkem_intt_passthrough_p;
  (pi_mode == 3'd1) &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  pi_intt_passthrough &&
  pi_enable
|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
po_uv_o.u20_o == $past(fv_compute_u_gs_0_mlkem_intt_passthrough_i, BF_LATENCY) &&
po_uv_o.u21_o == $past(fv_compute_u_gs_1_mlkem_intt_passthrough_i, BF_LATENCY) &&
po_uv_o.v20_o == $past(fv_compute_v_gs_1_mlkem_intt_passthrough_i, BF_LATENCY) &&
po_uv_o.v21_o == $past(fv_compute_v_gs_2_mlkem_intt_passthrough_i, BF_LATENCY) &&
  po_ready_o == $past(pi_enable, BF_LATENCY)
  ;
endproperty
assert_run_gs_mlkem_intt_passthrough: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_mlkem_intt_passthrough_p);






//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA mode (hold)
property run_PWA_p;
  (pi_mode == 3'd3) &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##PWA_LATENCY    //for pwa/pws enable comes out in 1 cycle
  po_pwo_uv_o.uv0 == $past(fv_compute_pwa_2_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwa_3_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwa_0_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwa_1_i, PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwa: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_p);


//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA mlkem mode (hold)
property run_PWA_mlkem_p;
  (pi_mode == 3'd3) &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##PWA_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pwa_2_mlkem_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwa_3_mlkem_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwa_0_mlkem_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwa_1_mlkem_i, PWA_LATENCY) &&
  po_ready_o == $past(pi_enable, PWA_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwa_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_mlkem_p);


//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS mode (hold)
property run_PWS_p;
  (pi_mode == 3'd4) &&
  !pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##PWS_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pws_2_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pws_3_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pws_0_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pws_1_i, PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pws: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_p);

//Property to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS mlkem mode (hold)
property run_PWS_mlkem_p;
  (pi_mode == 3'd4) &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##PWS_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pws_2_mlkem_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pws_3_mlkem_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pws_0_mlkem_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pws_1_mlkem_i, PWS_LATENCY) &&
  po_ready_o == $past(pi_enable, PWS_LATENCY) &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pws_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_mlkem_p);



property run_pairwm_accumulate_p;
  (pi_mode == 3'd5) &&
  pi_accumulate &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  po_pwo_uv_o.uv0 == ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv0_o &&
  po_pwo_uv_o.uv1 == ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv1_o &&
  po_pwo_uv_o.uv2 == ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv0_o &&
  po_pwo_uv_o.uv3 == ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv1_o

  ##(MLKEM_PAIRWM_ACC_LATENCY)
  po_ready_o //== $past(pi_enable, (MLKEM_PAIRWM_LATENCY)) //because pairwm outputs are cut, so only 1 PWM stage delay remains
  ;
endproperty
assert_run_pairwm_accumulate_a_old: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_accumulate_p);



cover_pairwm_active: cover property (disable iff(!pi_reset_n | pi_zeroize)
    (pi_mode == 3'd5) && pi_mlkem && (ntt_hybrid_butterfly_2x2.bf00_pairwm_mul_red != 23'd0));




function automatic logic [MLKEM_REG_SIZE-1:0] karatsuba_c0(
    input logic [MLKEM_REG_SIZE-1:0] m0,
    input logic [MLKEM_REG_SIZE-1:0] m1,
    input logic [MLKEM_REG_SIZE-1:0] zeta
);
    logic [(2*MLKEM_REG_SIZE)-1:0] fv_m1z;
    fv_m1z = m1 * zeta;
    return MLKEM_REG_SIZE'((m0 + (fv_m1z % MLKEM_Q)) % MLKEM_Q);
endfunction

function automatic logic [MLKEM_REG_SIZE-1:0] karatsuba_c1(
    input logic [MLKEM_REG_SIZE-1:0] m0,
    input logic [MLKEM_REG_SIZE-1:0] m1,
    input logic [MLKEM_REG_SIZE-1:0] u0,
    input logic [MLKEM_REG_SIZE-1:0] u1,
    input logic [MLKEM_REG_SIZE-1:0] v0,
    input logic [MLKEM_REG_SIZE-1:0] v1
);
    logic [(2*MLKEM_REG_SIZE)-1:0] fv_m2;
    fv_m2 = ((u0 + u1) % MLKEM_Q) * ((v0 + v1) % MLKEM_Q);  // matches abr_ntt_add_sub_mod pre-add
    return MLKEM_REG_SIZE'(((fv_m2 % MLKEM_Q) + 2*MLKEM_Q - m0 - m1) % MLKEM_Q);
endfunction

// Accumulate variants: add w{0,1} from w{0,1}_reg[3] (w delayed 4 cycles, aligned to T+0 inputs)
function automatic logic [MLKEM_REG_SIZE-1:0] karatsuba_c0_acc(
    input logic [MLKEM_REG_SIZE-1:0] m0,
    input logic [MLKEM_REG_SIZE-1:0] m1,
    input logic [MLKEM_REG_SIZE-1:0] zeta,
    input logic [MLKEM_REG_SIZE-1:0] w
);
    return MLKEM_REG_SIZE'((karatsuba_c0(m0, m1, zeta) + w) % MLKEM_Q);
endfunction

function automatic logic [MLKEM_REG_SIZE-1:0] karatsuba_c1_acc(
    input logic [MLKEM_REG_SIZE-1:0] m0,
    input logic [MLKEM_REG_SIZE-1:0] m1,
    input logic [MLKEM_REG_SIZE-1:0] u0,
    input logic [MLKEM_REG_SIZE-1:0] u1,
    input logic [MLKEM_REG_SIZE-1:0] v0,
    input logic [MLKEM_REG_SIZE-1:0] v1,
    input logic [MLKEM_REG_SIZE-1:0] w
);
    return MLKEM_REG_SIZE'((karatsuba_c1(m0, m1, u0, u1, v0, v1) + w) % MLKEM_Q);
endfunction

// PAIRWM-002: independent Karatsuba computation reference model
// Karatsuba0 drives po_pwo_uv_o.uv0/uv1 from pw lanes 0/1 and zeta z0_i.
// Karatsuba1 drives po_pwo_uv_o.uv2/uv3 from pw lanes 2/3 and zeta z1_i.

// -- Karatsuba0 (lanes 0/1 -> uv0/uv1) --
logic unsigned [22:0] fv_compute_pairwm0_uv00_i;
assign fv_compute_pairwm0_uv00_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pairwm0_uv11_i;
assign fv_compute_pairwm0_uv11_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pairwm0_uvz11_i;
assign fv_compute_pairwm0_uvz11_i = compute_pairwm_mult_mlkem(fv_compute_pairwm0_uv11_i, 23'(pi_mlkem_pairwm_zeta13_i.z0_i));

logic unsigned [22:0] fv_compute_pairwm0_uv0_i;
assign fv_compute_pairwm0_uv0_i = compute_pwa_mlkem(fv_compute_pairwm0_uvz11_i, fv_compute_pairwm0_uv00_i);

logic unsigned [22:0] fv_compute_pairwm0_addu_i;
assign fv_compute_pairwm0_addu_i = compute_pwa_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.u1_i);

logic unsigned [22:0] fv_compute_pairwm0_addv_i;
assign fv_compute_pairwm0_addv_i = compute_pwa_mlkem(pi_pw_uvw_i.v0_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pairwm0_m2_i;
assign fv_compute_pairwm0_m2_i = compute_pairwm_mult_mlkem(fv_compute_pairwm0_addu_i, fv_compute_pairwm0_addv_i);

logic unsigned [22:0] fv_compute_pairwm0_sub0_i;
assign fv_compute_pairwm0_sub0_i = compute_a_min_b(fv_compute_pairwm0_m2_i, fv_compute_pairwm0_uv00_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm0_uv1_i;
assign fv_compute_pairwm0_uv1_i = compute_a_min_b(fv_compute_pairwm0_sub0_i, fv_compute_pairwm0_uv11_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm0_uv0_acc_i;
assign fv_compute_pairwm0_uv0_acc_i = compute_pwa_mlkem(fv_compute_pairwm0_uv0_i, pi_pw_uvw_i.w0_i);

logic unsigned [22:0] fv_compute_pairwm0_uv1_acc_i;
assign fv_compute_pairwm0_uv1_acc_i = compute_pwa_mlkem(fv_compute_pairwm0_uv1_i, pi_pw_uvw_i.w1_i);

// -- Karatsuba1 (lanes 2/3 -> uv2/uv3) --
logic unsigned [22:0] fv_compute_pairwm1_uv00_i;
assign fv_compute_pairwm1_uv00_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i);

logic unsigned [22:0] fv_compute_pairwm1_uv11_i;
assign fv_compute_pairwm1_uv11_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pairwm1_uvz11_i;
assign fv_compute_pairwm1_uvz11_i = compute_pairwm_mult_mlkem(fv_compute_pairwm1_uv11_i, 23'(pi_mlkem_pairwm_zeta13_i.z1_i));

logic unsigned [22:0] fv_compute_pairwm1_uv0_i;
assign fv_compute_pairwm1_uv0_i = compute_pwa_mlkem(fv_compute_pairwm1_uvz11_i, fv_compute_pairwm1_uv00_i);

logic unsigned [22:0] fv_compute_pairwm1_addu_i;
assign fv_compute_pairwm1_addu_i = compute_pwa_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.u3_i);

logic unsigned [22:0] fv_compute_pairwm1_addv_i;
assign fv_compute_pairwm1_addv_i = compute_pwa_mlkem(pi_pw_uvw_i.v2_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pairwm1_m2_i;
assign fv_compute_pairwm1_m2_i = compute_pairwm_mult_mlkem(fv_compute_pairwm1_addu_i, fv_compute_pairwm1_addv_i);

logic unsigned [22:0] fv_compute_pairwm1_sub0_i;
assign fv_compute_pairwm1_sub0_i = compute_a_min_b(fv_compute_pairwm1_m2_i, fv_compute_pairwm1_uv00_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm1_uv1_i;
assign fv_compute_pairwm1_uv1_i = compute_a_min_b(fv_compute_pairwm1_sub0_i, fv_compute_pairwm1_uv11_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm1_uv0_acc_i;
assign fv_compute_pairwm1_uv0_acc_i = compute_pwa_mlkem(fv_compute_pairwm1_uv0_i, pi_pw_uvw_i.w2_i);

logic unsigned [22:0] fv_compute_pairwm1_uv1_acc_i;
assign fv_compute_pairwm1_uv1_acc_i = compute_pwa_mlkem(fv_compute_pairwm1_uv1_i, pi_pw_uvw_i.w3_i);

property run_pairwm_p;
  (pi_mode == 3'd5) &&
  !pi_accumulate &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##MLKEM_PAIRWM_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pairwm0_uv0_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pairwm0_uv1_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pairwm1_uv0_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pairwm1_uv1_i, MLKEM_PAIRWM_LATENCY);
endproperty
assert_run_pairwm: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_p);

property run_pairwm_accumulate_path_p;
  (pi_mode == 3'd5) &&
  pi_accumulate &&
  pi_mlkem &&
  !pi_ntt_passthrough &&
  !pi_intt_passthrough &&
  pi_enable
|->
  ##MLKEM_PAIRWM_ACC_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pairwm0_uv0_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pairwm0_uv1_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pairwm1_uv0_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pairwm1_uv1_acc_i, MLKEM_PAIRWM_ACC_LATENCY);

endproperty
assert_run_pairwm_accumulate: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_accumulate_path_p);




////////////////////////////////
/****************************************************************************/
// WHITE BOX CONNECTION CHECKS — corrected for ntt_hybrid_butterfly_2x2
/****************************************************************************/

//--------------------------------------------------------------------------
// 1. Mode decode
//--------------------------------------------------------------------------
property wb_pwo_mode_decode_p;
  ntt_hybrid_butterfly_2x2.pwo_mode == (pi_mode inside {pwm, pwa, pws});
endproperty
assert_wb_pwo_mode_decode: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_mode_decode_p);

property wb_pairwm_mode_decode_p;
  ntt_hybrid_butterfly_2x2.pairwm_mode == (pi_mlkem && (pi_mode == pairwm));
endproperty
assert_wb_pairwm_mode_decode: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_mode_decode_p);

//--------------------------------------------------------------------------
// 2. Stage-1 inputs — NTT/GS mode (!(pwo_mode|pairwm_mode))
//
// intt_passthrough mux applies to opv_i(bf00), opw_i(bf00),
//                                   opu_i(bf01), opw_i(bf01).
// opv_i(bf01) is ALWAYS v01 — no passthrough mux on that port.
//--------------------------------------------------------------------------
property wb_bf00_ntt_opu_p;   // u00 — no passthrough mux
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opu_i == pi_uvw_i.u00_i;
endproperty
assert_wb_bf00_ntt_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opu_p);

property wb_bf00_ntt_opv_p;   // v00 ↔ u01 swapped by intt_passthrough
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opv_i ==
    (pi_intt_passthrough ? pi_uvw_i.u01_i : pi_uvw_i.v00_i);
endproperty
assert_wb_bf00_ntt_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opv_p);

property wb_bf00_ntt_opw_p;   // w00_i; intt_passthrough uses w10_i[11:0] instead
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opw_i ==
    (pi_intt_passthrough ?
      NTT_REG_SIZE'(pi_uvw_i.w10_i[MLKEM_REG_SIZE-1:0]) : pi_uvw_i.w00_i);
endproperty
assert_wb_bf00_ntt_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opw_p);

property wb_bf01_ntt_opu_p;   // u01 ↔ v00 swapped by intt_passthrough
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opu_i ==
    (pi_intt_passthrough ? pi_uvw_i.v00_i : pi_uvw_i.u01_i);
endproperty
assert_wb_bf01_ntt_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opu_p);

property wb_bf01_ntt_opv_p;   // v01 — no passthrough mux on this port
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opv_i == pi_uvw_i.v01_i;
endproperty
assert_wb_bf01_ntt_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opv_p);

property wb_bf01_ntt_opw_p;   // w01_i; intt_passthrough uses w11_i[11:0] instead
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opw_i ==
    (pi_intt_passthrough ?
      NTT_REG_SIZE'(pi_uvw_i.w11_i[MLKEM_REG_SIZE-1:0]) : pi_uvw_i.w01_i);
endproperty
assert_wb_bf01_ntt_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opw_p);

//--------------------------------------------------------------------------
// 3. Stage-1 inputs — PWO/pairwm mode
//
// intt_passthrough STILL applies to opv(bf00), opw(bf00), opu(bf01), opw(bf01).
// Key: in intt_passthrough, opw comes from uvw_i.w10/11 (NTT twiddle),
//      NOT from pw_uvw_i.w0/1 — this is the same mux as NTT mode.
//--------------------------------------------------------------------------
property wb_bf00_pwo_opu_p;   // u00 = pw_uvw_i.u0_i, no passthrough mux
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opu_i == pi_pw_uvw_i.u0_i;
endproperty
assert_wb_bf00_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opu_p);

property wb_bf00_pwo_opv_p;   // v0↔u1 swapped by intt_passthrough
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opv_i ==
    (pi_intt_passthrough ? pi_pw_uvw_i.u1_i : pi_pw_uvw_i.v0_i);
endproperty
assert_wb_bf00_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opv_p);

property wb_bf00_pwo_opw_p;   // normal: pw_uvw_i.w0_i; intt_passthrough: uvw_i.w10_i[11:0]
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst00.opw_i ==
    (pi_intt_passthrough ?
      NTT_REG_SIZE'(pi_uvw_i.w10_i[MLKEM_REG_SIZE-1:0]) : pi_pw_uvw_i.w0_i);
endproperty
assert_wb_bf00_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opw_p);

property wb_bf01_pwo_opu_p;   // v0↔u1 swapped by intt_passthrough
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opu_i ==
    (pi_intt_passthrough ? pi_pw_uvw_i.v0_i : pi_pw_uvw_i.u1_i);
endproperty
assert_wb_bf01_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opu_p);

property wb_bf01_pwo_opv_p;   // v01 = pw_uvw_i.v1_i, no passthrough mux
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opv_i == pi_pw_uvw_i.v1_i;
endproperty
assert_wb_bf01_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opv_p);

property wb_bf01_pwo_opw_p;   // normal: pw_uvw_i.w1_i; intt_passthrough: uvw_i.w11_i[11:0]
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst01.opw_i ==
    (pi_intt_passthrough ?
      NTT_REG_SIZE'(pi_uvw_i.w11_i[MLKEM_REG_SIZE-1:0]) : pi_pw_uvw_i.w1_i);
endproperty
assert_wb_bf01_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opw_p);

//--------------------------------------------------------------------------
// 4. Stage-2 inputs — PWO/pairwm mode (opu/opv only)
//    opw is mode-split: pwo_mode → pw_uvw_i.w2/3_i (section 6 D1)
//                       pairwm_mode → mlkem_w10/11_reg[0]  (section 6 D2)
//    No intt_passthrough mux on stage-2 u/v operands.
//--------------------------------------------------------------------------
property wb_bf10_pwo_opu_opv_p;
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst10.opu_i == pi_pw_uvw_i.u2_i &&
  ntt_hybrid_butterfly_2x2.bf_inst10.opv_i == pi_pw_uvw_i.v2_i;
endproperty
assert_wb_bf10_pwo_opu_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_pwo_opu_opv_p);

property wb_bf11_pwo_opu_opv_p;
  (ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst11.opu_i == pi_pw_uvw_i.u3_i &&
  ntt_hybrid_butterfly_2x2.bf_inst11.opv_i == pi_pw_uvw_i.v3_i;
endproperty
assert_wb_bf11_pwo_opu_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_pwo_opu_opv_p);

property wb_bf10_pwo_opw_p;   // pwo_mode only — pairwm falls to mlkem twiddle (section 6)
  ntt_hybrid_butterfly_2x2.pwo_mode
|->
  ntt_hybrid_butterfly_2x2.bf_inst10.opw_i == pi_pw_uvw_i.w2_i;
endproperty
assert_wb_bf10_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_pwo_opw_p);

property wb_bf11_pwo_opw_p;
  ntt_hybrid_butterfly_2x2.pwo_mode
|->
  ntt_hybrid_butterfly_2x2.bf_inst11.opw_i == pi_pw_uvw_i.w3_i;
endproperty
assert_wb_bf11_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_pwo_opw_p);

//--------------------------------------------------------------------------
// 5. Stage-1 → Stage-2 crossbar (NTT/GS mode)
//    u10_int = bf_inst00.u_o,  v10_int = bf_inst01.u_o
//    u11_int = bf_inst00.v_o,  v11_int = bf_inst01.v_o
//    These drive bf_opu10/v10/u11/v11 which connect to bf_inst10/11.
//    No passthrough mux on the stage-2 u/v INPUTS (only on outputs).
//--------------------------------------------------------------------------
property wb_crossbar_p;
  !(ntt_hybrid_butterfly_2x2.pwo_mode || ntt_hybrid_butterfly_2x2.pairwm_mode)
|->
  ntt_hybrid_butterfly_2x2.bf_inst10.opu_i == ntt_hybrid_butterfly_2x2.bf_inst00.u_o &&
  ntt_hybrid_butterfly_2x2.bf_inst10.opv_i == ntt_hybrid_butterfly_2x2.bf_inst01.u_o &&
  ntt_hybrid_butterfly_2x2.bf_inst11.opu_i == ntt_hybrid_butterfly_2x2.bf_inst00.v_o &&
  ntt_hybrid_butterfly_2x2.bf_inst11.opv_i == ntt_hybrid_butterfly_2x2.bf_inst01.v_o;
endproperty
assert_wb_crossbar: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_crossbar_p);

//--------------------------------------------------------------------------
// 6. Stage-2 twiddle mux (bf_opw10/11)
//   pwo_mode        → pw_uvw_i.w2/3_i   (covered in section 4)
//   else if mlkem   → NTT_REG_SIZE'(mlkem_w10/11_reg[0])  (includes pairwm_mode)
//   else (mldsa)    → mldsa_w10/11_reg[0]
//--------------------------------------------------------------------------
property wb_bf10_twiddle_mldsa_p;
  !ntt_hybrid_butterfly_2x2.pwo_mode && !pi_mlkem
|->
  ntt_hybrid_butterfly_2x2.bf_inst10.opw_i == ntt_hybrid_butterfly_2x2.mldsa_w10_reg[0];
endproperty
assert_wb_bf10_twiddle_mldsa: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_twiddle_mldsa_p);

property wb_bf11_twiddle_mldsa_p;
  !ntt_hybrid_butterfly_2x2.pwo_mode && !pi_mlkem
|->
  ntt_hybrid_butterfly_2x2.bf_inst11.opw_i == ntt_hybrid_butterfly_2x2.mldsa_w11_reg[0];
endproperty
assert_wb_bf11_twiddle_mldsa: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_twiddle_mldsa_p);

// covers ct/gs AND pairwm for mlkem
property wb_bf10_twiddle_mlkem_p;
  !ntt_hybrid_butterfly_2x2.pwo_mode && pi_mlkem
|->
  ntt_hybrid_butterfly_2x2.bf_inst10.opw_i ==
    NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.mlkem_w10_reg[0]);
endproperty
assert_wb_bf10_twiddle_mlkem: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_twiddle_mlkem_p);

property wb_bf11_twiddle_mlkem_p;
  !ntt_hybrid_butterfly_2x2.pwo_mode && pi_mlkem
|->
  ntt_hybrid_butterfly_2x2.bf_inst11.opw_i ==
    NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.mlkem_w11_reg[0]);
endproperty
assert_wb_bf11_twiddle_mlkem: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_twiddle_mlkem_p);

//--------------------------------------------------------------------------
// 7a. Twiddle shift-register load and propagation (mldsa/mlkem w10/11)
//     Shift: {new, reg[N-1:1]} → new enters at index [N-1], output at [0]
//--------------------------------------------------------------------------
property wb_mldsa_w10_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mldsa_w10_reg[BF_STAGE1_LATENCY-1] == $past(pi_uvw_i.w10_i);
endproperty
assert_wb_mldsa_w10_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_w10_reg_load_p);

property wb_mldsa_w11_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mldsa_w11_reg[BF_STAGE1_LATENCY-1] == $past(pi_uvw_i.w11_i);
endproperty
assert_wb_mldsa_w11_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_w11_reg_load_p);

property wb_mlkem_w10_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(pi_uvw_i.w10_i[MLKEM_REG_SIZE-1:0]);
endproperty
assert_wb_mlkem_w10_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mlkem_w10_reg_load_p);

property wb_mlkem_w11_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(pi_uvw_i.w11_i[MLKEM_REG_SIZE-1:0]);
endproperty
assert_wb_mlkem_w11_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mlkem_w11_reg_load_p);

property wb_mldsa_w10_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mldsa_w10_reg[BF_STAGE1_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.mldsa_w10_reg[BF_STAGE1_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.mldsa_w10_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.mldsa_w10_reg[1]);
endproperty
assert_wb_mldsa_w10_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_w10_reg_propagate_p);

property wb_mldsa_w11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mldsa_w11_reg[BF_STAGE1_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.mldsa_w11_reg[BF_STAGE1_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.mldsa_w11_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.mldsa_w11_reg[1]);
endproperty
assert_wb_mldsa_w11_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_w11_reg_propagate_p);

property wb_mlkem_w10_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.mlkem_w10_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.mlkem_w10_reg[1]);
endproperty
assert_wb_mlkem_w10_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mlkem_w10_reg_propagate_p);

property wb_mlkem_w11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.mlkem_w11_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.mlkem_w11_reg[1]);
endproperty
assert_wb_mlkem_w11_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mlkem_w11_reg_propagate_p);

//--------------------------------------------------------------------------
// 7b. Passthrough delay shift-registers (u10_reg/v10_reg/u11_reg/v11_reg)
//     Used by the stage-2 output mux in ntt/intt_passthrough modes.
//     These always shift from u10/v10/u11/v11 regardless of passthrough flag.
//--------------------------------------------------------------------------
property wb_u10_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.u10_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(ntt_hybrid_butterfly_2x2.u10);
endproperty
assert_wb_u10_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_u10_reg_load_p);

property wb_v10_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.v10_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(ntt_hybrid_butterfly_2x2.v10);
endproperty
assert_wb_v10_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_v10_reg_load_p);

property wb_u11_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.u11_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(ntt_hybrid_butterfly_2x2.u11);
endproperty
assert_wb_u11_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_u11_reg_load_p);

property wb_v11_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.v11_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(ntt_hybrid_butterfly_2x2.v11);
endproperty
assert_wb_v11_reg_load: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_v11_reg_load_p);

property wb_u10v11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.u10_reg[0] == $past(ntt_hybrid_butterfly_2x2.u10_reg[1]) &&
  ntt_hybrid_butterfly_2x2.v11_reg[0] == $past(ntt_hybrid_butterfly_2x2.v11_reg[1]);
endproperty
assert_wb_u10v11_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_u10v11_reg_propagate_p);

property wb_v10u11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_hybrid_butterfly_2x2.v10_reg[0] == $past(ntt_hybrid_butterfly_2x2.v10_reg[1]) &&
  ntt_hybrid_butterfly_2x2.u11_reg[0] == $past(ntt_hybrid_butterfly_2x2.u11_reg[1]);
endproperty
assert_wb_v10u11_reg_propagate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_v10u11_reg_propagate_p);

//--------------------------------------------------------------------------
// 8. Twiddle shift-registers cleared by reset and by zeroize
//--------------------------------------------------------------------------
property wb_twiddle_reg_reset_p;
  $past(!pi_reset_n)
|->
  ntt_hybrid_butterfly_2x2.mldsa_w10_reg == '0 &&
  ntt_hybrid_butterfly_2x2.mldsa_w11_reg == '0 &&
  ntt_hybrid_butterfly_2x2.mlkem_w10_reg == '0 &&
  ntt_hybrid_butterfly_2x2.mlkem_w11_reg == '0;
endproperty
assert_wb_twiddle_reg_reset: assert property (wb_twiddle_reg_reset_p);

property wb_twiddle_reg_zeroize_p;
  (ntt_hybrid_butterfly_2x2.mldsa_w10_reg != '0 ||
   ntt_hybrid_butterfly_2x2.mldsa_w11_reg != '0 ||
   ntt_hybrid_butterfly_2x2.mlkem_w10_reg != '0 ||
   ntt_hybrid_butterfly_2x2.mlkem_w11_reg != '0)
|->
  $past(!pi_zeroize || !pi_reset_n);
endproperty
assert_wb_twiddle_reg_zeroize: assert property (
  disable iff (!pi_reset_n) wb_twiddle_reg_zeroize_p);

//--------------------------------------------------------------------------
// 9. Stage-2 output mux → uv_o (po_uv_o)
//
// RTL mux:
//   u20_o = (ntt_passthrough | intt_passthrough) ? u10_reg[0] : u20_int
//   v20_o = ntt_passthrough ? v10_reg[0] : intt_passthrough ? u11_reg[0] : v20_int
//   u21_o = ntt_passthrough ? u11_reg[0] : intt_passthrough ? v10_reg[0] : u21_int
//   v21_o = (ntt_passthrough | intt_passthrough) ? v11_reg[0] : v21_int
//
// u10_reg[0]/v11_reg[0] are the same source for both ntt and intt passthrough.
// v20_o/u21_o differ: ntt takes v10_reg/u11_reg; intt CROSSES them (u11_reg/v10_reg).
//--------------------------------------------------------------------------

// u20 and v21 share the same source for both passthrough modes
property wb_out_u20_v21_passthrough_p;
  (pi_ntt_passthrough | pi_intt_passthrough)
|->
  po_uv_o.u20_o == ntt_hybrid_butterfly_2x2.u10_reg[0] &&
  po_uv_o.v21_o == ntt_hybrid_butterfly_2x2.v11_reg[0];
endproperty
assert_wb_out_u20_v21_passthrough: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_out_u20_v21_passthrough_p);

// Normal (no passthrough): BF outputs directly
property wb_out_normal_p;
  !(pi_ntt_passthrough | pi_intt_passthrough)
|->
  po_uv_o.u20_o == ntt_hybrid_butterfly_2x2.u20_int &&
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.v20_int &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.u21_int &&
  po_uv_o.v21_o == ntt_hybrid_butterfly_2x2.v21_int;
endproperty
assert_wb_out_normal: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_out_normal_p);

// ntt_passthrough: v20=v10_reg[0], u21=u11_reg[0]
property wb_out_v20_u21_ntt_p;
  pi_ntt_passthrough
|->
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.v10_reg[0] &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.u11_reg[0];
endproperty
assert_wb_out_v20_u21_ntt: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_out_v20_u21_ntt_p);

// intt_passthrough (!ntt): v20=u11_reg[0], u21=v10_reg[0]  — NOTE the cross
property wb_out_v20_u21_intt_p;
  !pi_ntt_passthrough && pi_intt_passthrough
|->
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.u11_reg[0] &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.v10_reg[0];
endproperty
assert_wb_out_v20_u21_intt: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_out_v20_u21_intt_p);

//--------------------------------------------------------------------------
// 10. MLDSA PWO collection: bf pwm_res_o → mldsa_pwo_uv_o fields
//     (combinational wiring always active, output used only in pwo mode)
//--------------------------------------------------------------------------
property wb_mldsa_pwo_routing_p;
  ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv0 ==
      ntt_hybrid_butterfly_2x2.bf_inst00.pwm_res_o &&
  ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv1 ==
      ntt_hybrid_butterfly_2x2.bf_inst01.pwm_res_o &&
  ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv2 ==
      ntt_hybrid_butterfly_2x2.bf_inst10.pwm_res_o &&
  ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv3 ==
      ntt_hybrid_butterfly_2x2.bf_inst11.pwm_res_o;
endproperty
assert_wb_mldsa_pwo_routing: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_pwo_routing_p);

//--------------------------------------------------------------------------
// 11. Final PWO output mux: pairwm_mode selects Karatsuba results
//     RTL select: pairwm_mode (NOT pi_mlkem — MLKEM ct/gs uses mldsa_pwo path)
//     uv2/uv3 map to pairwm_uv23_o.uv0_o / uv1_o respectively
//--------------------------------------------------------------------------
property wb_pwo_out_mux_p;
  po_pwo_uv_o.uv0 == (ntt_hybrid_butterfly_2x2.pairwm_mode ?
      NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv0_o) :
      ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv0) &&
  po_pwo_uv_o.uv1 == (ntt_hybrid_butterfly_2x2.pairwm_mode ?
      NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv1_o) :
      ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv1) &&
  po_pwo_uv_o.uv2 == (ntt_hybrid_butterfly_2x2.pairwm_mode ?
      NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv0_o) :
      ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv2) &&
  po_pwo_uv_o.uv3 == (ntt_hybrid_butterfly_2x2.pairwm_mode ?
      NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv1_o) :
      ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv3);
endproperty
assert_wb_pwo_out_mux: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_out_mux_p);

//--------------------------------------------------------------------------
// 12. Karatsuba pairwm input wiring (active only when pairwm_mode)
//--------------------------------------------------------------------------
property wb_pairwm_uvw01_p;
  ntt_hybrid_butterfly_2x2.pairwm_mode
|->
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.u0_i == pi_pw_uvw_i.u0_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.v0_i == pi_pw_uvw_i.v0_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.w0_i == pi_pw_uvw_i.w0_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.u1_i == pi_pw_uvw_i.u1_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.v1_i == pi_pw_uvw_i.v1_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i.w1_i == pi_pw_uvw_i.w1_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_p);

property wb_pairwm_uvw23_p;
  ntt_hybrid_butterfly_2x2.pairwm_mode
|->
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.u0_i == pi_pw_uvw_i.u2_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.v0_i == pi_pw_uvw_i.v2_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.w0_i == pi_pw_uvw_i.w2_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.u1_i == pi_pw_uvw_i.u3_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.v1_i == pi_pw_uvw_i.v3_i[MLKEM_REG_SIZE-1:0] &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i.w1_i == pi_pw_uvw_i.w3_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_p);

//--------------------------------------------------------------------------
// 13. Karatsuba structs forced to zero when not in pairwm_mode
//--------------------------------------------------------------------------
property wb_pairwm_uvw_zero_p;
  !ntt_hybrid_butterfly_2x2.pairwm_mode
|->
  ntt_hybrid_butterfly_2x2.pairwm_uvw01_i == '0 &&
  ntt_hybrid_butterfly_2x2.pairwm_uvw23_i == '0;
endproperty
assert_wb_pairwm_uvw_zero: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw_zero_p);

//--------------------------------------------------------------------------
// 14. Karatsuba m0/m1 tap connections (cut-points → structural only)
//--------------------------------------------------------------------------
property wb_karatsuba0_m0_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.m0_red_i ==
    ntt_hybrid_butterfly_2x2.bf00_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba0_m0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba0_m0_p);

property wb_karatsuba0_m1_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.m1_red_i ==
    ntt_hybrid_butterfly_2x2.bf01_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba0_m1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba0_m1_p);

property wb_karatsuba1_m0_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.m0_red_i ==
    ntt_hybrid_butterfly_2x2.bf10_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba1_m0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba1_m0_p);

property wb_karatsuba1_m1_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.m1_red_i ==
    ntt_hybrid_butterfly_2x2.bf11_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba1_m1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba1_m1_p);


//--------------------------------------------------------------------------
// 15. Karatsuba zeta connections
//--------------------------------------------------------------------------
property wb_karatsuba_zeta_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.pwo_z_i == pi_mlkem_pairwm_zeta13_i.z0_i &&
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.pwo_z_i == pi_mlkem_pairwm_zeta13_i.z1_i;
endproperty
assert_wb_karatsuba_zeta: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba_zeta_p);

//--------------------------------------------------------------------------
// 16. ready_o sourced from ready_reg[0]
//--------------------------------------------------------------------------
property wb_ready_o_p;
  po_ready_o == ntt_hybrid_butterfly_2x2.ready_reg[0];
endproperty
assert_wb_ready_o: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_ready_o_p);

//--------------------------------------------------------------------------
// 17. Control signals uniformly driven to all four BF instances
//--------------------------------------------------------------------------
property wb_bf_ctrl_p;
  ntt_hybrid_butterfly_2x2.bf_inst00.mode == pi_mode &&
  ntt_hybrid_butterfly_2x2.bf_inst01.mode == pi_mode &&
  ntt_hybrid_butterfly_2x2.bf_inst10.mode == pi_mode &&
  ntt_hybrid_butterfly_2x2.bf_inst11.mode == pi_mode &&
  ntt_hybrid_butterfly_2x2.bf_inst00.mlkem == pi_mlkem &&
  ntt_hybrid_butterfly_2x2.bf_inst01.mlkem == pi_mlkem &&
  ntt_hybrid_butterfly_2x2.bf_inst10.mlkem == pi_mlkem &&
  ntt_hybrid_butterfly_2x2.bf_inst11.mlkem == pi_mlkem &&
  ntt_hybrid_butterfly_2x2.bf_inst00.accumulate == pi_accumulate &&
  ntt_hybrid_butterfly_2x2.bf_inst01.accumulate == pi_accumulate &&
  ntt_hybrid_butterfly_2x2.bf_inst10.accumulate == pi_accumulate &&
  ntt_hybrid_butterfly_2x2.bf_inst11.accumulate == pi_accumulate;
endproperty
assert_wb_bf_ctrl: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf_ctrl_p);

property wb_bf_reset_n_p;
  ntt_hybrid_butterfly_2x2.bf_inst00.reset_n == pi_reset_n &&
  ntt_hybrid_butterfly_2x2.bf_inst01.reset_n == pi_reset_n &&
  ntt_hybrid_butterfly_2x2.bf_inst10.reset_n == pi_reset_n &&
  ntt_hybrid_butterfly_2x2.bf_inst11.reset_n == pi_reset_n;
endproperty
assert_wb_bf_reset_n: assert property (wb_bf_reset_n_p);

property wb_bf_zeroize_p;
  ntt_hybrid_butterfly_2x2.bf_inst00.zeroize == pi_zeroize &&
  ntt_hybrid_butterfly_2x2.bf_inst01.zeroize == pi_zeroize &&
  ntt_hybrid_butterfly_2x2.bf_inst10.zeroize == pi_zeroize &&
  ntt_hybrid_butterfly_2x2.bf_inst11.zeroize == pi_zeroize;
endproperty
assert_wb_bf_zeroize: assert property (
  disable iff (!pi_reset_n) wb_bf_zeroize_p);

//--------------------------------------------------------------------------
// 18. Control signals to Karatsuba instances
//--------------------------------------------------------------------------
property wb_karatsuba_ctrl_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.accumulate == pi_accumulate &&
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.accumulate == pi_accumulate &&
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.reset_n    == pi_reset_n    &&
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.reset_n    == pi_reset_n;
endproperty
assert_wb_karatsuba_ctrl: assert property (wb_karatsuba_ctrl_p);

property wb_karatsuba_zeroize_ctrl_p;
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst0.zeroize == pi_zeroize &&
  ntt_hybrid_butterfly_2x2.mlkem_pawm_inst1.zeroize == pi_zeroize;
endproperty
assert_wb_karatsuba_zeroize_ctrl: assert property (
  disable iff (!pi_reset_n) wb_karatsuba_zeroize_ctrl_p);

//--------------------------------------------------------------------------
// 19. End-to-end twiddle delay — catches off-by-one in register depth.
//     Guards: all past cycles must be uninterrupted (reset_n=1, zeroize=0).
//--------------------------------------------------------------------------
property wb_mldsa_w10_e2e_p;
  $past(pi_reset_n && !pi_zeroize, 1) &&
  $past(pi_reset_n && !pi_zeroize, 2) &&
  $past(pi_reset_n && !pi_zeroize, BF_STAGE1_LATENCY)
|->
  ntt_hybrid_butterfly_2x2.mldsa_w10_reg[0] ==
    $past(pi_uvw_i.w10_i, BF_STAGE1_LATENCY);
endproperty
assert_wb_mldsa_w10_e2e: assert property (
  disable iff (!pi_reset_n) wb_mldsa_w10_e2e_p);

property wb_mldsa_w11_e2e_p;
  $past(pi_reset_n && !pi_zeroize, 1) &&
  $past(pi_reset_n && !pi_zeroize, 2) &&
  $past(pi_reset_n && !pi_zeroize, BF_STAGE1_LATENCY)
|->
  ntt_hybrid_butterfly_2x2.mldsa_w11_reg[0] ==
    $past(pi_uvw_i.w11_i, BF_STAGE1_LATENCY);
endproperty
assert_wb_mldsa_w11_e2e: assert property (
  disable iff (!pi_reset_n) wb_mldsa_w11_e2e_p);

property wb_mlkem_w10_e2e_p;
  $past(pi_reset_n && !pi_zeroize, 1) &&
  $past(pi_reset_n && !pi_zeroize, 2) &&
  $past(pi_reset_n && !pi_zeroize, MLKEM_BF_STAGE1_LATENCY)
|->
  ntt_hybrid_butterfly_2x2.mlkem_w10_reg[0] ==
    $past(pi_uvw_i.w10_i[MLKEM_REG_SIZE-1:0], MLKEM_BF_STAGE1_LATENCY);
endproperty
assert_wb_mlkem_w10_e2e: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w10_e2e_p);

property wb_mlkem_w11_e2e_p;
  $past(pi_reset_n && !pi_zeroize, 1) &&
  $past(pi_reset_n && !pi_zeroize, 2) &&
  $past(pi_reset_n && !pi_zeroize, MLKEM_BF_STAGE1_LATENCY)
|->
  ntt_hybrid_butterfly_2x2.mlkem_w11_reg[0] ==
    $past(pi_uvw_i.w11_i[MLKEM_REG_SIZE-1:0], MLKEM_BF_STAGE1_LATENCY);
endproperty
assert_wb_mlkem_w11_e2e: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w11_e2e_p);

//--------------------------------------------------------------------------
// 20. Ready register per-mode shift (load checks only — propagation
//     is implicitly verified by sections 7a/19 for the twiddle regs)
//--------------------------------------------------------------------------
property wb_ready_ct_gs_mldsa_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode inside {ct, gs}) && !pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-1] == $past(pi_enable);
endproperty
assert_wb_ready_ct_gs_mldsa_load: assert property (
  disable iff (!pi_reset_n) wb_ready_ct_gs_mldsa_load_p);

property wb_ready_ct_gs_mldsa_prop_p;
  pi_reset_n && !pi_zeroize && (pi_mode inside {ct, gs}) && !pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.ready_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.ready_reg[1]);
endproperty
assert_wb_ready_ct_gs_mldsa_prop: assert property (
  disable iff (!pi_reset_n) wb_ready_ct_gs_mldsa_prop_p);

property wb_ready_ct_gs_mlkem_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode inside {ct, gs}) && pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-1] == $past(pi_enable);
endproperty
assert_wb_ready_ct_gs_mlkem_load: assert property (
  disable iff (!pi_reset_n) wb_ready_ct_gs_mlkem_load_p);

property wb_ready_ct_gs_mlkem_prop_p;
  pi_reset_n && !pi_zeroize && (pi_mode inside {ct, gs}) && pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-2] ==
    $past(ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-1]) &&
  ntt_hybrid_butterfly_2x2.ready_reg[0] ==
    $past(ntt_hybrid_butterfly_2x2.ready_reg[1]);
endproperty
assert_wb_ready_ct_gs_mlkem_prop: assert property (
  disable iff (!pi_reset_n) wb_ready_ct_gs_mlkem_prop_p);

property wb_ready_pwm_mldsa_nonacc_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode == pwm) && !pi_accumulate && !pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[PWM_LATENCY-2] == $past(pi_enable);
endproperty
assert_wb_ready_pwm_mldsa_nonacc_load: assert property (
  disable iff (!pi_reset_n) wb_ready_pwm_mldsa_nonacc_load_p);

property wb_ready_pwm_mldsa_acc_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode == pwm) && pi_accumulate && !pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[PWM_LATENCY-1] == $past(pi_enable);
endproperty
assert_wb_ready_pwm_mldsa_acc_load: assert property (
  disable iff (!pi_reset_n) wb_ready_pwm_mldsa_acc_load_p);

property wb_ready_pwm_mlkem_zero_p;   // MLKEM has no PWM mode — reg stays 0
  pi_reset_n && !pi_zeroize && (pi_mode == pwm) && pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg == '0;
endproperty
assert_wb_ready_pwm_mlkem_zero: assert property (
  disable iff (!pi_reset_n) wb_ready_pwm_mlkem_zero_p);

property wb_ready_pwa_pws_p;
  pi_reset_n && !pi_zeroize && (pi_mode inside {pwa, pws})
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[0]             == $past(pi_enable) &&
  ntt_hybrid_butterfly_2x2.ready_reg[BF_LATENCY-1:1] == '0;
endproperty
assert_wb_ready_pwa_pws: assert property (
  disable iff (!pi_reset_n) wb_ready_pwa_pws_p);

property wb_ready_pairwm_nonacc_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode == pairwm) && !pi_accumulate && pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[MLKEM_PAIRWM_LATENCY-1] == $past(pi_enable);
endproperty
assert_wb_ready_pairwm_nonacc_load: assert property (
  disable iff (!pi_reset_n) wb_ready_pairwm_nonacc_load_p);

property wb_ready_pairwm_acc_load_p;
  pi_reset_n && !pi_zeroize && (pi_mode == pairwm) && pi_accumulate && pi_mlkem
|=>
  ntt_hybrid_butterfly_2x2.ready_reg[MLKEM_PAIRWM_ACC_LATENCY-1] == $past(pi_enable);
endproperty
assert_wb_ready_pairwm_acc_load: assert property (
  disable iff (!pi_reset_n) wb_ready_pairwm_acc_load_p);

property wb_ready_reg_zeroize_p;
  ntt_hybrid_butterfly_2x2.ready_reg != '0
|->
  $past(!pi_zeroize || !pi_reset_n);
endproperty
assert_wb_ready_reg_zeroize: assert property (
  disable iff (!pi_reset_n) wb_ready_reg_zeroize_p);

  //--------------------------------------------------------------------------
// WB PORT: po_uv_o output mux routing
//--------------------------------------------------------------------------
property wb_po_uv_normal_p;
  pi_mode inside {ct, gs} && !pi_ntt_passthrough && !pi_intt_passthrough
|->
  po_uv_o.u20_o == ntt_hybrid_butterfly_2x2.u20_int &&
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.v20_int &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.u21_int &&
  po_uv_o.v21_o == ntt_hybrid_butterfly_2x2.v21_int;
endproperty
assert_wb_po_uv_normal: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_uv_normal_p);

property wb_po_uv_ntt_pass_p;
  pi_ntt_passthrough
|->
  po_uv_o.u20_o == ntt_hybrid_butterfly_2x2.u10_reg[0] &&
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.v10_reg[0] &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.u11_reg[0] &&
  po_uv_o.v21_o == ntt_hybrid_butterfly_2x2.v11_reg[0];
endproperty
assert_wb_po_uv_ntt_pass: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_uv_ntt_pass_p);

// Only v20/u21 are crossed in intt_passthrough — u20/v21 are not
property wb_po_uv_intt_pass_p;
  !pi_ntt_passthrough && pi_intt_passthrough
|->
  po_uv_o.v20_o == ntt_hybrid_butterfly_2x2.u11_reg[0] &&
  po_uv_o.u21_o == ntt_hybrid_butterfly_2x2.v10_reg[0];
endproperty
assert_wb_po_uv_intt_pass: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_uv_intt_pass_p);

//--------------------------------------------------------------------------
// WB PORT: po_pwo_uv_o final mux routing
//--------------------------------------------------------------------------
property wb_po_pwo_uv_pairwm_p;
  ntt_hybrid_butterfly_2x2.pairwm_mode
|->
  po_pwo_uv_o.uv0 == NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv0_o) &&
  po_pwo_uv_o.uv1 == NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv01_o.uv1_o) &&
  po_pwo_uv_o.uv2 == NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv0_o) &&
  po_pwo_uv_o.uv3 == NTT_REG_SIZE'(ntt_hybrid_butterfly_2x2.pairwm_uv23_o.uv1_o);
endproperty
assert_wb_po_pwo_uv_pairwm: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_pwo_uv_pairwm_p);

property wb_po_pwo_uv_mldsa_p;
  !ntt_hybrid_butterfly_2x2.pairwm_mode
|->
  po_pwo_uv_o.uv0 == ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv0 &&
  po_pwo_uv_o.uv1 == ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv1 &&
  po_pwo_uv_o.uv2 == ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv2 &&
  po_pwo_uv_o.uv3 == ntt_hybrid_butterfly_2x2.mldsa_pwo_uv_o.uv3;
endproperty
assert_wb_po_pwo_uv_mldsa: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_pwo_uv_mldsa_p);

//--------------------------------------------------------------------------
// WB PORT: po_ready_o port connectivity
//--------------------------------------------------------------------------
property wb_po_ready_o_connect_p;
  po_ready_o == ntt_hybrid_butterfly_2x2.ready_reg[0];
endproperty
assert_wb_po_ready_o_connect: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_po_ready_o_connect_p);


endmodule
