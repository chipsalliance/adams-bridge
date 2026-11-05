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
// Copyright(c) LUBIS EDA GmbH, All rights reservedntt_hybrid_butterfly_2x2
// Contact: contact@lubis-eda.com
// -------------------------------------------------
//#$includes

//$#//

module fv_ntt_butterfly2x2
    //#$imports
    //$#//
     import ntt_defines_pkg::*;
    import abr_params_pkg::*;

#(
    //#$parameters
    parameter REG_SIZE         = 23,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q + 1) / 2
    //$#//
    //#$localparams
    //$#//
) (
    //#$ports
    input wire                pi_clk,
    input wire                pi_reset_n,
    input wire                pi_zeroize,
    input mode_t              pi_mode,
    input wire                pi_enable,
    input bf_uvwi_t           pi_uvw_i,
    input pwo_uvwi_t          pi_pw_uvw_i,
    input wire                pi_accumulate,
    input wire                pi_mlkem,
    input mlkem_pairwm_zeta_t pi_mlkem_pairwm_zeta13_i,
    input bf_uvo_t            po_uv_o,
    input pwo_t               po_pwo_uv_o,
    input logic               po_ready_o
    //$#//
);

    //#$instances
    //$#//

    default clocking default_clk @(posedge pi_clk); endclocking

// added for the pwa/pws operations
localparam PWA_LATENCY = 1;
localparam PWS_LATENCY = 1;

function automatic logic unsigned [22:0] compute_a_min_b(
    logic unsigned [22:0] a,
    logic unsigned [22:0] b,
    logic mlkem
);
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
  logic unsigned [22:0] fv_result; // @ ntt_butterfly2x2.h:74:5

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

function automatic logic unsigned [22:0] compute_u_ct(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  return 23'((u + 23'((v * w) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_u_ct_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  return 23'((u + 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q)) % MLKEM_Q);
endfunction

function automatic logic unsigned [22:0] compute_v_ct(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result;

  fv_result = 23'((v * w) % 64'(MLDSA_Q));
  return compute_a_min_b(u, fv_result, 1'b0);
endfunction

function automatic logic unsigned [22:0] compute_v_ct_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result;

  fv_result = 23'((2*MLKEM_REG_SIZE)'(v * w) % MLKEM_Q);
  return compute_a_min_b(u, fv_result, 1'b1);
endfunction

function automatic logic unsigned [22:0] compute_u_gs(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly2x2.h:117:5

  fv_result = 23'((u + v) % 64'(MLDSA_Q));
  return 23'(div2(fv_result) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_u_gs_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly2x2.h:117:5

  fv_result = 23'((u + v) % MLKEM_Q);
  return 23'(div2_mlkem(fv_result) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_v_gs(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly2x2.h:123:5

  fv_result = compute_a_min_b(u, v, 1'b0);
  return 23'((div2(fv_result) * w) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_v_gs_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w
);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly2x2.h:123:5

  fv_result = compute_a_min_b(u, v, 1'b1);
  return 23'(((2*MLKEM_REG_SIZE)'(div2_mlkem(fv_result) * w)) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_pwm(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v,
    logic unsigned [22:0] w,
    logic unsigned [0:0] acc
);
  if (acc != 64'd0) begin
    return 23'((w + 23'((u * v) % 64'(MLDSA_Q))) % 64'(MLDSA_Q));
  end else begin
    return 23'((u * v) % 64'(MLDSA_Q));
  end
endfunction


function automatic logic unsigned [22:0] compute_pwa(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v
);
  return 23'((u + v) % 64'(MLDSA_Q));
endfunction

function automatic logic unsigned [22:0] compute_pwa_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v
);
  return 23'((u + v) % MLKEM_Q);
endfunction


function automatic logic unsigned [22:0] compute_pws(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v
);
  return compute_a_min_b(u, v, 1'b0);
endfunction

function automatic logic unsigned [22:0] compute_pws_mlkem(
    logic unsigned [22:0] u,
    logic unsigned [22:0] v
);
  return compute_a_min_b(u, v, 1'b1);
endfunction


// Karatsuba pairwm modular multiply (PAIRWM-002): c2i = m0 + (m1*zeta), c2i+1 = m2 - m0 - m1,
// m2 = (u0+u1)*(v0+v1). Mirrors ntt_karatsuba_pairwm.sv / fv_ntt_karatsuba_pairwm_top.sv's
// fv_mult_modQ, transplanted onto ntt_butterfly2x2's own pi_pw_uvw_i / pi_mlkem_pairwm_zeta13_i
// primary inputs so this file independently re-derives the Karatsuba result end-to-end.
function automatic logic unsigned [22:0] compute_pairwm_mult_mlkem(
    logic unsigned [22:0] a,
    logic unsigned [22:0] b
);
  return 23'((2*MLKEM_REG_SIZE)'(a * b) % MLKEM_Q);
endfunction


// NOTE (CTGS-002): the *_intt_passthrough_i signals defined below are dead
// reference logic — ntt_butterfly2x2 has no single-stage INTT-passthrough
// mode, so no property in this file reads them. Kept only as inert leftover
// scaffolding; do not treat them as evidence of "no passthrough" coverage.
// Safe to delete if/when this AIP is next touched.
logic unsigned [22:0] fv_compute_u_gs_0_i;
assign fv_compute_u_gs_0_i = compute_u_gs(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);



///////////////////////////////////////
logic unsigned [22:0] fv_compute_u_ct_0_i;
assign fv_compute_u_ct_0_i = compute_u_ct(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_u_ct_0_intt_passthrough_i;
assign fv_compute_u_ct_0_intt_passthrough_i =
    compute_u_ct(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_1_i;
assign fv_compute_u_ct_1_i = compute_u_ct(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_ct_1_intt_passthrough_i;
assign fv_compute_u_ct_1_intt_passthrough_i =
    compute_u_ct(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_2_i;
assign fv_compute_u_ct_2_i = compute_u_ct(fv_compute_u_ct_0_i, fv_compute_u_ct_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_u_ct_0_mlkem_i;
assign fv_compute_u_ct_0_mlkem_i =
    compute_u_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_u_ct_0_mlkem_intt_passthrough_i;
assign fv_compute_u_ct_0_mlkem_intt_passthrough_i =
    compute_u_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_1_mlkem_i;
assign fv_compute_u_ct_1_mlkem_i =
    compute_u_ct_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_ct_1_mlkem_intt_passthrough_i;
assign fv_compute_u_ct_1_mlkem_intt_passthrough_i =
    compute_u_ct_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_2_mlkem_i;
assign fv_compute_u_ct_2_mlkem_i =
    compute_u_ct_mlkem(fv_compute_u_ct_0_mlkem_i, fv_compute_u_ct_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_0_i;
assign fv_compute_v_ct_0_i = compute_v_ct(fv_compute_u_ct_0_i, fv_compute_u_ct_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_0_mlkem_i;
assign fv_compute_v_ct_0_mlkem_i =
    compute_v_ct_mlkem(fv_compute_u_ct_0_mlkem_i, fv_compute_u_ct_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_ct_1_i;
assign fv_compute_v_ct_1_i = compute_v_ct(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_ct_1_intt_passthrough_i;
assign fv_compute_v_ct_1_intt_passthrough_i =
    compute_v_ct(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_ct_2_i;
assign fv_compute_v_ct_2_i = compute_v_ct(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_ct_2_intt_passthrough_i;
assign fv_compute_v_ct_2_intt_passthrough_i =
    compute_v_ct(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_3_i;
assign fv_compute_u_ct_3_i = compute_u_ct(fv_compute_v_ct_1_i, fv_compute_v_ct_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_1_mlkem_i;
assign fv_compute_v_ct_1_mlkem_i =
    compute_v_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_ct_1_mlkem_intt_passthrough_i;
assign fv_compute_v_ct_1_mlkem_intt_passthrough_i =
    compute_v_ct_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_ct_2_mlkem_i;
assign fv_compute_v_ct_2_mlkem_i =
    compute_v_ct_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_ct_2_mlkem_intt_passthrough_i;
assign fv_compute_v_ct_2_mlkem_intt_passthrough_i =
    compute_v_ct_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_ct_3_mlkem_i;
assign fv_compute_u_ct_3_mlkem_i =
    compute_u_ct_mlkem(fv_compute_v_ct_1_mlkem_i, fv_compute_v_ct_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_3_i;
assign fv_compute_v_ct_3_i = compute_v_ct(fv_compute_v_ct_1_i, fv_compute_v_ct_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_ct_3_mlkem_i;
assign fv_compute_v_ct_3_mlkem_i =
    compute_v_ct_mlkem(fv_compute_v_ct_1_mlkem_i, fv_compute_v_ct_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_u_gs_0_intt_passthrough_i;
assign fv_compute_u_gs_0_intt_passthrough_i =
    compute_u_gs(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_1_i;
assign fv_compute_u_gs_1_i = compute_u_gs(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_gs_1_intt_passthrough_i;
assign fv_compute_u_gs_1_intt_passthrough_i =
    compute_u_gs(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_2_i;
assign fv_compute_u_gs_2_i = compute_u_gs(fv_compute_u_gs_0_i, fv_compute_u_gs_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_u_gs_0_mlkem_i;
assign fv_compute_u_gs_0_mlkem_i =
    compute_u_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_u_gs_0_mlkem_intt_passthrough_i;
assign fv_compute_u_gs_0_mlkem_intt_passthrough_i =
    compute_u_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_1_mlkem_i;
assign fv_compute_u_gs_1_mlkem_i =
    compute_u_gs_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_u_gs_1_mlkem_intt_passthrough_i;
assign fv_compute_u_gs_1_mlkem_intt_passthrough_i =
    compute_u_gs_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_2_mlkem_i;
assign fv_compute_u_gs_2_mlkem_i =
    compute_u_gs_mlkem(fv_compute_u_gs_0_mlkem_i, fv_compute_u_gs_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_0_i;
assign fv_compute_v_gs_0_i = compute_v_gs(fv_compute_u_gs_0_i, fv_compute_u_gs_1_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_0_mlkem_i;
assign fv_compute_v_gs_0_mlkem_i =
    compute_v_gs_mlkem(fv_compute_u_gs_0_mlkem_i, fv_compute_u_gs_1_mlkem_i, pi_uvw_i.w10_i);

logic unsigned [22:0] fv_compute_v_gs_1_i;
assign fv_compute_v_gs_1_i = compute_v_gs(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_gs_1_intt_passthrough_i;
assign fv_compute_v_gs_1_intt_passthrough_i =
    compute_v_gs(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_gs_2_i;
assign fv_compute_v_gs_2_i = compute_v_gs(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_gs_2_intt_passthrough_i;
assign fv_compute_v_gs_2_intt_passthrough_i =
    compute_v_gs(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_3_i;
assign fv_compute_u_gs_3_i = compute_u_gs(fv_compute_v_gs_1_i, fv_compute_v_gs_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_1_mlkem_i;
assign fv_compute_v_gs_1_mlkem_i =
    compute_v_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.v00_i, pi_uvw_i.w00_i);

logic unsigned [22:0] fv_compute_v_gs_1_mlkem_intt_passthrough_i;
assign fv_compute_v_gs_1_mlkem_intt_passthrough_i =
    compute_v_gs_mlkem(pi_uvw_i.u00_i, pi_uvw_i.u01_i, pi_uvw_i.w10_i[11:0]);

logic unsigned [22:0] fv_compute_v_gs_2_mlkem_i;
assign fv_compute_v_gs_2_mlkem_i =
    compute_v_gs_mlkem(pi_uvw_i.u01_i, pi_uvw_i.v01_i, pi_uvw_i.w01_i);

logic unsigned [22:0] fv_compute_v_gs_2_mlkem_intt_passthrough_i;
assign fv_compute_v_gs_2_mlkem_intt_passthrough_i =
    compute_v_gs_mlkem(pi_uvw_i.v00_i, pi_uvw_i.v01_i, pi_uvw_i.w11_i[11:0]);

logic unsigned [22:0] fv_compute_u_gs_3_mlkem_i;
assign fv_compute_u_gs_3_mlkem_i =
    compute_u_gs_mlkem(fv_compute_v_gs_1_mlkem_i, fv_compute_v_gs_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_3_i;
assign fv_compute_v_gs_3_i = compute_v_gs(fv_compute_v_gs_1_i, fv_compute_v_gs_2_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_v_gs_3_mlkem_i;
assign fv_compute_v_gs_3_mlkem_i =
    compute_v_gs_mlkem(fv_compute_v_gs_1_mlkem_i, fv_compute_v_gs_2_mlkem_i, pi_uvw_i.w11_i);

logic unsigned [22:0] fv_compute_pwm_0_i;
assign fv_compute_pwm_0_i =
    compute_pwm(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.v2_i, pi_pw_uvw_i.w2_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_1_i;
assign fv_compute_pwm_1_i =
    compute_pwm(pi_pw_uvw_i.u3_i, pi_pw_uvw_i.v3_i, pi_pw_uvw_i.w3_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_2_i;
assign fv_compute_pwm_2_i =
    compute_pwm(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i, pi_pw_uvw_i.w0_i, pi_accumulate);

logic unsigned [22:0] fv_compute_pwm_3_i;
assign fv_compute_pwm_3_i =
    compute_pwm(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i, pi_pw_uvw_i.w1_i, pi_accumulate);

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

/****************************************************************************/
// PAIRWM-002: independent Karatsuba computation reference model
// Karatsuba0 drives po_pwo_uv_o.uv0/uv1 from pw lanes 0/1 and zeta z0_i.
// Karatsuba1 drives po_pwo_uv_o.uv2/uv3 from pw lanes 2/3 and zeta z1_i.
/****************************************************************************/

// -- Karatsuba0 (lanes 0/1 -> uv0/uv1) --
logic unsigned [22:0] fv_compute_pairwm0_uv00_i;
assign fv_compute_pairwm0_uv00_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.v0_i);

logic unsigned [22:0] fv_compute_pairwm0_uv11_i;
assign fv_compute_pairwm0_uv11_i = compute_pairwm_mult_mlkem(pi_pw_uvw_i.u1_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pairwm0_uvz11_i;
assign fv_compute_pairwm0_uvz11_i =
    compute_pairwm_mult_mlkem(fv_compute_pairwm0_uv11_i, 23'(pi_mlkem_pairwm_zeta13_i.z0_i));

logic unsigned [22:0] fv_compute_pairwm0_uv0_i;
assign fv_compute_pairwm0_uv0_i =
    compute_pwa_mlkem(fv_compute_pairwm0_uvz11_i, fv_compute_pairwm0_uv00_i);

logic unsigned [22:0] fv_compute_pairwm0_addu_i;
assign fv_compute_pairwm0_addu_i = compute_pwa_mlkem(pi_pw_uvw_i.u0_i, pi_pw_uvw_i.u1_i);

logic unsigned [22:0] fv_compute_pairwm0_addv_i;
assign fv_compute_pairwm0_addv_i = compute_pwa_mlkem(pi_pw_uvw_i.v0_i, pi_pw_uvw_i.v1_i);

logic unsigned [22:0] fv_compute_pairwm0_m2_i;
assign fv_compute_pairwm0_m2_i =
    compute_pairwm_mult_mlkem(fv_compute_pairwm0_addu_i, fv_compute_pairwm0_addv_i);

logic unsigned [22:0] fv_compute_pairwm0_sub0_i;
assign fv_compute_pairwm0_sub0_i =
    compute_a_min_b(fv_compute_pairwm0_m2_i, fv_compute_pairwm0_uv00_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm0_uv1_i;
assign fv_compute_pairwm0_uv1_i =
    compute_a_min_b(fv_compute_pairwm0_sub0_i, fv_compute_pairwm0_uv11_i, 1'b1);

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
assign fv_compute_pairwm1_uvz11_i =
    compute_pairwm_mult_mlkem(fv_compute_pairwm1_uv11_i, 23'(pi_mlkem_pairwm_zeta13_i.z1_i));

logic unsigned [22:0] fv_compute_pairwm1_uv0_i;
assign fv_compute_pairwm1_uv0_i =
    compute_pwa_mlkem(fv_compute_pairwm1_uvz11_i, fv_compute_pairwm1_uv00_i);

logic unsigned [22:0] fv_compute_pairwm1_addu_i;
assign fv_compute_pairwm1_addu_i = compute_pwa_mlkem(pi_pw_uvw_i.u2_i, pi_pw_uvw_i.u3_i);

logic unsigned [22:0] fv_compute_pairwm1_addv_i;
assign fv_compute_pairwm1_addv_i = compute_pwa_mlkem(pi_pw_uvw_i.v2_i, pi_pw_uvw_i.v3_i);

logic unsigned [22:0] fv_compute_pairwm1_m2_i;
assign fv_compute_pairwm1_m2_i =
    compute_pairwm_mult_mlkem(fv_compute_pairwm1_addu_i, fv_compute_pairwm1_addv_i);

logic unsigned [22:0] fv_compute_pairwm1_sub0_i;
assign fv_compute_pairwm1_sub0_i =
    compute_a_min_b(fv_compute_pairwm1_m2_i, fv_compute_pairwm1_uv00_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm1_uv1_i;
assign fv_compute_pairwm1_uv1_i =
    compute_a_min_b(fv_compute_pairwm1_sub0_i, fv_compute_pairwm1_uv11_i, 1'b1);

logic unsigned [22:0] fv_compute_pairwm1_uv0_acc_i;
assign fv_compute_pairwm1_uv0_acc_i = compute_pwa_mlkem(fv_compute_pairwm1_uv0_i, pi_pw_uvw_i.w2_i);

logic unsigned [22:0] fv_compute_pairwm1_uv1_acc_i;
assign fv_compute_pairwm1_uv1_acc_i = compute_pwa_mlkem(fv_compute_pairwm1_uv1_i, pi_pw_uvw_i.w3_i);

// Reset property
// When reset is active, all outputs must be 0 at the same cycle
property run_reset_p;
  $past(!pi_reset_n)
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
assert_run_reset: assert property (run_reset_p);

/****************************************************************************/
  // CT MLKEM
/****************************************************************************/

// Intent: outputs match the Cooley-Tukey (forward NTT) butterfly reference, MLDSA mode

property run_CT_p;
  (pi_mode == 3'd0) &&
  !pi_mlkem && pi_enable

|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o &&
  po_uv_o.u20_o == $past(fv_compute_u_ct_2_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_ct_0_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_ct_3_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_ct_3_i, BF_LATENCY);
endproperty
assert_run_ct: assert property (disable iff(!pi_reset_n | pi_zeroize) run_CT_p);




// Intent: outputs match the Cooley-Tukey butterfly reference, MLKEM mode
property run_CT_mlkem_p;
  (pi_mode == 3'd0) &&
  pi_mlkem &&
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




// Intent: outputs match the pointwise-multiply (PWM) reference, no accumulate, MLDSA mode
property run_PWM_p;
  (pi_mode == 3'd2) &&
  !pi_accumulate &&
  !pi_mlkem &&
  pi_enable

|->
  ##(PWM_LATENCY-1)
  po_pwo_uv_o.uv0 == $past(fv_compute_pwm_2_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwm_3_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwm_0_i, (PWM_LATENCY-1)) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwm_1_i, (PWM_LATENCY-1)) &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwm: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWM_p);

// Intent: outputs match the PWM reference with accumulate enabled, MLDSA mode
property run_PWMA_p;
  (pi_mode == 3'd2) &&
  pi_accumulate &&
  !pi_mlkem &&
  pi_enable

|->
  ##PWM_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pwm_2_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwm_3_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwm_0_i, PWM_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwm_1_i, PWM_LATENCY) &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 && //modified design
  po_uv_o.u21_o == 23'd0 && //modified design
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwma: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWMA_p);




// Intent: outputs match the Gentleman-Sande (inverse NTT) butterfly reference, MLDSA mode
property run_GS_p;
  (pi_mode == 3'd1) &&
  !pi_mlkem &&
  pi_enable

|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o &&
  po_uv_o.u20_o == $past(fv_compute_u_gs_2_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_gs_3_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_gs_0_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_gs_3_i, BF_LATENCY);
endproperty
assert_run_gs: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_p);


// Intent: outputs match the Gentleman-Sande butterfly reference, MLKEM mode
property run_GS_mlkem_p;
  (pi_mode == 3'd1) &&
  pi_mlkem &&
  pi_enable

|->
  ##BF_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o &&
  po_uv_o.u20_o == $past(fv_compute_u_gs_2_mlkem_i, BF_LATENCY) &&
  po_uv_o.u21_o == $past(fv_compute_u_gs_3_mlkem_i, BF_LATENCY) &&
  po_uv_o.v20_o == $past(fv_compute_v_gs_0_mlkem_i, BF_LATENCY) &&
  po_uv_o.v21_o == $past(fv_compute_v_gs_3_mlkem_i, BF_LATENCY)
  ;
endproperty
assert_run_gs_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_GS_mlkem_p);


// Intent: outputs match the pointwise-add (PWA) reference, MLDSA mode
property run_PWA_p;
  (pi_mode == 3'd3) &&
  !pi_mlkem &&
  pi_enable

|->
  ##PWA_LATENCY    //for pwa/pws enable comes out in 1 cycle
  po_pwo_uv_o.uv0 == $past(fv_compute_pwa_2_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pwa_3_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pwa_0_i, PWA_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pwa_1_i, PWA_LATENCY) &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwa: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_p);


// Intent: pwo outputs stay 0 in MLKEM PWA mode (non-pairwm modes carry no pairwm result)
// pwo outputs are 0: in MLKEM non-pairwm modes, pairwm_mul_red_o=0 → Karatsuba=0
// → pwo_uv_o is routed from pairwm_uv_o which evaluates to 0.
property run_PWA_mlkem_p;
  (pi_mode == 3'd3) &&
  pi_mlkem &&
  pi_enable
|->
  ##PWA_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pwa_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWA_mlkem_p);


// Intent: outputs match the pointwise-subtract (PWS) reference, MLDSA mode
property run_PWS_p;
  (pi_mode == 3'd4) &&
  !pi_mlkem &&
  pi_enable
|->
  ##PWS_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pws_2_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pws_3_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pws_0_i, PWS_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pws_1_i, PWS_LATENCY) &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pws: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_p);

// Intent: pwo outputs stay 0 in MLKEM PWS mode (non-pairwm modes carry no pairwm result)
// pwo outputs are 0: in MLKEM non-pairwm modes, pairwm_mul_red_o=0 → Karatsuba=0
// → pwo_uv_o is routed from pairwm_uv_o which evaluates to 0.
property run_PWS_mlkem_p;
  (pi_mode == 3'd4) &&
  pi_mlkem &&
  pi_enable
|->
  ##PWS_LATENCY
  po_pwo_uv_o.uv0 == 23'd0 &&
  po_pwo_uv_o.uv1 == 23'd0 &&
  po_pwo_uv_o.uv2 == 23'd0 &&
  po_pwo_uv_o.uv3 == 23'd0 &&
  po_ready_o &&
  po_uv_o.u20_o == 23'd0 &&
  po_uv_o.u21_o == 23'd0 &&
  po_uv_o.v20_o == 23'd0 &&
  po_uv_o.v21_o == 23'd0;
endproperty
assert_run_pws_mlkem: assert property (disable iff(!pi_reset_n | pi_zeroize) run_PWS_mlkem_p);


// Intent: pairwm-mode outputs mirror the RTL's own pairwm_uv01_o/uv23_o, ready after latency
property run_pairwm_p;
  (pi_mode == 3'd5) &&
  !pi_accumulate &&
  pi_mlkem &&
  pi_enable
|->
  po_pwo_uv_o.uv0 == ntt_butterfly2x2.pairwm_uv01_o.uv0_o &&
  po_pwo_uv_o.uv1 == ntt_butterfly2x2.pairwm_uv01_o.uv1_o &&
  po_pwo_uv_o.uv2 == ntt_butterfly2x2.pairwm_uv23_o.uv0_o &&
  po_pwo_uv_o.uv3 == ntt_butterfly2x2.pairwm_uv23_o.uv1_o

  ##(MLKEM_PAIRWM_LATENCY)
  po_ready_o
  ;
endproperty
assert_run_pairwm: assert property (disable iff(!pi_reset_n | pi_zeroize) run_pairwm_p);

// Intent: ready asserts after MLKEM_PAIRWM_ACC_LATENCY in pairwm accumulate mode
property run_pairwm_accumulate_p;
  (pi_mode == 3'd5) &&
  pi_accumulate &&
  pi_mlkem &&
  pi_enable
|->
  ##MLKEM_PAIRWM_ACC_LATENCY
  po_ready_o;
endproperty
assert_run_pairwm_accumulate: assert property (
  disable iff (!pi_reset_n | pi_zeroize) run_pairwm_accumulate_p);

// Intent: pairwm outputs match an independent Karatsuba reference model, no accumulate
property run_pairwm_computation_p;
  (pi_mode == 3'd5) &&
  !pi_accumulate &&
  pi_mlkem &&
  pi_enable
|->
  ##MLKEM_PAIRWM_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pairwm0_uv0_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pairwm0_uv1_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pairwm1_uv0_i, MLKEM_PAIRWM_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pairwm1_uv1_i, MLKEM_PAIRWM_LATENCY);
endproperty
assert_run_pairwm_computation: assert property (
  disable iff (!pi_reset_n | pi_zeroize) run_pairwm_computation_p);

// Intent: pairwm outputs match the independent Karatsuba reference, accumulate enabled
property run_pairwm_accumulate_computation_p;
  (pi_mode == 3'd5) &&
  pi_accumulate &&
  pi_mlkem &&
  pi_enable
|->
  ##MLKEM_PAIRWM_ACC_LATENCY
  po_pwo_uv_o.uv0 == $past(fv_compute_pairwm0_uv0_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv1 == $past(fv_compute_pairwm0_uv1_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv2 == $past(fv_compute_pairwm1_uv0_acc_i, MLKEM_PAIRWM_ACC_LATENCY) &&
  po_pwo_uv_o.uv3 == $past(fv_compute_pairwm1_uv1_acc_i, MLKEM_PAIRWM_ACC_LATENCY);
endproperty
assert_run_pairwm_accumulate_computation: assert property (
  disable iff (!pi_reset_n | pi_zeroize) run_pairwm_accumulate_computation_p);



// --------------------------------------------------------------------------
// 1. Mode decode
// --------------------------------------------------------------------------

// Intent: pwo_mode is asserted for pwm/pwa/pws mode encodings, cleared otherwise
property wb_pwo_mode_decode_p;
  ntt_butterfly2x2.pwo_mode ==
    ((pi_mode == 3'd2) || (pi_mode == 3'd3) || (pi_mode == 3'd4));
endproperty
assert_wb_pwo_mode_decode: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_mode_decode_p);

// Intent: pairwm_mode is asserted only for MLKEM pairwm mode
property wb_pairwm_mode_decode_p;
  ntt_butterfly2x2.pairwm_mode == (pi_mlkem && (pi_mode == 3'd5));
endproperty
assert_wb_pairwm_mode_decode: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_mode_decode_p);

// --------------------------------------------------------------------------
// 2. Stage-1 input mux — NTT/GS mode: bf_inst00 and bf_inst01 from uvw_i
// --------------------------------------------------------------------------

// Intent: bf_inst00 opu_i input mux in NTT/GS mode
property wb_bf00_ntt_opu_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opu_i == pi_uvw_i.u00_i;
endproperty
assert_wb_bf00_ntt_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opu_p);

// Intent: bf_inst00 opv_i input mux in NTT/GS mode
property wb_bf00_ntt_opv_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opv_i == pi_uvw_i.v00_i;
endproperty
assert_wb_bf00_ntt_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opv_p);

// Intent: bf_inst00 opw_i input mux in NTT/GS mode
property wb_bf00_ntt_opw_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opw_i == pi_uvw_i.w00_i;
endproperty
assert_wb_bf00_ntt_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_ntt_opw_p);

// Intent: bf_inst01 opu_i input mux in NTT/GS mode
property wb_bf01_ntt_opu_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opu_i == pi_uvw_i.u01_i;
endproperty
assert_wb_bf01_ntt_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opu_p);

// Intent: bf_inst01 opv_i input mux in NTT/GS mode
property wb_bf01_ntt_opv_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opv_i == pi_uvw_i.v01_i;
endproperty
assert_wb_bf01_ntt_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opv_p);

// Intent: bf_inst01 opw_i input mux in NTT/GS mode
property wb_bf01_ntt_opw_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opw_i == pi_uvw_i.w01_i;
endproperty
assert_wb_bf01_ntt_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_ntt_opw_p);

// --------------------------------------------------------------------------
// 3. Stage-1 input mux — PWO/pairwm mode: bf_inst00/01 from pw_uvw_i lanes 0/1
// --------------------------------------------------------------------------

// Intent: bf_inst00 opu_i input mux in PWO/pairwm mode
property wb_bf00_pwo_opu_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opu_i == pi_pw_uvw_i.u0_i;
endproperty
assert_wb_bf00_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opu_p);

// Intent: bf_inst00 opv_i input mux in PWO/pairwm mode
property wb_bf00_pwo_opv_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opv_i == pi_pw_uvw_i.v0_i;
endproperty
assert_wb_bf00_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opv_p);

// Intent: bf_inst00 opw_i input mux in PWO/pairwm mode
property wb_bf00_pwo_opw_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst00.opw_i == pi_pw_uvw_i.w0_i;
endproperty
assert_wb_bf00_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf00_pwo_opw_p);

// Intent: bf_inst01 opu_i input mux in PWO/pairwm mode
property wb_bf01_pwo_opu_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opu_i == pi_pw_uvw_i.u1_i;
endproperty
assert_wb_bf01_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opu_p);

// Intent: bf_inst01 opv_i input mux in PWO/pairwm mode
property wb_bf01_pwo_opv_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opv_i == pi_pw_uvw_i.v1_i;
endproperty
assert_wb_bf01_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opv_p);

// Intent: bf_inst01 opw_i input mux in PWO/pairwm mode
property wb_bf01_pwo_opw_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst01.opw_i == pi_pw_uvw_i.w1_i;
endproperty
assert_wb_bf01_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf01_pwo_opw_p);

// --------------------------------------------------------------------------
// 4. Stage-2 input mux — PWO/pairwm mode: bf_inst10/11 from pw_uvw_i lanes 2/3
// --------------------------------------------------------------------------

// Intent: bf_inst10 opu_i input mux in PWO/pairwm mode
property wb_bf10_pwo_opu_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst10.opu_i == pi_pw_uvw_i.u2_i;
endproperty
assert_wb_bf10_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_pwo_opu_p);

// Intent: bf_inst10 opv_i input mux in PWO/pairwm mode
property wb_bf10_pwo_opv_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst10.opv_i == pi_pw_uvw_i.v2_i;
endproperty
assert_wb_bf10_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_pwo_opv_p);

// Intent: bf_inst10 opw_i input mux in PWO/pairwm mode
property wb_bf10_pwo_opw_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst10.opw_i == pi_pw_uvw_i.w2_i;
endproperty
assert_wb_bf10_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_pwo_opw_p);

// Intent: bf_inst11 opu_i input mux in PWO/pairwm mode
property wb_bf11_pwo_opu_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst11.opu_i == pi_pw_uvw_i.u3_i;
endproperty
assert_wb_bf11_pwo_opu: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_pwo_opu_p);

// Intent: bf_inst11 opv_i input mux in PWO/pairwm mode
property wb_bf11_pwo_opv_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst11.opv_i == pi_pw_uvw_i.v3_i;
endproperty
assert_wb_bf11_pwo_opv: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_pwo_opv_p);

// Intent: bf_inst11 opw_i input mux in PWO/pairwm mode
property wb_bf11_pwo_opw_p;
  (ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst11.opw_i == pi_pw_uvw_i.w3_i;
endproperty
assert_wb_bf11_pwo_opw: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_pwo_opw_p);

// Intent: the stage-1 to stage-2 crossbar wiring for u10
property wb_crossbar_u10_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst10.opu_i == ntt_butterfly2x2.bf_inst00.u_o;
endproperty
assert_wb_crossbar_u10: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_crossbar_u10_p);

// Intent: the stage-1 to stage-2 crossbar wiring for v10
property wb_crossbar_v10_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst10.opv_i == ntt_butterfly2x2.bf_inst01.u_o;
endproperty
assert_wb_crossbar_v10: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_crossbar_v10_p);

// Intent: the stage-1 to stage-2 crossbar wiring for u11
property wb_crossbar_u11_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst11.opu_i == ntt_butterfly2x2.bf_inst00.v_o;
endproperty
assert_wb_crossbar_u11: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_crossbar_u11_p);

// Intent: the stage-1 to stage-2 crossbar wiring for v11
property wb_crossbar_v11_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode)
|->
  ntt_butterfly2x2.bf_inst11.opv_i == ntt_butterfly2x2.bf_inst01.v_o;
endproperty
assert_wb_crossbar_v11: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_crossbar_v11_p);

// --------------------------------------------------------------------------
// 6. Stage-2 twiddle input mux (NTT/GS mode)
// MLDSA: bf_inst10.opw_i ← mldsa_w10_reg[0]
// bf_inst11.opw_i ← mldsa_w11_reg[0]
// MLKEM: bf_inst10.opw_i ← mlkem_w10_reg[0]
// bf_inst11.opw_i ← mlkem_w11_reg[0]
// --------------------------------------------------------------------------

// Intent: bf_inst10 twiddle input mux in MLDSA mode
property wb_bf10_twiddle_mldsa_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode) && !pi_mlkem
|->
  ntt_butterfly2x2.bf_inst10.opw_i == ntt_butterfly2x2.mldsa_w10_reg[0];
endproperty
assert_wb_bf10_twiddle_mldsa: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_twiddle_mldsa_p);

// Intent: bf_inst11 twiddle input mux in MLDSA mode
property wb_bf11_twiddle_mldsa_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode) && !pi_mlkem
|->
  ntt_butterfly2x2.bf_inst11.opw_i == ntt_butterfly2x2.mldsa_w11_reg[0];
endproperty
assert_wb_bf11_twiddle_mldsa: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_twiddle_mldsa_p);

// Intent: bf_inst10 twiddle input mux in MLKEM mode
property wb_bf10_twiddle_mlkem_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode) && pi_mlkem
|->
  ntt_butterfly2x2.bf_inst10.opw_i == ntt_butterfly2x2.mlkem_w10_reg[0];
endproperty
assert_wb_bf10_twiddle_mlkem: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf10_twiddle_mlkem_p);

// Intent: bf_inst11 twiddle input mux in MLKEM mode
property wb_bf11_twiddle_mlkem_p;
  !(ntt_butterfly2x2.pwo_mode || ntt_butterfly2x2.pairwm_mode) && pi_mlkem
|->
  ntt_butterfly2x2.bf_inst11.opw_i == ntt_butterfly2x2.mlkem_w11_reg[0];
endproperty
assert_wb_bf11_twiddle_mlkem: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_bf11_twiddle_mlkem_p);

// --------------------------------------------------------------------------
// 7. Twiddle shift-register load and propagation
// The shift is: reg <= {new_val, reg[LATENCY-1:1]}
// So index [LATENCY-1] captures the new input each cycle,
// and it ripples down to index [0] after LATENCY cycles.
// --------------------------------------------------------------------------

// Intent: mlkem_w10_reg load captures w10_i on the next posedge
property wb_mlkem_w10_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(pi_uvw_i.w10_i[MLKEM_REG_SIZE-1:0]);
endproperty
assert_wb_mlkem_w10_reg_load: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w10_reg_load_p);

// Intent: mlkem_w11_reg load captures w11_i on the next posedge
property wb_mlkem_w11_reg_load_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-1] ==
    $past(pi_uvw_i.w11_i[MLKEM_REG_SIZE-1:0]);
endproperty
assert_wb_mlkem_w11_reg_load: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w11_reg_load_p);

// Intent: mldsa_w10_reg shift propagation by one position per cycle
property wb_mldsa_w10_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mldsa_w10_reg[BF_STAGE1_LATENCY-2] ==
    $past(ntt_butterfly2x2.mldsa_w10_reg[BF_STAGE1_LATENCY-1]) &&
  ntt_butterfly2x2.mldsa_w10_reg[0] ==
    $past(ntt_butterfly2x2.mldsa_w10_reg[1]);
endproperty
assert_wb_mldsa_w10_reg_propagate: assert property (
  disable iff (!pi_reset_n) wb_mldsa_w10_reg_propagate_p);

// Intent: mldsa_w11_reg shift propagation by one position per cycle
property wb_mldsa_w11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mldsa_w11_reg[BF_STAGE1_LATENCY-2] ==
    $past(ntt_butterfly2x2.mldsa_w11_reg[BF_STAGE1_LATENCY-1]) &&
  ntt_butterfly2x2.mldsa_w11_reg[0] ==
    $past(ntt_butterfly2x2.mldsa_w11_reg[1]);
endproperty
assert_wb_mldsa_w11_reg_propagate: assert property (
  disable iff (!pi_reset_n) wb_mldsa_w11_reg_propagate_p);

// Intent: mlkem_w10_reg shift propagation by one position per cycle
property wb_mlkem_w10_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-2] ==
    $past(ntt_butterfly2x2.mlkem_w10_reg[MLKEM_BF_STAGE1_LATENCY-1]) &&
  ntt_butterfly2x2.mlkem_w10_reg[0] ==
    $past(ntt_butterfly2x2.mlkem_w10_reg[1]);
endproperty
assert_wb_mlkem_w10_reg_propagate: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w10_reg_propagate_p);

// Intent: mlkem_w11_reg shift propagation by one position per cycle
property wb_mlkem_w11_reg_propagate_p;
  pi_reset_n && !pi_zeroize
|=>
  ntt_butterfly2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-2] ==
    $past(ntt_butterfly2x2.mlkem_w11_reg[MLKEM_BF_STAGE1_LATENCY-1]) &&
  ntt_butterfly2x2.mlkem_w11_reg[0] ==
    $past(ntt_butterfly2x2.mlkem_w11_reg[1]);
endproperty
assert_wb_mlkem_w11_reg_propagate: assert property (
  disable iff (!pi_reset_n) wb_mlkem_w11_reg_propagate_p);

// --------------------------------------------------------------------------
// 8. Twiddle shift-registers cleared by reset and by zeroize
// --------------------------------------------------------------------------

// Intent: the twiddle shift-registers are cleared by reset
property wb_twiddle_reg_reset_p;
  $past(!pi_reset_n)
|->
  ntt_butterfly2x2.mldsa_w10_reg == '0 &&
  ntt_butterfly2x2.mldsa_w11_reg == '0 &&
  ntt_butterfly2x2.mlkem_w10_reg == '0 &&
  ntt_butterfly2x2.mlkem_w11_reg == '0;
endproperty
assert_wb_twiddle_reg_reset: assert property (wb_twiddle_reg_reset_p);

// --------------------------------------------------------------------------
// 9. Stage-2 output wiring to po_uv_o
// bf_inst10.u_o → uv_o.u20_o → po_uv_o.u20_o
// bf_inst10.v_o → uv_o.v20_o → po_uv_o.v20_o
// bf_inst11.u_o → uv_o.u21_o → po_uv_o.u21_o
// bf_inst11.v_o → uv_o.v21_o → po_uv_o.v21_o
// --------------------------------------------------------------------------

// Intent: stage-2 output wiring to po_uv_o.u20_o
property wb_stage2_u20_p;
  po_uv_o.u20_o == ntt_butterfly2x2.bf_inst10.u_o;
endproperty
assert_wb_stage2_u20: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_stage2_u20_p);

// Intent: stage-2 output wiring to po_uv_o.v20_o
property wb_stage2_v20_p;
  po_uv_o.v20_o == ntt_butterfly2x2.bf_inst10.v_o;
endproperty
assert_wb_stage2_v20: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_stage2_v20_p);

// Intent: stage-2 output wiring to po_uv_o.u21_o
property wb_stage2_u21_p;
  po_uv_o.u21_o == ntt_butterfly2x2.bf_inst11.u_o;
endproperty
assert_wb_stage2_u21: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_stage2_u21_p);

// Intent: stage-2 output wiring to po_uv_o.v21_o
property wb_stage2_v21_p;
  po_uv_o.v21_o == ntt_butterfly2x2.bf_inst11.v_o;
endproperty
assert_wb_stage2_v21: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_stage2_v21_p);

// --------------------------------------------------------------------------
// 10. MLDSA PWO collection: bf pwm_res_o → mldsa_pwo_uv_o lanes
// --------------------------------------------------------------------------

// Intent: MLDSA PWO collection into mldsa_pwo_uv_o.uv0
property wb_mldsa_pwo_uv0_p;
  ntt_butterfly2x2.mldsa_pwo_uv_o.uv0 == ntt_butterfly2x2.bf_inst00.pwm_res_o;
endproperty
assert_wb_mldsa_pwo_uv0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_pwo_uv0_p);

// Intent: MLDSA PWO collection into mldsa_pwo_uv_o.uv1
property wb_mldsa_pwo_uv1_p;
  ntt_butterfly2x2.mldsa_pwo_uv_o.uv1 == ntt_butterfly2x2.bf_inst01.pwm_res_o;
endproperty
assert_wb_mldsa_pwo_uv1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_pwo_uv1_p);

// Intent: MLDSA PWO collection into mldsa_pwo_uv_o.uv2
property wb_mldsa_pwo_uv2_p;
  ntt_butterfly2x2.mldsa_pwo_uv_o.uv2 == ntt_butterfly2x2.bf_inst10.pwm_res_o;
endproperty
assert_wb_mldsa_pwo_uv2: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_pwo_uv2_p);

// Intent: MLDSA PWO collection into mldsa_pwo_uv_o.uv3
property wb_mldsa_pwo_uv3_p;
  ntt_butterfly2x2.mldsa_pwo_uv_o.uv3 == ntt_butterfly2x2.bf_inst11.pwm_res_o;
endproperty
assert_wb_mldsa_pwo_uv3: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_mldsa_pwo_uv3_p);

// --------------------------------------------------------------------------
// 11. Final PWO output mux: MLKEM → pairwm outputs, MLDSA → mldsa_pwo
// --------------------------------------------------------------------------

// Intent: the final PWO output mux for po_pwo_uv_o.uv0
property wb_pwo_out_uv0_mux_p;
  po_pwo_uv_o.uv0 == (pi_mlkem ?
    ntt_butterfly2x2.pairwm_uv01_o.uv0_o : ntt_butterfly2x2.mldsa_pwo_uv_o.uv0);
endproperty
assert_wb_pwo_out_uv0_mux: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_out_uv0_mux_p);

// Intent: the final PWO output mux for po_pwo_uv_o.uv1
property wb_pwo_out_uv1_mux_p;
  po_pwo_uv_o.uv1 == (pi_mlkem ?
    ntt_butterfly2x2.pairwm_uv01_o.uv1_o : ntt_butterfly2x2.mldsa_pwo_uv_o.uv1);
endproperty
assert_wb_pwo_out_uv1_mux: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_out_uv1_mux_p);

// Intent: the final PWO output mux for po_pwo_uv_o.uv2
property wb_pwo_out_uv2_mux_p;
  po_pwo_uv_o.uv2 == (pi_mlkem ?
    ntt_butterfly2x2.pairwm_uv23_o.uv0_o : ntt_butterfly2x2.mldsa_pwo_uv_o.uv2);
endproperty
assert_wb_pwo_out_uv2_mux: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_out_uv2_mux_p);

// Intent: the final PWO output mux for po_pwo_uv_o.uv3
property wb_pwo_out_uv3_mux_p;
  po_pwo_uv_o.uv3 == (pi_mlkem ?
    ntt_butterfly2x2.pairwm_uv23_o.uv1_o : ntt_butterfly2x2.mldsa_pwo_uv_o.uv3);
endproperty
assert_wb_pwo_out_uv3_mux: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pwo_out_uv3_mux_p);

// --------------------------------------------------------------------------
// 12. Karatsuba pairwm input wiring (active only in pairwm mode)
// pairwm_uvw01_i ← pw_uvw_i lanes 0/1  (truncated to MLKEM_REG_SIZE)
// pairwm_uvw23_i ← pw_uvw_i lanes 2/3  (truncated to MLKEM_REG_SIZE)
// --------------------------------------------------------------------------

// Intent: Karatsuba pairwm_uvw01_i.u0_i input wiring
property wb_pairwm_uvw01_u0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.u0_i == pi_pw_uvw_i.u0_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_u0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_u0_p);

// Intent: Karatsuba pairwm_uvw01_i.v0_i input wiring
property wb_pairwm_uvw01_v0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.v0_i == pi_pw_uvw_i.v0_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_v0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_v0_p);

// Intent: Karatsuba pairwm_uvw01_i.w0_i input wiring
property wb_pairwm_uvw01_w0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.w0_i == pi_pw_uvw_i.w0_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_w0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_w0_p);

// Intent: Karatsuba pairwm_uvw01_i.u1_i input wiring
property wb_pairwm_uvw01_u1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.u1_i == pi_pw_uvw_i.u1_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_u1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_u1_p);

// Intent: Karatsuba pairwm_uvw01_i.v1_i input wiring
property wb_pairwm_uvw01_v1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.v1_i == pi_pw_uvw_i.v1_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_v1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_v1_p);

// Intent: Karatsuba pairwm_uvw01_i.w1_i input wiring
property wb_pairwm_uvw01_w1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw01_i.w1_i == pi_pw_uvw_i.w1_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw01_w1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_w1_p);

// Intent: Karatsuba pairwm_uvw23_i.u0_i input wiring
property wb_pairwm_uvw23_u0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.u0_i == pi_pw_uvw_i.u2_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_u0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_u0_p);

// Intent: Karatsuba pairwm_uvw23_i.v0_i input wiring
property wb_pairwm_uvw23_v0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.v0_i == pi_pw_uvw_i.v2_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_v0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_v0_p);

// Intent: Karatsuba pairwm_uvw23_i.w0_i input wiring
property wb_pairwm_uvw23_w0_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.w0_i == pi_pw_uvw_i.w2_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_w0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_w0_p);

// Intent: Karatsuba pairwm_uvw23_i.u1_i input wiring
property wb_pairwm_uvw23_u1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.u1_i == pi_pw_uvw_i.u3_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_u1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_u1_p);

// Intent: Karatsuba pairwm_uvw23_i.v1_i input wiring
property wb_pairwm_uvw23_v1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.v1_i == pi_pw_uvw_i.v3_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_v1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_v1_p);

// Intent: Karatsuba pairwm_uvw23_i.w1_i input wiring
property wb_pairwm_uvw23_w1_p;
  pi_mlkem && (pi_mode == 3'd5)
|->
  ntt_butterfly2x2.pairwm_uvw23_i.w1_i == pi_pw_uvw_i.w3_i[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_pairwm_uvw23_w1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_w1_p);

// --------------------------------------------------------------------------
// 13. Karatsuba pairwm structs forced to zero when not in pairwm mode
// --------------------------------------------------------------------------

// Intent: pairwm_uvw01_i is forced to zero outside pairwm mode
property wb_pairwm_uvw01_zero_p;
  !(pi_mlkem && (pi_mode == 3'd5))
|->
  ntt_butterfly2x2.pairwm_uvw01_i == '0;
endproperty
assert_wb_pairwm_uvw01_zero: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw01_zero_p);

// Intent: pairwm_uvw23_i is forced to zero outside pairwm mode
property wb_pairwm_uvw23_zero_p;
  !(pi_mlkem && (pi_mode == 3'd5))
|->
  ntt_butterfly2x2.pairwm_uvw23_i == '0;
endproperty
assert_wb_pairwm_uvw23_zero: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_pairwm_uvw23_zero_p);

// --------------------------------------------------------------------------
// 14. Karatsuba m0/m1 tap connections from bf *_pairwm_mul_red_o
// mlkem_pawm_inst0: m0 ← bf00_pairwm_mul_red[MLKEM_REG_SIZE-1:0]
// m1 ← bf01_pairwm_mul_red[MLKEM_REG_SIZE-1:0]
// mlkem_pawm_inst1: m0 ← bf10_pairwm_mul_red[MLKEM_REG_SIZE-1:0]
// m1 ← bf11_pairwm_mul_red[MLKEM_REG_SIZE-1:0]
// --------------------------------------------------------------------------

// Intent: Karatsuba mlkem_pawm_inst0 m0_red_i tap connection
property wb_karatsuba0_m0_p;
  ntt_butterfly2x2.mlkem_pawm_inst0.m0_red_i ==
    ntt_butterfly2x2.bf00_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba0_m0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba0_m0_p);

// Intent: Karatsuba mlkem_pawm_inst0 m1_red_i tap connection
property wb_karatsuba0_m1_p;
  ntt_butterfly2x2.mlkem_pawm_inst0.m1_red_i ==
    ntt_butterfly2x2.bf01_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba0_m1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba0_m1_p);

// Intent: Karatsuba mlkem_pawm_inst1 m0_red_i tap connection
property wb_karatsuba1_m0_p;
  ntt_butterfly2x2.mlkem_pawm_inst1.m0_red_i ==
    ntt_butterfly2x2.bf10_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba1_m0: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba1_m0_p);

// Intent: Karatsuba mlkem_pawm_inst1 m1_red_i tap connection
property wb_karatsuba1_m1_p;
  ntt_butterfly2x2.mlkem_pawm_inst1.m1_red_i ==
    ntt_butterfly2x2.bf11_pairwm_mul_red[MLKEM_REG_SIZE-1:0];
endproperty
assert_wb_karatsuba1_m1: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba1_m1_p);

// --------------------------------------------------------------------------
// 15. Karatsuba zeta connections
// mlkem_pawm_inst0.pwo_z_i ← mlkem_pairwm_zeta13_i.z0_i
// mlkem_pawm_inst1.pwo_z_i ← mlkem_pairwm_zeta13_i.z1_i
// --------------------------------------------------------------------------

// Intent: Karatsuba mlkem_pawm_inst0 zeta connection
property wb_karatsuba0_zeta_p;
  ntt_butterfly2x2.mlkem_pawm_inst0.pwo_z_i == pi_mlkem_pairwm_zeta13_i.z0_i;
endproperty
assert_wb_karatsuba0_zeta: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba0_zeta_p);

// Intent: Karatsuba mlkem_pawm_inst1 zeta connection
property wb_karatsuba1_zeta_p;
  ntt_butterfly2x2.mlkem_pawm_inst1.pwo_z_i == pi_mlkem_pairwm_zeta13_i.z1_i;
endproperty
assert_wb_karatsuba1_zeta: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_karatsuba1_zeta_p);

// --------------------------------------------------------------------------
// 16. ready_o is directly driven from ready_reg[0]
// --------------------------------------------------------------------------

// Intent: po_ready_o is directly driven from ready_reg[0]
property wb_ready_o_p;
  po_ready_o == ntt_butterfly2x2.ready_reg[0];
endproperty
assert_wb_ready_o: assert property (
  disable iff (!pi_reset_n | pi_zeroize) wb_ready_o_p);

// Intent: ready_reg clears when pi_mode takes an undefined encoding (UNDEF-001)
property undef_mode_ready_p;
  pi_reset_n && !pi_zeroize &&
  !(pi_mode inside {3'd0, 3'd1, 3'd2, 3'd3, 3'd4, 3'd5})
|=>
  ntt_butterfly2x2.ready_reg == '0;
endproperty
assert_undef_mode_ready: assert property (disable iff (!pi_reset_n) undef_mode_ready_p);


endmodule

