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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+
//
// Connectivity checking for ntt_butterfly.
//
// Organised in four groups:
//   1. Input pipeline register connectivity   (u_reg, w_reg, add_res delay chain)
//   2. Multiplier input mux connectivity       (mul_opa / mul_opb per mode)
//   3. Adder input mux connectivity            (add_opa / add_opb per mode)
//   4. Output mux connectivity                 (u_o / v_o / pwm_res_o / pairwm_mul_red_o per mode)


import ntt_defines_pkg::*;
import fv_ntt_butterfly_functions::*;


module fv_ntt_butterfly_conn_m (
  input logic        rst_n,
  input logic        clk,

  // Primary inputs
  input logic unsigned [22:0] opu_i,
  input logic unsigned [22:0] opv_i,
  input logic unsigned [22:0] opw_i,
  input logic unsigned [2:0]  mode,
  input logic unsigned [0:0]  accumulate,
  input logic unsigned [0:0]  mlkem,

  // Primary outputs
  input logic unsigned [22:0] u_o,
  input logic unsigned [22:0] v_o,
  input logic unsigned [22:0] pwm_res_o,
  input logic unsigned [22:0] pairwm_mul_red_o,

  // Input pipeline registers
  input logic unsigned [22:0] u_reg,
  input logic unsigned [22:0] u_reg_d2,
  input logic unsigned [22:0] w_reg,
  input logic unsigned [22:0] w_reg_d2,

  // Adder pipeline
  input logic unsigned [22:0] add_res,
  input logic unsigned [22:0] add_res_d1,
  input logic unsigned [22:0] add_res_d2,

  // Muxed operator inputs
  input logic unsigned [22:0] mul_opa,
  input logic unsigned [22:0] mul_opb,
  input logic unsigned [22:0] add_opa,
  input logic unsigned [22:0] add_opb,

  // Subtracter outputs
  input logic unsigned [22:0] sub_res,
  input logic unsigned [22:0] u_minus_v,

  // Multiplication pipeline (internal)
  input logic unsigned [45:0] mul_res,
  input logic unsigned [23:0] mul_res_reg,
  input logic unsigned [45:0] mldsa_mul_res_reg,
  input logic unsigned [11:0] mlkem_mul_res_reduced,
  input logic unsigned [22:0] mldsa_mul_res_reduced_comb,
  input logic unsigned [11:0] mlkem_mul_res_reduced_reg,
  input logic unsigned [22:0] mldsa_mul_res_reduced
);


default clocking default_clk @(posedge clk); endclocking


// ---------------------------------------------------------------------------
// Local convenience expressions for div2 outputs (not separately exposed).
// These mirror the RTL instances mldsa_div2_inst_0 / mlkem_div2_inst_0/2.
// ---------------------------------------------------------------------------

// mldsa_add_res_div2  (input to u_o mux in GS for MLDSA)
logic unsigned [22:0] fv_gs_u_o_mldsa;
assign fv_gs_u_o_mldsa = div2(add_res_d2, 1'b0);

// mlkem_add_res_div2  (input to u_o mux in GS for MLKEM, 12-bit div2)
logic unsigned [22:0] fv_gs_u_o_mlkem;
assign fv_gs_u_o_mlkem = 23'(add_res_d2[0]
                          ? (add_res_d2[11:0] >> 1) + 12'd1665
                          : add_res_d2[11:0] >> 1);

// mldsa_u_minus_v_div2 (mul_opa source in GS for MLDSA)
logic unsigned [22:0] fv_gs_mul_opa_mldsa;
assign fv_gs_mul_opa_mldsa = div2(u_minus_v, 1'b0);

// mlkem_u_minus_v_div2 (mul_opa source in GS for MLKEM, 12-bit div2)
logic unsigned [22:0] fv_gs_mul_opa_mlkem;
assign fv_gs_mul_opa_mlkem = 23'(u_minus_v[0]
                              ? (u_minus_v[11:0] >> 1) + 12'd1665
                              : u_minus_v[11:0] >> 1);

// Mode decode
logic fv_ct, fv_gs, fv_pwm, fv_pwa, fv_pws, fv_pairwm;
assign fv_ct      = (mode == 3'd0);
assign fv_gs      = (mode == 3'd1);
assign fv_pwm     = (mode == 3'd2);
assign fv_pwa     = (mode == 3'd3);
assign fv_pws     = (mode == 3'd4);
assign fv_pairwm  = (mode == 3'd5);


// ===========================================================================
// Group 1 — Input pipeline register connectivity
// ===========================================================================

// u_reg captures opu_i on the rising edge
property conn_u_reg_p;
  ##1 u_reg == $past(opu_i);
endproperty
a_conn_u_reg: assert property (disable iff (!rst_n) conn_u_reg_p);

// u_reg_d2 is one-cycle delayed u_reg
property conn_u_reg_d2_p;
  ##1 u_reg_d2 == $past(u_reg);
endproperty
a_conn_u_reg_d2: assert property (disable iff (!rst_n) conn_u_reg_d2_p);

// w_reg captures opw_i on the rising edge
property conn_w_reg_p;
  ##1 w_reg == $past(opw_i);
endproperty
a_conn_w_reg: assert property (disable iff (!rst_n) conn_w_reg_p);

// w_reg_d2 is one-cycle delayed w_reg
property conn_w_reg_d2_p;
  ##1 w_reg_d2 == $past(w_reg);
endproperty
a_conn_w_reg_d2: assert property (disable iff (!rst_n) conn_w_reg_d2_p);

// add_res_d1 captures add_res on the rising edge
property conn_add_res_d1_p;
  ##1 add_res_d1 == $past(add_res);
endproperty
a_conn_add_res_d1: assert property (disable iff (!rst_n) conn_add_res_d1_p);

// add_res_d2 is one-cycle delayed add_res_d1
property conn_add_res_d2_p;
  ##1 add_res_d2 == $past(add_res,2);
endproperty
a_conn_add_res_d2: assert property (disable iff (!rst_n) conn_add_res_d2_p);


// ===========================================================================
// Group 2 — Multiplier input mux connectivity
// ===========================================================================

// CT: mul_opa driven by opv_i, mul_opb driven by opw_i
property conn_mul_ct_p;
  fv_ct
|->
  mul_opa == opv_i && mul_opb == opw_i;
endproperty
a_conn_mul_ct: assert property (disable iff (!rst_n) conn_mul_ct_p);

// GS: mul_opb driven by w_reg (one-cycle delayed opw_i)
property conn_mul_opb_gs_p;
  fv_gs
|->
  mul_opb == w_reg;
endproperty
a_conn_mul_opb_gs: assert property (disable iff (!rst_n) conn_mul_opb_gs_p);

// GS MLDSA: mul_opa driven by mldsa_u_minus_v_div2
property conn_mul_opa_gs_mldsa_p;
  fv_gs && !mlkem
|->
  mul_opa == fv_gs_mul_opa_mldsa;
endproperty
a_conn_mul_opa_gs_mldsa: assert property (disable iff (!rst_n) conn_mul_opa_gs_mldsa_p);

// GS MLKEM: mul_opa driven by mlkem_u_minus_v_div2 (12-bit div2, zero-extended)
property conn_mul_opa_gs_mlkem_p;
  fv_gs && mlkem
|->
  mul_opa == fv_gs_mul_opa_mlkem;
endproperty
a_conn_mul_opa_gs_mlkem: assert property (disable iff (!rst_n) conn_mul_opa_gs_mlkem_p);

// PWM: mul_opa driven by opu_i, mul_opb driven by opv_i
property conn_mul_pwm_p;
  fv_pwm
|->
  mul_opa == opu_i && mul_opb == opv_i;
endproperty
a_conn_mul_pwm: assert property (disable iff (!rst_n) conn_mul_pwm_p);


// PAIRWM MLKEM: mul_opa = opu_i, mul_opb = opv_i
property conn_mul_pairwm_mlkem_p;
  fv_pairwm && mlkem
|->
  mul_opa == opu_i && mul_opb == opv_i;
endproperty
a_conn_mul_pairwm_mlkem: assert property (disable iff (!rst_n) conn_mul_pairwm_mlkem_p);

// ===========================================================================
// Group 3 — Adder input mux connectivity
// ===========================================================================

// CT MLKEM: add_opa = u_reg_d2, add_opb = mlkem_mul_res_reduced_reg (zero-extended)
property conn_add_ct_mlkem_p;
  fv_ct && mlkem
|->
    add_opa == u_reg_d2 &&
    add_opb == 23'(mlkem_mul_res_reduced_reg);
endproperty
a_conn_add_ct_mlkem: assert property (disable iff (!rst_n) conn_add_ct_mlkem_p);

// CT MLDSA: add_opa = u_reg_d2, add_opb = mldsa_mul_res_reduced
property conn_add_ct_mldsa_p;
  fv_ct && !mlkem
|->
    add_opa == u_reg_d2 &&
    add_opb == mldsa_mul_res_reduced;
endproperty
a_conn_add_ct_mldsa: assert property (disable iff (!rst_n) conn_add_ct_mldsa_p);

// GS: add_opa = opu_i, add_opb = opv_i (sum feeds the div2 → u_o path)
property conn_add_gs_p;
  fv_gs
|->
  add_opa == opu_i && add_opb == opv_i;
endproperty
a_conn_add_gs: assert property (disable iff (!rst_n) conn_add_gs_p);

// PWM MLKEM: adder inputs forced to zero (result unused; output goes via pairwm path)
property conn_add_pwm_mlkem_p;
  fv_pwm && mlkem
|->
  add_opa == 23'd0 && add_opb == 23'd0;
endproperty
a_conn_add_pwm_mlkem: assert property (disable iff (!rst_n) conn_add_pwm_mlkem_p);

// PWM MLDSA: add_opa = w_reg_d2 (accumulate reg), add_opb = mldsa_mul_res_reduced
property conn_add_pwm_mldsa_p;
  fv_pwm && !mlkem
|->
    add_opa == w_reg_d2 &&
    add_opb == mldsa_mul_res_reduced;
endproperty
a_conn_add_pwm_mldsa: assert property (disable iff (!rst_n) conn_add_pwm_mldsa_p);

// PWA: add_opa = opu_i, add_opb = opv_i
property conn_add_pwa_p;
  fv_pwa
|->
  add_opa == opu_i && add_opb == opv_i;
endproperty
a_conn_add_pwa: assert property (disable iff (!rst_n) conn_add_pwa_p);




// ===========================================================================
// Group 4 — Output mux connectivity
// All checks are combinational (same-cycle) because the output mux is purely
// combinational; the registered latency has already been absorbed by add_res,
// sub_res, u_minus_v, and the mul reduction pipeline.
// ===========================================================================

// ---- CT ----

// u_o is wired directly to add_res
property conn_u_o_ct_p;
  fv_ct
|->
  u_o == add_res;
endproperty
a_conn_u_o_ct: assert property (disable iff (!rst_n) conn_u_o_ct_p);

// v_o is wired directly to sub_res (sub_inst_1 output)
property conn_v_o_ct_p;
  fv_ct
|->
  v_o == sub_res;
endproperty
a_conn_v_o_ct: assert property (disable iff (!rst_n) conn_v_o_ct_p);


// ---- GS ----

// u_o is mldsa_add_res_div2 when !mlkem
property conn_u_o_gs_mldsa_p;
  fv_gs && !mlkem
|->
  u_o == fv_gs_u_o_mldsa;
endproperty
a_conn_u_o_gs_mldsa: assert property (disable iff (!rst_n) conn_u_o_gs_mldsa_p);

// u_o is mlkem_add_res_div2 (12-bit, zero-extended) when mlkem
property conn_u_o_gs_mlkem_p;
  fv_gs && mlkem
|->
  u_o == fv_gs_u_o_mlkem;
endproperty
a_conn_u_o_gs_mlkem: assert property (disable iff (!rst_n) conn_u_o_gs_mlkem_p);

// v_o is mldsa_mul_res_reduced when !mlkem
property conn_v_o_gs_mldsa_p;
  fv_gs && !mlkem
|->
  v_o == 23'(mldsa_mul_res_reduced);
endproperty
a_conn_v_o_gs_mldsa: assert property (disable iff (!rst_n) conn_v_o_gs_mldsa_p);

// v_o is mlkem_mul_res_reduced_reg (12-bit, zero-extended) when mlkem
property conn_v_o_gs_mlkem_p;
  fv_gs && mlkem
|->
  v_o == 23'(mlkem_mul_res_reduced_reg);
endproperty
a_conn_v_o_gs_mlkem: assert property (disable iff (!rst_n) conn_v_o_gs_mlkem_p);






// pwm_res_o is add_res for MLDSA accumulate
property conn_pwm_res_o_pwm_mldsa_acc_p;
  fv_pwm && !mlkem && accumulate
|->
  pwm_res_o == add_res;
endproperty
a_conn_pwm_res_o_pwm_mldsa_acc: assert property (disable iff (!rst_n) conn_pwm_res_o_pwm_mldsa_acc_p);

// pwm_res_o is mldsa_mul_res_reduced for MLDSA non-accumulate
property conn_pwm_res_o_pwm_mldsa_nacc_p;
  fv_pwm && !mlkem && !accumulate
|->
  pwm_res_o == 23'(mldsa_mul_res_reduced);
endproperty
a_conn_pwm_res_o_pwm_mldsa_nacc: assert property (disable iff (!rst_n) conn_pwm_res_o_pwm_mldsa_nacc_p);

// ---- PWA ----



// pwm_res_o is add_res (= (opu_i + opv_i) % Q)
property conn_pwm_res_o_pwa_p;
  fv_pwa
|->
  pwm_res_o == add_res;
endproperty
a_conn_pwm_res_o_pwa: assert property (disable iff (!rst_n) conn_pwm_res_o_pwa_p);

// ---- PWS ----



// pwm_res_o is u_minus_v (sub_inst_0 output: (opu_i - opv_i) % Q)
property conn_pwm_res_o_pws_p;
  fv_pws
|->
  pwm_res_o == u_minus_v;
endproperty
a_conn_pwm_res_o_pws: assert property (disable iff (!rst_n) conn_pwm_res_o_pws_p);

// ---- PAIRWM ----

// u_o, v_o, pwm_res_o are all zero


// pairwm_mul_red_o carries the MLKEM barrett-reduced product (1 registered stage)
// RTL: pairwm_mul_red_o = ((mode==pairwm) & mlkem) ? mlkem_mul_res_reduced_reg : 0
property conn_pairwm_mul_red_o_mlkem_p;
  fv_pairwm && mlkem
|->
  pairwm_mul_red_o == 23'(mlkem_mul_res_reduced_reg);
endproperty
a_conn_pairwm_mul_red_o_mlkem: assert property (disable iff (!rst_n) conn_pairwm_mul_red_o_mlkem_p);




endmodule


// ---------------------------------------------------------------------------
// Bind statement
// ---------------------------------------------------------------------------

bind ntt_butterfly fv_ntt_butterfly_conn_m fv_ntt_butterfly_conn (
  .rst_n              (ntt_butterfly.reset_n && !ntt_butterfly.zeroize),
  .clk                (ntt_butterfly.clk),

  .opu_i              (ntt_butterfly.opu_i),
  .opv_i              (ntt_butterfly.opv_i),
  .opw_i              (ntt_butterfly.opw_i),
  .mode               (ntt_butterfly.mode),
  .accumulate         (ntt_butterfly.accumulate),
  .mlkem              (ntt_butterfly.mlkem),

  .u_o                (ntt_butterfly.u_o),
  .v_o                (ntt_butterfly.v_o),
  .pwm_res_o          (ntt_butterfly.pwm_res_o),
  .pairwm_mul_red_o   (ntt_butterfly.pairwm_mul_red_o),

  .u_reg              (ntt_butterfly.u_reg),
  .u_reg_d2           (ntt_butterfly.u_reg_d2),
  .w_reg              (ntt_butterfly.w_reg),
  .w_reg_d2           (ntt_butterfly.w_reg_d2),

  .add_res            (ntt_butterfly.add_res),
  .add_res_d1         (ntt_butterfly.add_res_d1),
  .add_res_d2         (ntt_butterfly.add_res_d2),

  .mul_opa            (ntt_butterfly.mul_opa),
  .mul_opb            (ntt_butterfly.mul_opb),
  .add_opa            (ntt_butterfly.add_opa),
  .add_opb            (ntt_butterfly.add_opb),

  .sub_res            (ntt_butterfly.sub_res),
  .u_minus_v          (ntt_butterfly.u_minus_v),

  .mul_res            (ntt_butterfly.mul_res),
  .mul_res_reg        (ntt_butterfly.mul_res_reg),
  .mldsa_mul_res_reg  (ntt_butterfly.mldsa_mul_res_reg),
  .mlkem_mul_res_reduced        (ntt_butterfly.mlkem_mul_res_reduced),
  .mldsa_mul_res_reduced_comb   (ntt_butterfly.mldsa_mul_res_reduced_comb),
  .mlkem_mul_res_reduced_reg    (ntt_butterfly.mlkem_mul_res_reduced_reg),
  .mldsa_mul_res_reduced        (ntt_butterfly.mldsa_mul_res_reduced)
);
