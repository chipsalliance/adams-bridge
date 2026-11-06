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

#include "jasperc.h"
#include "stdint.h"

// Unmasked MLKEM golden model for ntt_hybrid_butterfly_2x2.
//
// We have no separate spec document for this block, so this model encodes
// the RTL's own intended arithmetic directly (CT/GS butterfly modular
// add/sub/mul/div2, and the Karatsuba pairwm identity) rather than tracking
// any FV property file - it's meant to independently confirm the RTL's
// behavior via check_c2rtl equivalence, not to validate another model.
// Masking (masking_en, share pairs _0/_1) removed: current RTL has neither.

#define MLKEM_Q 3329u

uint32_t compute_a_min_b(uint32_t a, uint32_t b) {
    if (a >= b) {
        return (a - b);
    } else {
        return (a - b + MLKEM_Q);
    }
}

uint32_t div2_mlkem(uint32_t data) {
    if ((data & 1u) == 1u) {
        return (data >> 1) + ((MLKEM_Q + 1) / 2);
    } else {
        return data >> 1;
    }
}

uint32_t compute_u_ct_mlkem(uint32_t u, uint32_t v, uint32_t w) {
    uint32_t vw = (uint32_t)(((uint64_t)v * (uint64_t)w) % MLKEM_Q);
    return (u + vw) % MLKEM_Q;
}

uint32_t compute_v_ct_mlkem(uint32_t u, uint32_t v, uint32_t w) {
    uint32_t vw = (uint32_t)(((uint64_t)v * (uint64_t)w) % MLKEM_Q);
    return compute_a_min_b(u, vw);
}

// w unused - GS mode's u_o = div2(u+v), independent of w
uint32_t compute_u_gs_mlkem(uint32_t u, uint32_t v) {
    uint32_t sum = (u + v) % MLKEM_Q;
    return div2_mlkem(sum) % MLKEM_Q;
}

uint32_t compute_v_gs_mlkem(uint32_t u, uint32_t v, uint32_t w) {
    uint32_t diff = compute_a_min_b(u, v);
    uint32_t halved = div2_mlkem(diff);
    return (uint32_t)(((uint64_t)halved * (uint64_t)w) % MLKEM_Q);
}

uint32_t compute_pwa_mlkem(uint32_t a, uint32_t b) {
    return (a + b) % MLKEM_Q;
}

uint32_t compute_pairwm_mult_mlkem(uint32_t a, uint32_t b) {
    return (uint32_t)(((uint64_t)a * (uint64_t)b) % MLKEM_Q);
}

int main() {

    //----------------------------------------------------
    // Control-signal inputs - not read by any compute_* call below (the
    // model still computes every mode's result unconditionally); these
    // exist purely so check_c2rtl -setup can map them 1:1 to the RTL,
    // letting properties reference bare mode/mlkem/etc instead of $imp.<sig>.
    //----------------------------------------------------
    uint8_t mode;
    bool mlkem, accumulate, intt_passthrough, ntt_passthrough;
    JG_INPUT(mode);
    JG_INPUT(mlkem);
    JG_INPUT(accumulate);
    JG_INPUT(intt_passthrough);
    JG_INPUT(ntt_passthrough);

    //----------------------------------------------------
    // CT/GS inputs - plain scalars, matches bf_uvwi_t fields
    //----------------------------------------------------
    uint32_t u00, v00, w00, u01, v01, w01, w10, w11;
    JG_INPUT(u00);
    JG_INPUT(v00);
    JG_INPUT(w00);
    JG_INPUT(u01);
    JG_INPUT(v01);
    JG_INPUT(w01);
    JG_INPUT(w10);
    JG_INPUT(w11);

    //----------------------------------------------------
    // Pairwm lane inputs - plain scalars, matches pwo_uvwi_t / zeta fields
    //----------------------------------------------------
    uint32_t pw_u0, pw_v0, pw_w0, pw_u1, pw_v1, pw_w1;
    uint32_t pw_u2, pw_v2, pw_w2, pw_u3, pw_v3, pw_w3;
    uint32_t z0, z1;
    JG_INPUT(pw_u0);
    JG_INPUT(pw_v0);
    JG_INPUT(pw_w0);
    JG_INPUT(pw_u1);
    JG_INPUT(pw_v1);
    JG_INPUT(pw_w1);
    JG_INPUT(pw_u2);
    JG_INPUT(pw_v2);
    JG_INPUT(pw_w2);
    JG_INPUT(pw_u3);
    JG_INPUT(pw_v3);
    JG_INPUT(pw_w3);
    JG_INPUT(z0);
    JG_INPUT(z1);

    //----------------------------------------------------
    // CT mode - stage 1 (bf_inst00/01), no passthrough
    //----------------------------------------------------
    uint32_t u_ct_0 = compute_u_ct_mlkem(u00, v00, w00);   // -> bf_inst00.u_o == u10_int
    uint32_t v_ct_1 = compute_v_ct_mlkem(u00, v00, w00);   // -> bf_inst00.v_o == u11_int
    uint32_t u_ct_1 = compute_u_ct_mlkem(u01, v01, w01);   // -> bf_inst01.u_o == v10_int
    uint32_t v_ct_2 = compute_v_ct_mlkem(u01, v01, w01);   // -> bf_inst01.v_o == v11_int
    JG_BUFFER(u_ct_0);
    JG_BUFFER(v_ct_1);
    JG_BUFFER(u_ct_1);
    JG_BUFFER(v_ct_2);

    // CT mode - stage 2 (bf_inst10/11), no passthrough
    uint32_t u_ct_2 = compute_u_ct_mlkem(u_ct_0, u_ct_1, w10);   // -> bf_inst10.u_o == u20_int
    uint32_t v_ct_0 = compute_v_ct_mlkem(u_ct_0, u_ct_1, w10);   // -> bf_inst10.v_o == v20_int
    uint32_t u_ct_3 = compute_u_ct_mlkem(v_ct_1, v_ct_2, w11);   // -> bf_inst11.u_o == u21_int
    uint32_t v_ct_3 = compute_v_ct_mlkem(v_ct_1, v_ct_2, w11);   // -> bf_inst11.v_o == v21_int
    JG_OUTPUT(u_ct_2);
    JG_OUTPUT(v_ct_0);
    JG_OUTPUT(u_ct_3);
    JG_OUTPUT(v_ct_3);

    //----------------------------------------------------
    // GS mode - stage 1 (bf_inst00/01), no passthrough
    //----------------------------------------------------
    uint32_t u_gs_0 = compute_u_gs_mlkem(u00, v00);            // -> bf_inst00.u_o == u10_int
    uint32_t v_gs_1 = compute_v_gs_mlkem(u00, v00, w00);       // -> bf_inst00.v_o == u11_int
    uint32_t u_gs_1 = compute_u_gs_mlkem(u01, v01);            // -> bf_inst01.u_o == v10_int
    uint32_t v_gs_2 = compute_v_gs_mlkem(u01, v01, w01);       // -> bf_inst01.v_o == v11_int
    JG_BUFFER(u_gs_0);
    JG_BUFFER(v_gs_1);
    JG_BUFFER(u_gs_1);
    JG_BUFFER(v_gs_2);

    // GS mode - stage 2 (bf_inst10/11), no passthrough
    uint32_t u_gs_2 = compute_u_gs_mlkem(u_gs_0, u_gs_1);          // -> bf_inst10.u_o == u20_int
    uint32_t v_gs_0 = compute_v_gs_mlkem(u_gs_0, u_gs_1, w10);     // -> bf_inst10.v_o == v20_int
    uint32_t u_gs_3 = compute_u_gs_mlkem(v_gs_1, v_gs_2);          // -> bf_inst11.u_o == u21_int
    uint32_t v_gs_3 = compute_v_gs_mlkem(v_gs_1, v_gs_2, w11);     // -> bf_inst11.v_o == v21_int
    JG_OUTPUT(u_gs_2);
    JG_OUTPUT(v_gs_0);
    JG_OUTPUT(u_gs_3);
    JG_OUTPUT(v_gs_3);

    //----------------------------------------------------
    // GS mode - stage 1 with intt_passthrough (bf_inst00 gets (u00,u01) pair,
    // bf_inst01 gets (v00,v01) pair, w taken from the low 12 bits of w10/w11 -
    // matches the RTL's intt_passthrough input mux)
    //----------------------------------------------------
    uint32_t w10_lo12 = w10 & 0xFFFu;
    uint32_t w11_lo12 = w11 & 0xFFFu;
    uint32_t u_gs_0_ipt = compute_u_gs_mlkem(u00, u01);            // -> bf_inst00.u_o == u10_int
    uint32_t v_gs_1_ipt = compute_v_gs_mlkem(u00, u01, w10_lo12);  // -> bf_inst00.v_o == u11_int
    uint32_t u_gs_1_ipt = compute_u_gs_mlkem(v00, v01);            // -> bf_inst01.u_o == v10_int
    uint32_t v_gs_2_ipt = compute_v_gs_mlkem(v00, v01, w11_lo12);  // -> bf_inst01.v_o == v11_int
    JG_OUTPUT(u_gs_0_ipt);
    JG_OUTPUT(v_gs_1_ipt);
    JG_OUTPUT(u_gs_1_ipt);
    JG_OUTPUT(v_gs_2_ipt);

    //----------------------------------------------------
    // MLKEM Karatsuba pairwm
    //   c0 = m0 + m1*zeta ; c1 = (u0+u1)*(v0+v1) - m0 - m1   (all mod Q)
    // lanes 0/1 -> uv0/uv1 via zeta z0 (mlkem_pawm_inst0)
    // lanes 2/3 -> uv2/uv3 via zeta z1 (mlkem_pawm_inst1)
    //----------------------------------------------------
    uint32_t m0_01 = compute_pairwm_mult_mlkem(pw_u0, pw_v0);
    uint32_t m1_01 = compute_pairwm_mult_mlkem(pw_u1, pw_v1);
    uint32_t m1z_01 = compute_pairwm_mult_mlkem(m1_01, z0);
    uint32_t c0_01 = compute_pwa_mlkem(m1z_01, m0_01);
    uint32_t sum_u01 = compute_pwa_mlkem(pw_u0, pw_u1);
    uint32_t sum_v01 = compute_pwa_mlkem(pw_v0, pw_v1);
    uint32_t m2_01 = compute_pairwm_mult_mlkem(sum_u01, sum_v01);
    uint32_t c1_01 = compute_a_min_b(compute_a_min_b(m2_01, m0_01), m1_01);
    uint32_t c0_acc_01 = compute_pwa_mlkem(c0_01, pw_w0);
    uint32_t c1_acc_01 = compute_pwa_mlkem(c1_01, pw_w1);
    JG_OUTPUT(c0_01);       // -> mlkem_pawm_inst0.pwo_uv_o.uv0_o (accumulate == 0)
    JG_OUTPUT(c1_01);       // -> mlkem_pawm_inst0.pwo_uv_o.uv1_o (accumulate == 0)
    JG_OUTPUT(c0_acc_01);   // -> mlkem_pawm_inst0.pwo_uv_o.uv0_o (accumulate == 1)
    JG_OUTPUT(c1_acc_01);   // -> mlkem_pawm_inst0.pwo_uv_o.uv1_o (accumulate == 1)

    uint32_t m0_23 = compute_pairwm_mult_mlkem(pw_u2, pw_v2);
    uint32_t m1_23 = compute_pairwm_mult_mlkem(pw_u3, pw_v3);
    uint32_t m1z_23 = compute_pairwm_mult_mlkem(m1_23, z1);
    uint32_t c0_23 = compute_pwa_mlkem(m1z_23, m0_23);
    uint32_t sum_u23 = compute_pwa_mlkem(pw_u2, pw_u3);
    uint32_t sum_v23 = compute_pwa_mlkem(pw_v2, pw_v3);
    uint32_t m2_23 = compute_pairwm_mult_mlkem(sum_u23, sum_v23);
    uint32_t c1_23 = compute_a_min_b(compute_a_min_b(m2_23, m0_23), m1_23);
    uint32_t c0_acc_23 = compute_pwa_mlkem(c0_23, pw_w2);
    uint32_t c1_acc_23 = compute_pwa_mlkem(c1_23, pw_w3);
    JG_OUTPUT(c0_23);       // -> mlkem_pawm_inst1.pwo_uv_o.uv0_o (accumulate == 0)
    JG_OUTPUT(c1_23);       // -> mlkem_pawm_inst1.pwo_uv_o.uv1_o (accumulate == 0)
    JG_OUTPUT(c0_acc_23);   // -> mlkem_pawm_inst1.pwo_uv_o.uv0_o (accumulate == 1)
    JG_OUTPUT(c1_acc_23);   // -> mlkem_pawm_inst1.pwo_uv_o.uv1_o (accumulate == 1)

    //----------------------------------------------------
    // PWA/PWS mode (MLKEM) - bf_inst00/01/10/11's pwm_res_o, routed through
    // mldsa_pwo_uv_o -> pwo_uv_o.uv0/1/2/3. Same 4 pw_uvw_i lanes as pairwm,
    // just add/sub instead of Karatsuba multiply, and only 1 cycle of latency
    // (PWA_LATENCY == PWS_LATENCY == 1).
    //----------------------------------------------------
    uint32_t pwa0 = compute_pwa_mlkem(pw_u0, pw_v0);   // -> bf_inst00.pwm_res_o == pwo_uv_o.uv0
    uint32_t pwa1 = compute_pwa_mlkem(pw_u1, pw_v1);   // -> bf_inst01.pwm_res_o == pwo_uv_o.uv1
    uint32_t pwa2 = compute_pwa_mlkem(pw_u2, pw_v2);   // -> bf_inst10.pwm_res_o == pwo_uv_o.uv2
    uint32_t pwa3 = compute_pwa_mlkem(pw_u3, pw_v3);   // -> bf_inst11.pwm_res_o == pwo_uv_o.uv3
    JG_OUTPUT(pwa0);
    JG_OUTPUT(pwa1);
    JG_OUTPUT(pwa2);
    JG_OUTPUT(pwa3);

    uint32_t pws0 = compute_a_min_b(pw_u0, pw_v0);   // -> bf_inst00.pwm_res_o == pwo_uv_o.uv0
    uint32_t pws1 = compute_a_min_b(pw_u1, pw_v1);   // -> bf_inst01.pwm_res_o == pwo_uv_o.uv1
    uint32_t pws2 = compute_a_min_b(pw_u2, pw_v2);   // -> bf_inst10.pwm_res_o == pwo_uv_o.uv2
    uint32_t pws3 = compute_a_min_b(pw_u3, pw_v3);   // -> bf_inst11.pwm_res_o == pwo_uv_o.uv3
    JG_OUTPUT(pws0);
    JG_OUTPUT(pws1);
    JG_OUTPUT(pws2);
    JG_OUTPUT(pws3);
}
