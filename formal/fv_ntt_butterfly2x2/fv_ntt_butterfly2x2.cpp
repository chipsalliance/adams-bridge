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
// Jasper Gold C model for ntt_butterfly2x2
// Full pipeline verification — no cut points.
//
// RTL structure (ntt_butterfly2x2.sv):
//
//  Input mux: pwo_mode = mode ∈ {pwm=2, pwa=3, pws=4}
//             pairwm_mode = mlkem & (mode == pairwm=5)
//  If (pwo_mode | pairwm_mode): all 4 BFs take pw_uvw_i
//  Else CT/GS: bf_inst00/01 take uvw_i; bf_inst10/11 take stage-1 outputs
//
//  CT/GS pipeline per BF (ntt_butterfly.sv):
//    p0  = v * w % Q
//    p1  = (u + v) % Q
//    p2  = mod_sub(u, v, Q)
//    p3  = mod_div2(p2, Q)
//    u_ct = (u + p0) % Q
//    v_ct = mod_sub(u, p0, Q)
//    u_gs = mod_div2(p1, Q)
//    v_gs = p3 * w % Q
//
//  Stage-1 mapping (BF00->u10_int/u11_int; BF01->v10_int/v11_int):
//    CT: u10_int=u_ct_00, u11_int=v_ct_00, v10_int=u_ct_01, v11_int=v_ct_01
//    GS: u10_int=u_gs_00, u11_int=v_gs_00, v10_int=u_gs_01, v11_int=v_gs_01
//
//  Stage-2 (BF10: u10_int/v10_int/w10; BF11: u11_int/v11_int/w11)
//    -> u20_o/v20_o, u21_o/v21_o
//
//  PAIRWM (mode=5, mlkem=1):
//    BF pairwm_mul_red_o = (u*v) % MLKEM_Q  [2-cycle tap]
//    Karatsuba inst0(m0_01,m1_01,z0) -> pwo_uv0,pwo_uv1
//    Karatsuba inst1(m0_23,m1_23,z1) -> pwo_uv2,pwo_uv3
//
//  PWO (modes 2,3,4, mlkem=0): pwo_uv = BF pwm_res_o; u_o=v_o=0
//
//  MLDSA pairwm (mode=5, mlkem=0): ready_o=0, data outputs unconstrained (modeled as 0)
//  MLKEM PWM   (mode=2, mlkem=1): ready_o=0, data outputs = 0 (Karatsuba gets 0 inputs)

#include "jasperc.h"
#include "stdint.h"

#define MLDSA_Q 8380417U
#define MLKEM_Q 3329U

// ---- MLDSA helpers ---------------------------------------------------------

uint32_t mldsa_sub(uint32_t a, uint32_t b) {
    if (a >= b) return a - b;
    return a - b + MLDSA_Q;
}

uint32_t mldsa_div2(uint32_t d) {
    if (d & 1u) return (d >> 1u) + (MLDSA_Q + 1u) / 2u;
    return d >> 1u;
}

// ---- MLKEM helpers (CT/GS domain) ------------------------------------------

uint32_t mlkem_bf_sub(uint32_t a, uint32_t b) {
    if (a >= b) return a - b;
    return a - b + MLKEM_Q;
}

uint32_t mlkem_bf_div2(uint32_t d) {
    if (d & 1u) return (d >> 1u) + (MLKEM_Q + 1u) / 2u;
    return d >> 1u;
}

// ---- MLKEM modular subtraction (Karatsuba c1 computation) -------------------

uint32_t mlkem_sub(uint32_t a, uint32_t b) {
    if (a >= b) return a - b;
    return a - b + MLKEM_Q;
}

// ---- MLDSA PWO (BF pwm_res_o, mlkem=0 only) ---------------------------------

uint32_t compute_pwm(uint32_t u, uint32_t v, uint32_t w, uint8_t nm, bool acc) {
    if (nm == 2u) {
        uint32_t prod = (uint32_t)((uint64_t)u * v % MLDSA_Q);
        if (acc) return (uint32_t)((w + prod) % MLDSA_Q);
        return prod;
    }
    if (nm == 3u) return (uint32_t)((u + v) % MLDSA_Q);
    if (nm == 4u) return mldsa_sub(u, v);
    return 0u;
}

// ============================================================================

int main() {

    // CT/GS inputs (uvw_i struct)
    uint32_t u00_i, u01_i;
    uint32_t v00_i, v01_i;
    uint32_t w00_i, w01_i;
    uint32_t w10_i,  w11_i;

    // PWO/PAIRWM inputs (pw_uvw_i struct)
    uint32_t pw_u0_i, pw_u1_i, pw_u2_i, pw_u3_i;
    uint32_t pw_v0_i, pw_v1_i, pw_v2_i, pw_v3_i;
    uint32_t pw_w0_i, pw_w1_i, pw_w2_i, pw_w3_i;

    // MLKEM Karatsuba zeta factors (MLKEM_REG_SIZE=12 bits)
    uint32_t z0_i;
    uint32_t z1_i;

    uint8_t  mode;
    bool     accumulate;
    bool     mlkem;

    JG_INPUT(u00_i);   JG_INPUT(u01_i);
    JG_INPUT(v00_i);   JG_INPUT(v01_i);
    JG_INPUT(w00_i);   JG_INPUT(w01_i);
    JG_INPUT(w10_i);   JG_INPUT(w11_i);
    JG_INPUT(pw_u0_i); JG_INPUT(pw_u1_i); JG_INPUT(pw_u2_i); JG_INPUT(pw_u3_i);
    JG_INPUT(pw_v0_i); JG_INPUT(pw_v1_i); JG_INPUT(pw_v2_i); JG_INPUT(pw_v3_i);
    JG_INPUT(pw_w0_i); JG_INPUT(pw_w1_i); JG_INPUT(pw_w2_i); JG_INPUT(pw_w3_i);
    JG_INPUT(z0_i);    JG_INPUT(z1_i);
    JG_INPUT(mode);
    JG_INPUT(accumulate);
    JG_INPUT(mlkem);

    uint32_t u20_o,   v20_o;
    uint32_t u21_o,   v21_o;
    uint32_t pwo_uv0, pwo_uv1, pwo_uv2, pwo_uv3;

    bool pwo_mode    = (mode == 2u || mode == 3u || mode == 4u);
    bool pairwm_mode = mlkem && (mode == 5u);

    if (pwo_mode || pairwm_mode) {

        // BF u_o = v_o = 0 in all PWO and PAIRWM modes
        u20_o = 0u; v20_o = 0u;
        u21_o = 0u; v21_o = 0u;

        if (pairwm_mode) {
            // ---- PAIRWM path (mlkem=1, mode=5) ----
            // BF pairwm_mul_red_o = (u*v) % MLKEM_Q  [2-cycle registered tap]

            uint32_t m0_01 = (uint32_t)((uint64_t)pw_u0_i * pw_v0_i % MLKEM_Q);
            uint32_t m1_01 = (uint32_t)((uint64_t)pw_u1_i * pw_v1_i % MLKEM_Q);
            uint32_t m0_23 = (uint32_t)((uint64_t)pw_u2_i * pw_v2_i % MLKEM_Q);
            uint32_t m1_23 = (uint32_t)((uint64_t)pw_u3_i * pw_v3_i % MLKEM_Q);
            JG_BUFFER(m0_01); JG_BUFFER(m1_01);
            JG_BUFFER(m0_23); JG_BUFFER(m1_23);

            // Karatsuba inst0 (pair 0/1, zeta = z0_i):
            uint32_t sum_u01 = (uint32_t)((pw_u0_i + pw_u1_i) % MLKEM_Q);
            uint32_t sum_v01 = (uint32_t)((pw_v0_i + pw_v1_i) % MLKEM_Q);
            uint32_t m2_01   = (uint32_t)((uint64_t)sum_u01 * sum_v01 % MLKEM_Q);
            uint32_t m1z_01  = (uint32_t)((uint64_t)m1_01 * z0_i % MLKEM_Q);
            uint32_t c0_01   = (uint32_t)((m0_01 + m1z_01) % MLKEM_Q);
            uint32_t c1_01   = mlkem_sub(mlkem_sub(m2_01, m0_01), m1_01);
            if (accumulate) {
                pwo_uv0 = (uint32_t)((c0_01 + pw_w0_i) % MLKEM_Q);
                pwo_uv1 = (uint32_t)((c1_01 + pw_w1_i) % MLKEM_Q);
            } else {
                pwo_uv0 = c0_01;
                pwo_uv1 = c1_01;
            }

            // Karatsuba inst1 (pair 2/3, zeta = z1_i):
            uint32_t sum_u23 = (uint32_t)((pw_u2_i + pw_u3_i) % MLKEM_Q);
            uint32_t sum_v23 = (uint32_t)((pw_v2_i + pw_v3_i) % MLKEM_Q);
            uint32_t m2_23   = (uint32_t)((uint64_t)sum_u23 * sum_v23 % MLKEM_Q);
            uint32_t m1z_23  = (uint32_t)((uint64_t)m1_23 * z1_i % MLKEM_Q);
            uint32_t c0_23   = (uint32_t)((m0_23 + m1z_23) % MLKEM_Q);
            uint32_t c1_23   = mlkem_sub(mlkem_sub(m2_23, m0_23), m1_23);
            if (accumulate) {
                pwo_uv2 = (uint32_t)((c0_23 + pw_w2_i) % MLKEM_Q);
                pwo_uv3 = (uint32_t)((c1_23 + pw_w3_i) % MLKEM_Q);
            } else {
                pwo_uv2 = c0_23;
                pwo_uv3 = c1_23;
            }

        } else {
            // ---- PWO path (modes 2,3,4) ----
            if (mlkem) {
                // MLKEM + PWO (mode=2/3/4, mlkem=1):
                // pairwm_mul_red_o=0 (non-pairwm) -> Karatsuba=0 -> pwo_uv_o=0
                pwo_uv0 = 0u; pwo_uv1 = 0u;
                pwo_uv2 = 0u; pwo_uv3 = 0u;
            } else {
                // MLDSA PWM/PWA/PWS (mode=2/3/4, mlkem=0)
                // pwo_uv0 <- u0/v0/w0, pwo_uv1 <- u1/v1/w1,
                // pwo_uv2 <- u2/v2/w2, pwo_uv3 <- u3/v3/w3
                pwo_uv0 = compute_pwm(pw_u0_i, pw_v0_i, pw_w0_i, mode, accumulate);
                pwo_uv1 = compute_pwm(pw_u1_i, pw_v1_i, pw_w1_i, mode, accumulate);
                pwo_uv2 = compute_pwm(pw_u2_i, pw_v2_i, pw_w2_i, mode, accumulate);
                pwo_uv3 = compute_pwm(pw_u3_i, pw_v3_i, pw_w3_i, mode, accumulate);
            }
        }

    } else if (mlkem && (mode == 0u || mode == 1u)) {
        // ================================================================
        // MLKEM CT (mode=0) / GS (mode=1) path — full 2-stage pipeline
        // All arithmetic uses MLKEM_Q = 3329.
        // ================================================================

        // ===== STAGE 1: bf_inst00(u00_i, v00_i, w00_i) =====
        uint32_t p0_00 = (uint32_t)((uint64_t)v00_i * w00_i % MLKEM_Q);
        uint32_t p1_00 = (uint32_t)((u00_i + v00_i) % MLKEM_Q);
        uint32_t p2_00 = mlkem_bf_sub(u00_i, v00_i);
        uint32_t p3_00 = mlkem_bf_div2(p2_00);
        uint32_t u_ct_00 = (uint32_t)((u00_i + p0_00) % MLKEM_Q);
        uint32_t v_ct_00 = mlkem_bf_sub(u00_i, p0_00);
        uint32_t u_gs_00 = mlkem_bf_div2(p1_00);
        uint32_t v_gs_00 = (uint32_t)((uint64_t)p3_00 * w00_i % MLKEM_Q);
        JG_BUFFER(p0_00); JG_BUFFER(p1_00); JG_BUFFER(p2_00); JG_BUFFER(p3_00);
        JG_BUFFER(u_ct_00); JG_BUFFER(v_ct_00); JG_BUFFER(u_gs_00); JG_BUFFER(v_gs_00);

        // ===== STAGE 1: bf_inst01(u01_i, v01_i, w01_i) =====
        uint32_t p0_01 = (uint32_t)((uint64_t)v01_i * w01_i % MLKEM_Q);
        uint32_t p1_01 = (uint32_t)((u01_i + v01_i) % MLKEM_Q);
        uint32_t p2_01 = mlkem_bf_sub(u01_i, v01_i);
        uint32_t p3_01 = mlkem_bf_div2(p2_01);
        uint32_t u_ct_01 = (uint32_t)((u01_i + p0_01) % MLKEM_Q);
        uint32_t v_ct_01 = mlkem_bf_sub(u01_i, p0_01);
        uint32_t u_gs_01 = mlkem_bf_div2(p1_01);
        uint32_t v_gs_01 = (uint32_t)((uint64_t)p3_01 * w01_i % MLKEM_Q);
        JG_BUFFER(p0_01); JG_BUFFER(p1_01); JG_BUFFER(p2_01); JG_BUFFER(p3_01);
        JG_BUFFER(u_ct_01); JG_BUFFER(v_ct_01); JG_BUFFER(u_gs_01); JG_BUFFER(v_gs_01);

        // ===== STAGE 2: bf_inst10(u10_int, v10_int, w10_i) =====
        // CT: u_in=u_ct_00, v_in=u_ct_01
        // GS: u_in=u_gs_00, v_in=u_gs_01
        uint32_t p0_10_ct = (uint32_t)((uint64_t)u_ct_01 * w10_i % MLKEM_Q);
        uint32_t p1_10_gs = (uint32_t)((u_gs_00 + u_gs_01) % MLKEM_Q);
        uint32_t p2_10_gs = mlkem_bf_sub(u_gs_00, u_gs_01);
        uint32_t p3_10_gs = mlkem_bf_div2(p2_10_gs);
        uint32_t u_ct_10  = (uint32_t)((u_ct_00 + p0_10_ct) % MLKEM_Q);
        uint32_t v_ct_10  = mlkem_bf_sub(u_ct_00, p0_10_ct);
        uint32_t u_gs_10  = mlkem_bf_div2(p1_10_gs);
        uint32_t v_gs_10  = (uint32_t)((uint64_t)p3_10_gs * w10_i % MLKEM_Q);
        JG_BUFFER(p0_10_ct); JG_BUFFER(p1_10_gs); JG_BUFFER(p2_10_gs); JG_BUFFER(p3_10_gs);
        JG_BUFFER(u_ct_10); JG_BUFFER(v_ct_10); JG_BUFFER(u_gs_10); JG_BUFFER(v_gs_10);

        // ===== STAGE 2: bf_inst11(u11_int, v11_int, w11_i) =====
        // CT: u_in=v_ct_00, v_in=v_ct_01
        // GS: u_in=v_gs_00, v_in=v_gs_01
        uint32_t p0_11_ct = (uint32_t)((uint64_t)v_ct_01 * w11_i % MLKEM_Q);
        uint32_t p1_11_gs = (uint32_t)((v_gs_00 + v_gs_01) % MLKEM_Q);
        uint32_t p2_11_gs = mlkem_bf_sub(v_gs_00, v_gs_01);
        uint32_t p3_11_gs = mlkem_bf_div2(p2_11_gs);
        uint32_t u_ct_11  = (uint32_t)((v_ct_00 + p0_11_ct) % MLKEM_Q);
        uint32_t v_ct_11  = mlkem_bf_sub(v_ct_00, p0_11_ct);
        uint32_t u_gs_11  = mlkem_bf_div2(p1_11_gs);
        uint32_t v_gs_11  = (uint32_t)((uint64_t)p3_11_gs * w11_i % MLKEM_Q);
        JG_BUFFER(p0_11_ct); JG_BUFFER(p1_11_gs); JG_BUFFER(p2_11_gs); JG_BUFFER(p3_11_gs);
        JG_BUFFER(u_ct_11); JG_BUFFER(v_ct_11); JG_BUFFER(u_gs_11); JG_BUFFER(v_gs_11);

        if (mode == 0u) {
            u20_o = u_ct_10; v20_o = v_ct_10;
            u21_o = u_ct_11; v21_o = v_ct_11;
        } else {
            u20_o = u_gs_10; v20_o = v_gs_10;
            u21_o = u_gs_11; v21_o = v_gs_11;
        }
        pwo_uv0 = 0u; pwo_uv1 = 0u;
        pwo_uv2 = 0u; pwo_uv3 = 0u;

    } else if (!mlkem && (mode == 0u || mode == 1u)) {
        // ================================================================
        // MLDSA CT (mode=0) / GS (mode=1) path — full 2-stage pipeline
        // All arithmetic uses MLDSA_Q = 8380417.
        // ================================================================

        // ===== STAGE 1: bf_inst00(u00_i, v00_i, w00_i) =====
        uint32_t p0_00 = (uint32_t)((uint64_t)v00_i * w00_i % MLDSA_Q);
        uint32_t p1_00 = (uint32_t)((u00_i + v00_i) % MLDSA_Q);
        uint32_t p2_00 = mldsa_sub(u00_i, v00_i);
        uint32_t p3_00 = mldsa_div2(p2_00);
        uint32_t u_ct_00 = (uint32_t)((u00_i + p0_00) % MLDSA_Q);
        uint32_t v_ct_00 = mldsa_sub(u00_i, p0_00);
        uint32_t u_gs_00 = mldsa_div2(p1_00);
        uint32_t v_gs_00 = (uint32_t)((uint64_t)p3_00 * w00_i % MLDSA_Q);
        JG_BUFFER(p0_00); JG_BUFFER(p1_00); JG_BUFFER(p2_00); JG_BUFFER(p3_00);
        JG_BUFFER(u_ct_00); JG_BUFFER(v_ct_00); JG_BUFFER(u_gs_00); JG_BUFFER(v_gs_00);

        // ===== STAGE 1: bf_inst01(u01_i, v01_i, w01_i) =====
        uint32_t p0_01 = (uint32_t)((uint64_t)v01_i * w01_i % MLDSA_Q);
        uint32_t p1_01 = (uint32_t)((u01_i + v01_i) % MLDSA_Q);
        uint32_t p2_01 = mldsa_sub(u01_i, v01_i);
        uint32_t p3_01 = mldsa_div2(p2_01);
        uint32_t u_ct_01 = (uint32_t)((u01_i + p0_01) % MLDSA_Q);
        uint32_t v_ct_01 = mldsa_sub(u01_i, p0_01);
        uint32_t u_gs_01 = mldsa_div2(p1_01);
        uint32_t v_gs_01 = (uint32_t)((uint64_t)p3_01 * w01_i % MLDSA_Q);
        JG_BUFFER(p0_01); JG_BUFFER(p1_01); JG_BUFFER(p2_01); JG_BUFFER(p3_01);
        JG_BUFFER(u_ct_01); JG_BUFFER(v_ct_01); JG_BUFFER(u_gs_01); JG_BUFFER(v_gs_01);

        // ===== STAGE 2: bf_inst10(u10_int, v10_int, w10_i) =====
        // CT: u_in=u_ct_00, v_in=u_ct_01
        // GS: u_in=u_gs_00, v_in=u_gs_01
        uint32_t p0_10_ct = (uint32_t)((uint64_t)u_ct_01 * w10_i % MLDSA_Q);
        uint32_t p1_10_gs = (uint32_t)((u_gs_00 + u_gs_01) % MLDSA_Q);
        uint32_t p2_10_gs = mldsa_sub(u_gs_00, u_gs_01);
        uint32_t p3_10_gs = mldsa_div2(p2_10_gs);
        uint32_t u_ct_10  = (uint32_t)((u_ct_00 + p0_10_ct) % MLDSA_Q);
        uint32_t v_ct_10  = mldsa_sub(u_ct_00, p0_10_ct);
        uint32_t u_gs_10  = mldsa_div2(p1_10_gs);
        uint32_t v_gs_10  = (uint32_t)((uint64_t)p3_10_gs * w10_i % MLDSA_Q);
        JG_BUFFER(p0_10_ct); JG_BUFFER(p1_10_gs); JG_BUFFER(p2_10_gs); JG_BUFFER(p3_10_gs);
        JG_BUFFER(u_ct_10); JG_BUFFER(v_ct_10); JG_BUFFER(u_gs_10); JG_BUFFER(v_gs_10);

        // ===== STAGE 2: bf_inst11(u11_int, v11_int, w11_i) =====
        // CT: u_in=v_ct_00, v_in=v_ct_01
        // GS: u_in=v_gs_00, v_in=v_gs_01
        uint32_t p0_11_ct = (uint32_t)((uint64_t)v_ct_01 * w11_i % MLDSA_Q);
        uint32_t p1_11_gs = (uint32_t)((v_gs_00 + v_gs_01) % MLDSA_Q);
        uint32_t p2_11_gs = mldsa_sub(v_gs_00, v_gs_01);
        uint32_t p3_11_gs = mldsa_div2(p2_11_gs);
        uint32_t u_ct_11  = (uint32_t)((v_ct_00 + p0_11_ct) % MLDSA_Q);
        uint32_t v_ct_11  = mldsa_sub(v_ct_00, p0_11_ct);
        uint32_t u_gs_11  = mldsa_div2(p1_11_gs);
        uint32_t v_gs_11  = (uint32_t)((uint64_t)p3_11_gs * w11_i % MLDSA_Q);
        JG_BUFFER(p0_11_ct); JG_BUFFER(p1_11_gs); JG_BUFFER(p2_11_gs); JG_BUFFER(p3_11_gs);
        JG_BUFFER(u_ct_11); JG_BUFFER(v_ct_11); JG_BUFFER(u_gs_11); JG_BUFFER(v_gs_11);

        if (mode == 0u) {
            u20_o = u_ct_10; v20_o = v_ct_10;
            u21_o = u_ct_11; v21_o = v_ct_11;
        } else {
            u20_o = u_gs_10; v20_o = v_gs_10;
            u21_o = u_gs_11; v21_o = v_gs_11;
        }
        pwo_uv0 = 0u; pwo_uv1 = 0u;
        pwo_uv2 = 0u; pwo_uv3 = 0u;

    } else {
        // Undefined / don't-care modes:
        //   mode=5, mlkem=0 (MLDSA pairwm): RTL hardwires ready_o=0; data unconstrained
        //   mode=6,7 (invalid): no assertions
        // Model all data outputs as 0 to avoid false counterexamples.
        u20_o   = 0u; v20_o   = 0u;
        u21_o   = 0u; v21_o   = 0u;
        pwo_uv0 = 0u; pwo_uv1 = 0u;
        pwo_uv2 = 0u; pwo_uv3 = 0u;
    }

    JG_OUTPUT(u20_o);    JG_OUTPUT(v20_o);
    JG_OUTPUT(u21_o);    JG_OUTPUT(v21_o);
    JG_OUTPUT(pwo_uv0);  JG_OUTPUT(pwo_uv1);
    JG_OUTPUT(pwo_uv2);  JG_OUTPUT(pwo_uv3);
}
