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
// MLKEM Karatsuba pair-wise multiplier reference:
//   uv0_o   = (m0 + m1*zeta)          mod Q   (+ w0 when accumulate)
//   uv1_o   = (m2 - m0 - m1)          mod Q   (+ w1 when accumulate)


#include "jasperc.h"
#include <cstdint>

// MLKEM prime. All field elements are assumed < Q (enforced by tcl assumptions).
const uint32_t MLKEM_Q = 3329; // 0xD01

// (a + b) mod Q.  a,b < Q  =>  a+b < 2*Q, fits in uint32_t.
uint32_t add_modQ(uint32_t a, uint32_t b) {
    return (a + b) % MLKEM_Q;
}

// (a - b) mod Q with wrap-around.  a,b < Q  =>  result in [0, Q).
uint32_t sub_modQ(uint32_t a, uint32_t b) {
    return (a >= b) ? (a - b) : (a - b + MLKEM_Q);
}

// (a * b) mod Q.
uint32_t mult_modQ(uint32_t a, uint32_t b) {
    return (a * b) % MLKEM_Q;
}

int main() {

    uint32_t u0;   // pwo_uvw_i.u0_i
    uint32_t u1;   // pwo_uvw_i.u1_i
    uint32_t v0;   // pwo_uvw_i.v0_i
    uint32_t v1;   // pwo_uvw_i.v1_i
    uint32_t w0;   // pwo_uvw_i.w0_i  
    uint32_t w1;   // pwo_uvw_i.w1_i  
    uint32_t z;    // pwo_z_i         (zeta)
    uint32_t m0;   // m0_red_i        (BF-tap: u0*v0 mod Q)
    uint32_t m1;   // m1_red_i        (BF-tap: u1*v1 mod Q)
    bool     accumulate;

    uint32_t uv0;
    uint32_t uv1;
    uint32_t add_res_u;

    JG_INPUT(u0);
    JG_INPUT(u1);
    JG_INPUT(v0);
    JG_INPUT(v1);
    JG_INPUT(w0);
    JG_INPUT(w1);
    JG_INPUT(z);
    JG_INPUT(m0);
    JG_INPUT(m1);
    JG_INPUT(accumulate);

    // ---- Stage 1: pre-add  sum_a = u0+u1 mod Q, sum_b = v0+v1 mod Q --------
    add_res_u = add_modQ(u0, u1);
    uint32_t add_res_v = add_modQ(v0, v1);
    JG_BUFFER(add_res_u);
    JG_BUFFER(add_res_v);

    // ---- Stage 2: m2 = sum_a * sum_b mod Q  (comb mult + Barrett) ----------
    uint32_t m2_red = mult_modQ(add_res_u, add_res_v);
    JG_BUFFER(m2_red);

    // ---- Stage 2: m1*zeta mod Q  (comb mult + Barrett) --------------------
    uint32_t m1z_red = mult_modQ(m1, z);
    JG_BUFFER(m1z_red);

    // ---- Stage 3: c1_int = m2 - m0 mod Q ----------------------------------
    uint32_t c1_int = sub_modQ(m2_red, m0);
    JG_BUFFER(c1_int);

    // ---- Stage 4: pre-mux results -----------------------------------------
    uint32_t uv0_o_int = add_modQ(m1z_red, m0);
    uint32_t uv1_o_int = sub_modQ(c1_int, m1);

    // ---- Stage 5: accumulate path ------------------
    uint32_t uv0_o_acc = add_modQ(uv0_o_int, w0);
    uint32_t uv1_o_acc = add_modQ(uv1_o_int, w1);

    // ---- Output mux: select accumulate vs non-accumulate result ----------
    uv0 = accumulate ? uv0_o_acc : uv0_o_int; // pwo_uv_o.uv0_o
    uv1 = accumulate ? uv1_o_acc : uv1_o_int; // pwo_uv_o.uv1_o
    JG_OUTPUT(uv0);
    JG_OUTPUT(uv1);

    return 0;
}
