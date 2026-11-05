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

#define MLDSA_Q          8380417U
#define MLKEM_Q          3329U
#define MLDSA_Q_DIV2_ODD 4190209U   // (8380417+1)/2
#define MLKEM_Q_DIV2_ODD 1665U      // (3329+1)/2

uint32_t mod_sub(uint32_t a, uint32_t b, uint32_t Q) {
    if (a >= b) return a - b;
    return a - b + Q;
}

uint32_t div2_modQ(uint32_t data, bool mlkem) {
    uint32_t half_Q1 = mlkem ? MLKEM_Q_DIV2_ODD : MLDSA_Q_DIV2_ODD;
    if (data % 2 == 1) return (data >> 1) + half_Q1;
    return data >> 1;
}

int main() {

    // ---- Primary inputs ----
    uint32_t opu_i, opv_i, opw_i;
    uint8_t  mode;
    bool     accumulate, mlkem;

    JG_INPUT(opu_i);
    JG_INPUT(opv_i);
    JG_INPUT(opw_i);
    JG_INPUT(mode);
    JG_INPUT(accumulate);
    JG_INPUT(mlkem);

    // ---- Input constraints ----
    uint32_t Q = mlkem ? MLKEM_Q : MLDSA_Q;
    JG_ASSUME(opu_i < Q, assume_opu_range);
    JG_ASSUME(opv_i < Q, assume_opv_range);
    JG_ASSUME(opw_i < Q, assume_opw_range);
    JG_ASSUME(mode <= 5, assume_mode_range);

    // ---- Multiplier operands (combinational) ----
    uint32_t mul_opa, mul_opb;
    uint32_t u_minus_v = mod_sub(opu_i, opv_i, Q);

    if (mode == 0) {        // CT: v * w
        mul_opa = opv_i;
        mul_opb = opw_i;
    } else if (mode == 1) { // GS: div2(u-v) * w
        mul_opa = div2_modQ(u_minus_v, mlkem);
        mul_opb = opw_i;
    } else if (mode == 2) { // PWM: u * v
        mul_opa = opu_i;
        mul_opb = opv_i;
    } else if (mode == 5) { // PAIRWM (MLKEM only): u * v
        mul_opa = mlkem ? opu_i : 0;
        mul_opb = mlkem ? opv_i : 0;
    } else {                // PWA, PWS: no multiply
        mul_opa = 0;
        mul_opb = 0;
    }

    JG_OUTPUT(mul_opa);
    JG_OUTPUT(mul_opb);

    // ---- Multiplication pipeline (2 registers) ----
    // mul_res_reg (cycle +1) -> *_mul_res_reduced_reg (cycle +2)
    uint64_t mul_res = (uint64_t)mul_opa * (uint64_t)mul_opb;
    JG_BUFFER(mul_res);

    uint32_t mul_res_reduced = (uint32_t)(mul_res % Q);
    JG_BUFFER(mul_res_reduced);

    // ---- PAIRWM dedicated output: explicit 2-register pipeline ----
    // JG_BUFFER on intermediate variables, then a plain assignment to the output-named
    // variable with JG_OUTPUT placed immediately after. This avoids the depth-inference
    // issue (ternary-else-0 gives depth 0) and also avoids calling JG_BUFFER + JG_OUTPUT
    // on the same variable non-contiguously (which the tool cannot resolve cleanly).
    uint32_t pairwm_reg1 = (mode == 5 && mlkem) ? (uint32_t)((uint64_t)opu_i * (uint64_t)opv_i) : 0U;
    JG_BUFFER(pairwm_reg1);                           // register stage 1 (cycle +1)
    uint32_t pairwm_reg2 = pairwm_reg1 % MLKEM_Q;
    JG_BUFFER(pairwm_reg2);                           // register stage 2 (cycle +2)
    uint32_t pairwm_mul_red_o = pairwm_reg2;          // name the output — no JG_BUFFER here
    JG_OUTPUT(pairwm_mul_red_o);                      // check at depth 2 against RTL port


    // ---- Adder/subtracter pipeline (1 register via abr_ntt_add_sub_mod) ----
    uint32_t add_res = 0, sub_res = 0;

    if (mode == 0) {        // CT: u_reg_d2 + mul_res_reduced
        add_res = (opu_i + mul_res_reduced) % Q;
        sub_res = mod_sub(opu_i, mul_res_reduced, Q);
    } else if (mode == 1) { // GS: opu_i + opv_i
        add_res = (opu_i + opv_i) % Q;
    } else if (mode == 2) { // PWM (MLDSA): w_reg_d2 + mul_res_reduced
        add_res = !mlkem ? (opw_i + mul_res_reduced) % Q : 0;
    } else if (mode == 3) { // PWA: u + v
        add_res = (opu_i + opv_i) % Q;
    } else if (mode == 4) { // PWS: u - v
        sub_res = mod_sub(opu_i, opv_i, Q);
    }

    JG_BUFFER(add_res);         // add_res_d1

    uint32_t add_res_d2 = add_res;
    JG_BUFFER(add_res_d2);      // add_res_d2

    // ---- Output computation per mode ----
    uint32_t u_o, v_o, pwm_res_o;

    if (mode == 0) {        // CT
        u_o       = add_res;
        v_o       = sub_res;
        pwm_res_o = 0;
    } else if (mode == 1) { // GS
        u_o       = div2_modQ(add_res_d2, mlkem);   // div2((u+v) % Q)
        v_o       = mul_res_reduced;                 // (div2(u-v) * w) % Q
        pwm_res_o = 0;
    } else if (mode == 2) { // PWM
        u_o       = 0;
        v_o       = 0;
        pwm_res_o = mlkem ? 0 : (accumulate ? add_res : mul_res_reduced);
    } else if (mode == 3) { // PWA
        u_o       = 0;
        v_o       = 0;
        pwm_res_o = add_res;
    } else if (mode == 4) { // PWS
        u_o       = 0;
        v_o       = 0;
        pwm_res_o = sub_res;
    } else {                // PAIRWM (mode == 5, MLKEM only)
        u_o       = 0;
        v_o       = 0;
        pwm_res_o = 0;
    }

    JG_OUTPUT(u_o);
    JG_OUTPUT(v_o);
    JG_OUTPUT(pwm_res_o);
    return 0;
}
