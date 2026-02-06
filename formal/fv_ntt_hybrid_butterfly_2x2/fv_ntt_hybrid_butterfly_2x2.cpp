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

typedef unsigned __int128 uint128_t; 

uint32_t compute_a_min_b (uint32_t a, uint32_t b) {
    if (a >= b) {
        return (a - b);
    }
    else {
        return (a - b + 0xD01);
    }
}

uint32_t compute_a_min_b_mldsa (uint32_t a, uint32_t b) {
    if (a >= b) {
        return (a - b);
    }
    else {
        return (a - b + 0x7FE001);
    }
}

uint32_t div2_mldsa(uint32_t data) {
    uint32_t result = 0;
    if (data % 2 == 1) {
        result = (data >> 1) + uint32_t ((0x7FE001 + 1) / 2);
    }
    else {
        result = data >> 1;
    }
    return result;
}

uint32_t div2(uint32_t data) {
    uint32_t result = 0;
    if (data % 2 == 1) {
        result = (data >> 1) + uint32_t ((0xD01 + 1) / 2);
    }
    else {
        result = data >> 1;
    }
    return result;
}

int main () {

    
    uint32_t u00_0;
    uint32_t u00_1;
    uint32_t u01_0;
    uint32_t u01_1;
    uint32_t v00_0;
    uint32_t v00_1;
    uint32_t v01_0;
    uint32_t v01_1;
    uint32_t w00_0;
    uint32_t w00_1;
    uint32_t w01_0;
    uint32_t w01_1;
    
    uint32_t u10_0;
    uint32_t u10_1;
    uint32_t u11_0;
    uint32_t u11_1;
    uint32_t v10_0;
    uint32_t v10_1;
    uint32_t v11_0;
    uint32_t v11_1;
    uint32_t w10_0;
    uint32_t w10_1;
    uint32_t w11_0;
    uint32_t w11_1;
    
    uint32_t u00;
    uint32_t v00;
    uint32_t w00;

    uint32_t u01;
    uint32_t v01;
    uint32_t w01;

    uint32_t w10;
    uint32_t w11;

    uint64_t u0_0;
    uint64_t u0_1;
    uint64_t u1_0;
    uint64_t u1_1;
    uint64_t u2_0;
    uint64_t u2_1;
    uint64_t u3_0;
    uint64_t u3_1;
    uint64_t v0_0;
    uint64_t v0_1;
    uint64_t v1_0;
    uint64_t v1_1;
    uint64_t v2_0;
    uint64_t v2_1;
    uint64_t v3_0;
    uint64_t v3_1;
    uint64_t w0_0;
    uint64_t w0_1;
    uint64_t w1_0;
    uint64_t w1_1;
    uint64_t w2_0;
    uint64_t w2_1;
    uint64_t w3_0;
    uint64_t w3_1;
    bool acc;
    bool mlkem;
    uint8_t mode;
    bool masking_en;
    bool intt_passthrough;
    bool ntt_passthrough;

    uint64_t rnd0, rnd1, rnd2, rnd3, rnd4, p4, u_ct_mldsa, v_gs_mldsa, p8, pwm_res_o;
    uint32_t p0_0, p1_0, p2_0, p3_0, u_ct_mlkem, v_ct_mlkem, u_gs_mlkem, v_gs_mlkem;
    uint32_t p0_1, p1_1, p2_1, p3_1, u_ct_mlkem_1, v_ct_mlkem_1, u_gs_mlkem_1, v_gs_mlkem_1;
    uint32_t p0_2, p1_2, p2_2, p3_2, u_ct_mlkem_2, v_ct_mlkem_2, u_gs_mlkem_2, v_gs_mlkem_2;
    uint32_t p0_3, p1_3, p2_3, p3_3, u_ct_mlkem_3, v_ct_mlkem_3, u_gs_mlkem_3, v_gs_mlkem_3;

    uint32_t u10_div2;
    uint32_t u11_div2;
    uint32_t v10_div2;
    uint32_t v11_div2;

    uint32_t v10_int_0;
    uint32_t v10_int_1;
    uint32_t v11_int_0;
    uint32_t v11_int_1;
 
    uint64_t u10_int, u11_int, v10_comb, v11_comb;
    uint32_t sub_res_0, sub_res_1;
    uint128_t pp0, pp1, pp2, pp3, sum;
 
    JG_INPUT(u00);
    JG_INPUT(v00);
    JG_INPUT(w00);
    JG_INPUT(u01);
    JG_INPUT(v01);
    JG_INPUT(w01);
    JG_INPUT(w10);
    JG_INPUT(w11);
    JG_INPUT(u0_0);
    JG_INPUT(u0_1);
    JG_INPUT(v0_0);
    JG_INPUT(v0_1);
    JG_INPUT(w0_0);
    JG_INPUT(w0_1);
    JG_INPUT(u1_0);
    JG_INPUT(u1_1);
    JG_INPUT(v1_0);
    JG_INPUT(v1_1);
    JG_INPUT(w1_0);
    JG_INPUT(w1_1);
    JG_INPUT(u00_0);
    JG_INPUT(u00_1);
    JG_INPUT(v00_0);
    JG_INPUT(v00_1);
    JG_INPUT(u01_0);
    JG_INPUT(u01_1);
    JG_INPUT(v01_0);
    JG_INPUT(v01_1);
    JG_INPUT(rnd0);
    JG_INPUT(rnd1);
    JG_INPUT(rnd2);
    JG_INPUT(rnd3);
    JG_INPUT(rnd4);
    JG_INPUT(acc);
    JG_INPUT(mlkem);
    JG_INPUT(mode);
    JG_INPUT(masking_en);
    JG_INPUT(intt_passthrough);
    JG_INPUT(ntt_passthrough);
    JG_INPUT(v10_int_0);
    JG_INPUT(v10_int_1);
    JG_INPUT(v11_int_0);
    JG_INPUT(v11_int_1);


    //ntt butterfly 1x2 checks first masked gs bfu instance
    u10_int = ((u00_0 + u00_1 + v00_0 + v00_1) % (uint64_t)0xD01);
    //v10_int = ((compute_a_min_b((u00_0 + u00_1), (v00_0 + v00_1)) * (w00_0 + w00_1)) % (uint64_t)0xD01);
    v10_comb = (v10_int_0 + v10_int_1) % (uint64_t)0xD01;
    sub_res_0 = compute_a_min_b((u00_0 + u00_1), (v00_0 + v00_1));
    JG_BUFFER(u10_int);
    //JG_BUFFER(v10_int);
    JG_BUFFER(sub_res_0);
    JG_BUFFER(v10_comb);

    u11_int = ((u01_0 + u01_1 + v01_0 + v01_1) % (uint64_t)0xD01);
    //v10_int = ((compute_a_min_b((u00_0 + u00_1), (v00_0 + v00_1)) * (w00_0 + w00_1)) % (uint64_t)0xD01);
    v11_comb = (v11_int_0 + v11_int_1) % (uint64_t)0xD01;
    sub_res_1 = compute_a_min_b((u01_0 + u01_1), (v01_0 + v01_1));
    JG_BUFFER(u11_int);
    //JG_BUFFER(v10_int);
    JG_BUFFER(sub_res_1);
    JG_BUFFER(v11_comb);

    u10_div2 = div2(u10_int);
    v10_div2 = div2(v10_comb);
    JG_OUTPUT(u10_div2);
    JG_OUTPUT(v10_div2);

    u11_div2 = div2(u11_int);
    v11_div2 = div2(v11_comb);
    JG_OUTPUT(u11_div2);
    JG_OUTPUT(v11_div2);
    

    //NTT Butterfly 1st stage CT & GS mode output checks
    if (!intt_passthrough) {
        p0_0 = (v00 * w00) % (uint32_t)0xD01;
        p1_0 = (u00 + v00) % (uint32_t)0xD01;
        p2_0 = compute_a_min_b(u00, v00);
        p3_0 = div2(p2_0);
        u_ct_mlkem = (u00 + p0_0) % (uint32_t)0xD01;
        v_ct_mlkem = compute_a_min_b(u00, p0_0);
        u_gs_mlkem = div2(p1_0);
        v_gs_mlkem = (p3_0 * w00) % (uint32_t)0xD01;
        p0_1 = (v01 * w01) % (uint32_t)0xD01;
        p1_1 = (u01 + v01) % (uint32_t)0xD01;
        p2_1 = compute_a_min_b(u01, v01);
        p3_1 = div2(p2_1);
        u_ct_mlkem_1 = (u01 + p0_1) % (uint32_t)0xD01;
        v_ct_mlkem_1 = compute_a_min_b(u01, p0_1);
        u_gs_mlkem_1 = div2(p1_1);
        v_gs_mlkem_1 = (p3_1 * w01) % (uint32_t)0xD01;
    }
    else {
        p0_0 = (u01 * w10) % (uint32_t)0xD01;
        p1_0 = (u00 + u01) % (uint32_t)0xD01;
        p2_0 = compute_a_min_b(u00, u01);
        p3_0 = div2(p2_0);
        u_ct_mlkem = (u00 + p0_0) % (uint32_t)0xD01;
        v_ct_mlkem = compute_a_min_b(u00, p0_0);
        u_gs_mlkem = div2(p1_0);
        v_gs_mlkem = (p3_0 * w10) % (uint32_t)0xD01;
        p0_1 = (v01 * w11) % (uint32_t)0xD01;
        p1_1 = (v00 + v01) % (uint32_t)0xD01;
        p2_1 = compute_a_min_b(v00, v01);
        p3_1 = div2(p2_1);
        u_ct_mlkem_1 = (v00 + p0_1) % (uint32_t)0xD01;
        v_ct_mlkem_1 = compute_a_min_b(v00, p0_1);
        u_gs_mlkem_1 = div2(p1_1);
        v_gs_mlkem_1 = (p3_1 * w11) % (uint32_t)0xD01;
    }
    JG_BUFFER(p0_0);
    JG_BUFFER(p1_0);
    JG_BUFFER(p2_0);
    JG_BUFFER(p3_0);
    JG_BUFFER(u_ct_mlkem);
    JG_BUFFER(v_ct_mlkem);
    JG_BUFFER(u_gs_mlkem);
    JG_BUFFER(v_gs_mlkem);
    JG_BUFFER(p0_1);
    JG_BUFFER(p1_1);
    JG_BUFFER(p2_1);
    JG_BUFFER(p3_1);
    JG_BUFFER(u_ct_mlkem_1);
    JG_BUFFER(v_ct_mlkem_1);
    JG_BUFFER(u_gs_mlkem_1);
    JG_BUFFER(v_gs_mlkem_1);

    //NTT Butterfly 2nd stage CT & GS mode output checks. 
    // CT: u10 = u_ct_mlkem, v10 = u_ct_mlkem_1, u11 = v_ct_mlkem, v11 = v_ct_mlkem_1
    // GS: u10 = u_gs_mlkem, v10 = u_gs_mlkem_1, u11 = v_gs_mlkem, v11 = v_gs_mlkem_1
    p0_2 = (u_ct_mlkem_1 * w10) % (uint32_t)0xD01;
    p1_2 = (u_gs_mlkem + u_gs_mlkem_1) % (uint32_t)0xD01;
    p2_2 = compute_a_min_b(u_gs_mlkem, u_gs_mlkem_1);
    p3_2 = div2(p2_2);
    u_ct_mlkem_2 = (u_ct_mlkem + p0_2) % (uint32_t)0xD01;
    v_ct_mlkem_2 = compute_a_min_b(u_ct_mlkem, p0_2);
    u_gs_mlkem_2 = div2(p1_2);
    v_gs_mlkem_2 = (p3_2 * w10) % (uint32_t)0xD01;

    p0_3 = (v_ct_mlkem_1 * w11) % (uint32_t)0xD01;
    p1_3 = (v_gs_mlkem + v_gs_mlkem_1) % (uint32_t)0xD01;
    p2_3 = compute_a_min_b(v_gs_mlkem, v_gs_mlkem_1);
    p3_3 = div2(p2_3);
    u_ct_mlkem_3 = (v_ct_mlkem + p0_3) % (uint32_t)0xD01;
    v_ct_mlkem_3 = compute_a_min_b(v_ct_mlkem, p0_3);
    u_gs_mlkem_3 = div2(p1_3);
    v_gs_mlkem_3 = (p3_3 * w11) % (uint32_t)0xD01;

    JG_BUFFER(p0_2);
    JG_BUFFER(p1_2);
    JG_BUFFER(p2_2);
    JG_BUFFER(p3_2);
    JG_BUFFER(u_ct_mlkem_2);
    JG_BUFFER(v_ct_mlkem_2);
    JG_BUFFER(u_gs_mlkem_2);
    JG_BUFFER(v_gs_mlkem_2);
    JG_BUFFER(p0_3);
    JG_BUFFER(p1_3);
    JG_BUFFER(p2_3);
    JG_BUFFER(p3_3);
    JG_BUFFER(u_ct_mlkem_3);
    JG_BUFFER(v_ct_mlkem_3);
    JG_BUFFER(u_gs_mlkem_3);
    JG_BUFFER(v_gs_mlkem_3);

}