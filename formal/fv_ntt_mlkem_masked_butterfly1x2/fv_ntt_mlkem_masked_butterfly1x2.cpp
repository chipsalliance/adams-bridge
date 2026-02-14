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
 

uint32_t compute_a_min_b (uint32_t a, uint32_t b) {
    if (a >= b) {
        return (a - b);
    }
    else {
        return (a - b + 0xD01);
    }
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
    uint32_t rnd0, rnd1, rnd2, rnd3, rnd4;
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
 
    JG_INPUT(u00_0);
    JG_INPUT(u00_1);
    JG_INPUT(u01_0);
    JG_INPUT(u01_1);
    JG_INPUT(v00_0);
    JG_INPUT(v00_1);
    JG_INPUT(v01_0);
    JG_INPUT(v01_1);
    JG_INPUT(w00_0);
    JG_INPUT(w00_1);
    JG_INPUT(w01_0);
    JG_INPUT(w01_1);
    JG_INPUT(v10_int_0);
    JG_INPUT(v10_int_1);
    JG_INPUT(v11_int_0);
    JG_INPUT(v11_int_1);
    JG_INPUT(rnd0);
    JG_INPUT(rnd1);
    JG_INPUT(rnd2);
    JG_INPUT(rnd3);
    JG_INPUT(rnd4);

    
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
 
}