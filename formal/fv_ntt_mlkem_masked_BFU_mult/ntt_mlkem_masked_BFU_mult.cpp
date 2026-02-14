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
 
//typedef unsigned __int128 uint128_t;
#define Q 3329

int main () {
    uint32_t u0;
    uint32_t u1;
    uint32_t v0;
    uint32_t v1;
    uint32_t rnd0, rnd1, rnd2, rnd3, rnd4;
    uint32_t rndw;
    uint64_t mul_res;
    uint32_t mul_res_reduced;
 
    JG_INPUT(u0);
    JG_INPUT(u1);
    JG_INPUT(v1);
    JG_INPUT(v0);
    JG_INPUT(rnd0);
    JG_INPUT(rnd1);
    JG_INPUT(rnd2);
    JG_INPUT(rnd3);
    JG_INPUT(rnd4);
    JG_INPUT(rndw);

    mul_res = ((u0+u1)*(v0+v1));
    mul_res_reduced = mul_res % Q;
    
    JG_OUTPUT(mul_res);
    JG_OUTPUT(mul_res_reduced);
}
