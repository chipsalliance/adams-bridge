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

int main() {


    uint32_t u00_0;
    uint32_t u00_1;
    uint32_t v00_0;
    uint32_t v00_1;
    uint32_t w00_0;
    uint32_t w00_1;

    uint32_t add_res_0, add_res_1, sub_res_0;

    JG_INPUT(u00_0);
    JG_INPUT(u00_1);
    JG_INPUT(v00_0);
    JG_INPUT(v00_1);

    add_res_0 = ((u00_0 + u00_1 + v00_0 + v00_1) % (uint64_t)0xD01);
    sub_res_0 = compute_a_min_b((u00_0 + u00_1), (v00_0 + v00_1));
    JG_BUFFER(add_res_0);
    JG_BUFFER(sub_res_0);


}