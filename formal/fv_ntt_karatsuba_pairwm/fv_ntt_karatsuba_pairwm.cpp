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
#include <cstdint>

int main(){

    //Input width is all 24 bits
    uint32_t z;
    uint32_t u0;
    uint32_t u1;
    uint32_t v0;
    uint32_t v1; 
    uint32_t w0;
    uint32_t w1;
    bool accumulate;


    JASPER_INPUT(z);
    JASPER_INPUT(u0);
    JASPER_INPUT(u1);
    JASPER_INPUT(v0);
    JASPER_INPUT(v1);
    JASPER_INPUT(w0);
    JASPER_INPUT(w1);
    JASPER_INPUT(accumulate);


    
}