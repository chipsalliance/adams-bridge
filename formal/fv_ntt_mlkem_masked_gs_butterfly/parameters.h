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

#include <cmath>
// Parameters from masked_gadget.py
const uint64_t numOfBits =  12;
const uint64_t MultMod  =  uint64_t(pow(2,numOfBits)); // 2**12 = 4096
const uint64_t MLKEM_Q  =  3329 ;
const uint64_t BooleanMod  =  uint64_t(pow(2,int(numOfBits/2))); // 2**6 = 64
const uint64_t Roller =  uint64_t(pow(2,9) + pow(2,8) - 1); // 2**9 + 2**8 - 1 = 768
const uint64_t MLKEM_N  = 256;
const uint64_t MLKEM_LOGN =  7;
const uint64_t ModulArithBits = uint64_t(numOfBits/2);// 6 bits for arithmetic operations