# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
import numpy as np
import random

DILITHIUM_Q = 8380417 # 2**23 - 2**13 + 1
DILITHIUM_N = 256
DILITHIUM_K = 8
DILITHIUM_D = 13


def vec_power2round(t):
    coeff_high = []
    coeff_low  = []
    for poly_i in t:
        r1, r0 = poly_power2round(poly_i)
        coeff_high.append(r1)
        coeff_low.append(r0)
    return coeff_high, coeff_low

def poly_power2round(poly):
    r1_coeffs = []
    r0_coeffs = []
    for coeff_i in poly:
        r1, r0 = power2round(coeff_i)
        r1_coeffs.append(r1)
        r0_coeffs.append(r0)    
    return r1_coeffs, r0_coeffs

def power2round(coeff):
    power_2 = (1 << DILITHIUM_D-1)
    r  = coeff % DILITHIUM_Q
    r1 = (r + (power_2 - 1)) >> DILITHIUM_D
    r0 = r - (r1 << DILITHIUM_D)
    return r1, r0

def skencode(value):
    value_encodede = (1 << (DILITHIUM_D-1)) - value
    return f"{value_encodede:0X}"

vec = []
for _ in range(DILITHIUM_K):
    poly = [random.randrange(DILITHIUM_Q) for _ in range(DILITHIUM_N)]
    vec.append(poly)

coeff_high, coeff_low = vec_power2round(vec)

# Export to files
with open("coeff_input.hex", "w") as input_file, \
    open("coeff_high.hex", "w") as high_file, \
    open("coeff_low.hex", "w") as low_file:
    
    for poly_index, (r1_coeffs, r0_coeffs) in enumerate(zip(coeff_high, coeff_low)):
        for i in range(DILITHIUM_N):
            input_file.write(f"{vec[poly_index][i]:06X}\n")
            high_file.write(f"{r1_coeffs[i]:X}\n")
            low_file.write(f"{skencode(r0_coeffs[i])}\n")
