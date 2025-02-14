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
import random

DILITHIUM_Q = 8380417 # 2**23 - 2**13 + 1
DILITHIUM_N = 256
DILITHIUM_LOGN = 8
DILITHIUM_ROOT_OF_UNITY = 1753

## Category 5 parameters:
DILITHIUM_K = 8
DILITHIUM_L = 7
DILITHIUM_GAMMA2 = (DILITHIUM_Q -1)// 32
DILITHIUM_OMEGA = 75


def make_hint_poly(v1, v2):
    return [[make_hint(r, z) for r, z in zip(p1, p2)] for p1, p2 in zip(v1, v2)]

def make_hint(r, z):
    if (r <= DILITHIUM_GAMMA2) or (r > (DILITHIUM_Q - DILITHIUM_GAMMA2)) or (r == (DILITHIUM_Q - DILITHIUM_GAMMA2) and z == 0):
        return 0
    return 1

def sum_hint(hint):
    return sum(sum(row) for row in hint)


# Adjusted random input generation
def generate_biased_random_inputs():
    #w0_minus_cs2_plus_ct0 = [[random.randint(0, DILITHIUM_Q - 1) for _ in range(DILITHIUM_N)] for poly_i in range(DILITHIUM_K)]
    w0_minus_cs2_plus_ct0 = [[0] * DILITHIUM_N for _ in range(DILITHIUM_K)]
    for poly_idx in range(DILITHIUM_K):
        for coeff_idx in range(DILITHIUM_N):
            if random.random() < 0.5:
                w0_minus_cs2_plus_ct0[poly_idx][coeff_idx] = random.randint(0, DILITHIUM_GAMMA2)
            else:
                w0_minus_cs2_plus_ct0[poly_idx][coeff_idx] = random.randint(DILITHIUM_Q - DILITHIUM_GAMMA2, DILITHIUM_Q - 1)

    total_ones = random.randint(0, 200)  # Control the number of ones
    ones_positions = random.sample(range(DILITHIUM_K * DILITHIUM_N), total_ones)

    for pos in ones_positions:
        poly_idx = pos // DILITHIUM_N
        coeff_idx = pos % DILITHIUM_N
        w0_minus_cs2_plus_ct0[poly_idx][coeff_idx] = random.randint(0, DILITHIUM_Q - 1)

    return w0_minus_cs2_plus_ct0


# Generate controlled input
w0_minus_cs2_plus_ct0 = generate_biased_random_inputs()
w1 = [[random.randint(0, 15) for _ in range(DILITHIUM_N)] for _ in range(DILITHIUM_K)]
h = make_hint_poly(w0_minus_cs2_plus_ct0, w1)   

print("w0_minus_cs2_plus_ct0=", w0_minus_cs2_plus_ct0)
print("w1=", w1)
print("h=",h)

print(sum_hint(h))
if sum_hint(h) <= DILITHIUM_OMEGA:
    print("successful")
else:
    print("failed")