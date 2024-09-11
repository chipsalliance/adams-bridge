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
import sys
import os
import binascii
from hashlib import shake_128, shake_256

DILITHIUM_Q = 8380417 # 2**23 - 2**13 + 1
DILITHIUM_N = 256
DILITHIUM_LOGN = 8
DILITHIUM_ROOT_OF_UNITY = 1753

## Category 5 parameters:
DILITHIUM_ETA = 2
DILITHIUM_ETA_BOUND = 15
DILITHIUM_TAU = 60
DILITHIUM_GAMMA1 = 2**19


class Shake():
    def __init__(self, algorithm, block_length):
        self.algorithm    = algorithm
        self.block_length = block_length
        self.read_blocks  = 0
        self.read_data    = b""
        
    def absorb(self, input_bytes):
        self.read_blocks  = 0
        self.read_data    = b""
        self.xof = self.algorithm(input_bytes)
        
    def digest(self, input_bytes, length):
        return self.algorithm(input_bytes).digest(length)
        
    def get_n_blocks(self, n):
        byte_count = self.block_length * (self.read_blocks + n)
        xof_data   = self.xof.digest(byte_count)
        self.read_blocks += n
        self.read_data = xof_data[-self.block_length*n:]
    
    def read(self, n):
        if n > len(self.read_data):
            self.get_n_blocks(5*n)
        send = self.read_data[:n]
        self.read_data = self.read_data[n:]
        return send

Shake128 = Shake(shake_128, 168)
Shake256 = Shake(shake_256, 136)

def expand_mask(seed):                            
    global DILITHIUM_Q
    global DILITHIUM_N
    global DILITHIUM_GAMMA1

    if DILITHIUM_GAMMA1 == (1 << 17):
        bit_count = 18
        total_bytes = 576 # (256 * 18) / 8
    else:
        bit_count = 20
        total_bytes = 680 # multiple of Shake256 640 # (256 * 20) / 8
    
    # Initialise the XOF
    xof_bytes = Shake256.digest(seed, total_bytes)
    r = int.from_bytes(xof_bytes, 'little')
    input_vectors.write(f"{r:01360x}")
    mask = (1 << bit_count) - 1
    coeffs = [((DILITHIUM_GAMMA1 - ((r >> bit_count*i) & mask)) % DILITHIUM_Q) for i in range(DILITHIUM_N)]
    
    return coeffs

#open the input vector file for reading
input_seeds = open("input_seeds.txt", "r")
input_vectors = open("input_vectors.txt", "w")
exp_results = open("exp_results.txt", "w")
log_file = open("rej_sampler.log", "w")
Lines = input_seeds.readlines()

for line in Lines:
    Coeffs = expand_mask( bytes(line.strip(),'utf-8') )
    for coeff in Coeffs:
        exp_results.write(f"{coeff:06x}"+" ")
    input_vectors.write("\n")
    exp_results.write("\n")


