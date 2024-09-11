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

def rejbounded(seed):
    global DILITHIUM_Q
    global DILITHIUM_N
    global DILITHIUM_ETA
    global DILITHIUM_ETA_BOUND
    global buff_arr

    def rejection_sample(xof):
        global buff_arr
        while True:
            js = []
            if (len(buff_arr) == 0):
                log_file.write("squeezing\n")
                buff_bytes = xof.read(136)
                buff_arr = bytearray(buff_bytes)
                buff_int = int.from_bytes(buff_bytes, "little")
                input_vectors.write(f"{buff_int:0272x}")
            j = buff_arr[0]
            buff_arr.pop(0)
            log_file.write("byte: " + f"{j:02x}" + "\n")
            # Consider two values for each byte (top and bottom four bits)
            j0 = j & 0x0F
            j1 = j >> 4
            
            # rejection sample
            if j0 < DILITHIUM_ETA_BOUND:
                if DILITHIUM_ETA == 2: j0 %= 5
                log_file.write("ack: " + f"{j0:01x}" + "\n")
                js.append((DILITHIUM_ETA - j0) % DILITHIUM_Q)
            else: log_file.write("rej: " + f"{j0:01x}" + "\n")
            if j1 < DILITHIUM_ETA_BOUND:
                if DILITHIUM_ETA == 2: j1 %= 5
                log_file.write("ack: " + f"{j1:01x}" + "\n")
                js.append((DILITHIUM_ETA - j1) % DILITHIUM_Q)
            else: log_file.write("rej: " + f"{j1:01x}" + "\n")
            
            if js:
                return js
                
    # Initialise the XOF
    Shake256.absorb(seed)
    buff_arr = bytearray()
    coeffs = []
    while len(coeffs) < DILITHIUM_N:
        js = rejection_sample(Shake256)
        coeffs += js

    # Remove the last byte if we ended up overfilling
    if len(coeffs) > DILITHIUM_N:
        coeffs = coeffs[:DILITHIUM_N]
    
    return coeffs

#open the input vector file for reading
input_seeds = open("input_seeds.txt", "r")
input_vectors = open("input_vectors.txt", "w")
exp_results = open("exp_results.txt", "w")
log_file = open("rej_bounded.log", "w")
Lines = input_seeds.readlines()

for line in Lines:
    Coeffs = rejbounded( bytes(line.strip(),'utf-8') )
    for coeff in Coeffs:
        exp_results.write(f"{coeff:06x}"+" ")
    input_vectors.write("\n")
    exp_results.write("\n")
