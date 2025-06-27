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
from hashlib import shake_128

# Constants for MLKEM
MLKEM_Q = 3329
MLKEM_N = 256

class Shake:
    def __init__(self, algorithm, block_length):
        self.algorithm = algorithm
        self.block_length = block_length
        self.read_blocks = 0
        self.read_data = b""

    def absorb(self, input_bytes):
        self.read_blocks = 0
        self.read_data = b""
        self.xof = self.algorithm(input_bytes)

    def read(self, n):
        if n > len(self.read_data):
            self._get_n_blocks(5 * n)
        result = self.read_data[:n]
        self.read_data = self.read_data[n:]
        return result

    def _get_n_blocks(self, n):
        byte_count = self.block_length * (self.read_blocks + n)
        xof_data = self.xof.digest(byte_count)
        self.read_blocks += n
        self.read_data = xof_data[-self.block_length * n:]

Shake128 = Shake(shake_128, 168)

def rejection_sample(xof, buffer, bit_buffer, bit_count, log_file, input_vectors):
    while True:
        while bit_count < 12:
            if not buffer:
                log_file.write("squeezing\n")
                new_bytes = xof.read(168)
                buffer.extend(new_bytes)
                input_vectors.write(f"{int.from_bytes(new_bytes, 'little'):0336x}")
            bit_buffer |= buffer.pop(0) << bit_count
            bit_count += 8

        j = bit_buffer & 0x0FFF  # Extract 12 bits
        bit_buffer >>= 12
        bit_count -= 12

        if j < MLKEM_Q:
            log_file.write(f"ack: {j:03x}\n")
            return j, bit_buffer, bit_count
        log_file.write(f"rej: {j:03x}\n")

def rejection_q(seed, log_file, input_vectors):
    Shake128.absorb(seed)
    buffer = bytearray()
    bit_buffer = 0
    bit_count = 0
    coeffs = []
    for _ in range(MLKEM_N):
        coeff, bit_buffer, bit_count = rejection_sample(Shake128, buffer, bit_buffer, bit_count, log_file, input_vectors)
        coeffs.append(coeff)
    input_vectors.write("\n")
    log_file.write("\n")
    return coeffs

def main():
    with open("input_seeds.txt", "r") as seed_file, \
         open("input_vectors.txt", "w") as input_vectors, \
         open("exp_results.txt", "w") as exp_results, \
         open("rej_sampler.log", "w") as log_file:

        for line in seed_file:
            seed = bytes(line.strip(), 'utf-8')
            coeffs = rejection_q(seed, log_file, input_vectors)
            exp_results.write(" ".join(f"{c:03x}" for c in coeffs) + "\n")

if __name__ == "__main__":
    main()