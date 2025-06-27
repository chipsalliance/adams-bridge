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

# Constants
MLDSA_Q = 8380417
MLDSA_N = 256

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

def rejection_sample(xof, buffer, log_file, input_vectors):
    while True:
        if not buffer:
            log_file.write("squeezing\n")
            new_bytes = xof.read(168)
            buffer.extend(new_bytes)
            input_vectors.write(f"{int.from_bytes(new_bytes, 'little'):0336x}")
        j = int.from_bytes(buffer[:3], "little") & 0x7FFFFF
        del buffer[:3]
        if j < MLDSA_Q:
            log_file.write(f"ack: {j:06x}\n")
            return j
        log_file.write(f"rej: {j:06x}\n")

def rejection_q(seed, log_file, input_vectors):
    Shake128.absorb(seed)
    buffer = bytearray()
    coeffs = [rejection_sample(Shake128, buffer, log_file, input_vectors) for _ in range(MLDSA_N)]
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
            exp_results.write(" ".join(f"{c:06x}" for c in coeffs) + "\n")

if __name__ == "__main__":
    main()
