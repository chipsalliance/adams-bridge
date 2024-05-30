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

def rejection_q(seed):
    global DILITHIUM_Q
    global DILITHIUM_N
    global buff_arr

    def rejection_sample(xof):
        global buff_arr
        while True:    
            if (len(buff_arr) == 0):
                log_file.write("squeezing\n")
                buff_bytes = xof.read(168)
                buff_arr = bytearray(buff_bytes)
                buff_int = int.from_bytes(buff_bytes, "little")
                input_vectors.write(f"{buff_int:0336x}")
            j_bytes = buff_arr[0:3]
            for i in range (3):
                buff_arr.pop(0)
            j = int.from_bytes(j_bytes, "little")
            j &= 0x7FFFFF
            if j < DILITHIUM_Q:
                log_file.write("ack: " + f"{j:06x}" + "\n")
                return j
            log_file.write("rej: " + f"{j:06x}" + "\n")

    # Initialise the XOF
    Shake128.absorb(seed)
    buff_arr = bytearray()
    coeffs = [rejection_sample(Shake128) for _ in range(DILITHIUM_N)]
    input_vectors.write("\n")
    log_file.write("\n")
    return coeffs

#open the input vector file for reading
input_seeds = open("input_seeds.txt", "r")
input_vectors = open("input_vectors.txt", "w")
exp_results = open("exp_results.txt", "w")
log_file = open("rej_sampler.log", "w")
Lines = input_seeds.readlines()

for line in Lines:
    Coeffs = rejection_q( bytes(line.strip(),'utf-8') )
    for coeff in Coeffs:
        exp_results.write(f"{coeff:06x}"+" ")
    exp_results.write("\n")