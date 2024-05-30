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

def sample_in_ball(seed):
    global DILITHIUM_Q
    global DILITHIUM_N
    global DILITHIUM_TAU
    global buff_bytes
    global buff_arr

    def rejection_sample(i):
        global buff_bytes
        global buff_arr
        while True:
            if (len(buff_arr) == 0):
                    buff_bytes = Shake256.read(136)
                    buff_arr = bytearray(buff_bytes)
                    buff_int = int.from_bytes(buff_bytes, "little")
                    input_vectors.write(f"{buff_int:0272x}")
            j = buff_arr[0]
            buff_arr.pop(0)
            if j <= i: 
                log_file.write("ack - i: " + f"{i:02x}" + " j: " + f"{j:02x}" + "\n") 
                return j
            log_file.write("rej - i: " + f"{i:02x}" + " j: " + f"{j:02x}" + "\n") 
    
    # Initialise the XOF
    Shake256.absorb(seed)
    
    # Set the first 8 bytes for the sign, and leave the rest for
    # sampling.
    buff_bytes = Shake256.read(136)
    buff_arr = bytearray(buff_bytes)
    buff_int = int.from_bytes(buff_bytes, "little")
    input_vectors.write(f"{buff_int:0272x}")
    sign_bytes = buff_arr[0:8]
    sign_int = int.from_bytes(sign_bytes, "little")
    sign_int_big = int.from_bytes(sign_bytes, "little")
    log_file.write("sign: " + f"{sign_int_big:016x}" + "\n") 
    for i in range (8):
        buff_arr.pop(0)

    # Set the list of coeffs to be 0
    coeffs = [0 for _ in range(DILITHIUM_N)]
    
    # Now set tau values of coeffs to be +/-1
    for i in range(DILITHIUM_N - DILITHIUM_TAU, DILITHIUM_N):
        j = rejection_sample(i)
        coeffs[i] = coeffs[j]
        coeffs[j] = (1 - 2*(sign_int & 1)) % DILITHIUM_Q
        log_file.write("sign: " + f"{(sign_int & 1):x}" + "\n")
        sign_int >>= 1
        
    input_vectors.write("\n")
    return coeffs

#open the input vector file for reading
input_seeds = open("input_seeds.txt", "r")
input_vectors = open("input_vectors.txt", "w")
exp_results = open("exp_results.txt", "w")
log_file = open("sib.log", "w")
Lines = input_seeds.readlines()

for line in Lines:
    Coeffs = sample_in_ball( bytes(line.strip(),'utf-8') )
    for coeff in Coeffs:
        exp_results.write(f"{coeff:06x}"+" ")
    exp_results.write("\n")


