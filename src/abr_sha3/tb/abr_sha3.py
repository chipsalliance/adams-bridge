import hashlib
import sys
import os
import binascii
import re

def sha3_256(m_hex_str):
    #m_hex_str = hex(m)[2:]
    #if len(m_hex_str) & 1 == 1:
    #    m_hex_str="0"+m_hex_str
    m_ascii_str = binascii.unhexlify(m_hex_str)
    m_hashed = hashlib.sha3_256(m_ascii_str).digest()
    return format(int.from_bytes( m_hashed , byteorder='little', signed=False ), 'x')

def sha3_512(m_hex_str):
    #m_hex_str = hex(m)[2:]
    #if len(m_hex_str) & 1 == 1:
    #    m_hex_str="0"+m_hex_str
    m_ascii_str = binascii.unhexlify(m_hex_str)
    m_hashed = hashlib.sha3_512(m_ascii_str).digest()
    return format(int.from_bytes( m_hashed , byteorder='little', signed=False ), 'x')

def shake_128(m_hex_str,byte_num):
    #m_hex_str = hex(m)[2:]
    #if len(m_hex_str) & 1 == 1:
    #    m_hex_str="0"+m_hex_str    
    m_ascii_str = binascii.unhexlify(m_hex_str)
    m_hashed = hashlib.shake_128(m_ascii_str).digest(byte_num)
    return format(int.from_bytes( m_hashed , byteorder='little', signed=False ), 'x')

def shake_256(m_hex_str,byte_num):
    #m_hex_str = hex(m)[2:]
    #if len(m_hex_str) & 1 == 1:
    #    m_hex_str="0"+m_hex_str    
    m_ascii_str = binascii.unhexlify(m_hex_str)
    m_hashed = hashlib.shake_256(m_ascii_str).digest(byte_num)
    return format(int.from_bytes( m_hashed , byteorder='little', signed=False ), 'x')

#open the input vector file for reading
input_vectors = open("input_vectors.txt", "r")
exp_results = open("exp_results.txt", "w")

Lines = input_vectors.readlines()

for line in Lines:
    fields = line.split()
    mode = fields[0]
    strength = fields[1]
    valid_bytes_hex = fields[2]
    vector_raw = fields[3]
    valid_bytes_onehot = int(valid_bytes_hex, 16)
    valid_bytes_onehot = bin(valid_bytes_onehot)[2:]
    valid_bytes = valid_bytes_onehot.count('1')
    slice_start = (len(vector_raw)-(valid_bytes*2))
    vector = vector_raw[slice_start:]
    vector_ba = bytearray.fromhex(vector)
    vector_ba.reverse()
    m = vector_ba.hex()
    if ((mode == "Shake") & (strength == "L256")):
        digest = shake_256(m,1008)
    elif ((mode == "Shake") & (strength == "L128")):
        digest = shake_128(m,1008)
    elif ((mode == "Sha3") & (strength == "L512")):
        digest = sha3_512(m)
    elif ((mode == "Sha3") & (strength == "L256")):
        digest = sha3_256(m)
    exp_results.write(str(mode)+" "+str(strength)+" "+str(digest)+"\n")