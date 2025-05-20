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

# NTT Reference Implementation

import numpy as np
import copy
import random

### Dilithium Parameter
DILITHIUM_Q = 8380417 # 2**23 - 2**13 + 1
DILITHIUM_N = 256
DILITHIUM_LOGN = 8
DILITHIUM_ROOT_OF_UNITY = 1753

### Kyber Parameters
KYBER_Q = 3329
KYBER_N = 128
KYBER_LOGN = 6 #take care of last layer separately
KYBER_ROOT_OF_UNITY = 17

### Butterfly
def ct_bf(u, v, z):
    global KYBER_Q
    t = (v * z) % KYBER_Q
    v = (u - t) % KYBER_Q
    u = (u + t) % KYBER_Q
    return u, v

def gs_bf(u, v, z):
    global KYBER_Q
    t = (u - v) % KYBER_Q
    u = (u + v) % KYBER_Q
    v = (t * z) % KYBER_Q
    return u, v

def gs_bf_div2(u, v, z):
    global KYBER_Q
    t = div2((u - v) % KYBER_Q)
    u = div2((u + v) % KYBER_Q)
    v = (t * z) % KYBER_Q
    return u, v

def div2(x):
    global KYBER_Q
    if x & 1:
        return (x >> 1) + ((KYBER_Q + 1) // 2)
    else:
        return x >> 1

### Twiddle factor
def bit_reversal(x):  
    binary_string = format(x, '07b')    
    reversed_binary_string = binary_string[::-1]    
    reversed_decimal = int(reversed_binary_string, 2)
    return reversed_decimal

def zeta_generator():
    global KYBER_Q
    global KYBER_N
    global KYBER_ROOT_OF_UNITY

    tree = np.zeros(KYBER_N+128) #last 128 are used for PaWM
    for i in range(KYBER_N+128):
        tree[i] = bit_reversal(i)
        # print("i: ", i, "tree val = ", tree[i])

    tmp = {}
    tmp[0] = 1

    zetas = {}
    zetas_inv = {}

    for i in range(1, KYBER_N+128, 1):
        # print("tmp i = ", i)
        tmp[i] = (tmp[i-1] * KYBER_ROOT_OF_UNITY) % KYBER_Q
        # print("tmp val at index ", i, " = ", tmp[i])

    for i in range(0, KYBER_N+128, 1):
        # print("zetas i = ", i)
        zetas[i] = tmp[tree[i]]
        zetas[i] = zetas[i]
        zetas_inv[i] = -zetas[i] % KYBER_Q

    return zetas, zetas_inv

### ref NTTT/INTT model
def fwd_NTT(poly_r):
    global KYBER_Q
    global KYBER_N
    global zetas

    r = copy.deepcopy(poly_r)
    
    k = 0
    m = 128
    while (m >= 2):
        start = 0
        # print("===================",m,"========================")
        # print_table("r_array=", r, rows=64, cols=4)
        while (start < 256):
            k += 1
            zeta = zetas[k]
            # print("start = ", start)
            for j in range(start, start+m):
                # print("Before ntt, r[j], r[j+m], zeta = ", hex(r[j]), hex(r[j+m]), hex(zeta), "at index ", j, j+m)
                r[j], r[j + m] = ct_bf(r[j], r[j + m], zeta)
                # print("m = ", m, "k = ", k, "index = ", j, j+m)
                # print("After ntt, r[j], r[j+m] = ", r[j], r[j+m], "at index ", j, j+m)
            start = start + 2 * m
        m >>= 1

    # print("===================",m,"========================")
    # print_table("r_array=", r, rows=64, cols=4)
    return r

def inv_NTT(poly_r):
    global KYBER_Q
    global KYBER_N
    global zetas_inv

    r = copy.deepcopy(poly_r)
    
    k = KYBER_N
    m = 2 #1
    while (m <= KYBER_N):
        start = 0
        print("===================",m,"========================")
        print_table("r_array=", r, rows=64, cols=4)
        while (start < 256): #KYBER_N):
            k -= 1
            zeta = zetas_inv[k]
            # print("start = ", start)
            for j in range(start, start+m):
                print("Before intt, r[j], r[j+m], zeta = ", hex(r[j]), hex(r[j+m]), hex(zeta))
                r[j], r[j + m] = gs_bf(r[j], r[j + m], zeta)
                # print("m = ", m, "k = ", k, "index = ", j, j+m)
            start = start + 2 * m
        m <<= 1
    
    print("===================",m,"========================")
    print_table("r_array=", r, rows=64, cols=4)

    #f = 8347681  # 256^-1 mod DILITHIUM_Q
    f = 3303 #Modular inverse of 128 % KYBER_Q #128^-1 mod KYBER_Q
    for j in range(256): #(KYBER_N):
        print("r[",j,"] = ",r[j])
        r[j] = f*r[j] % KYBER_Q

    
    return r

### 2x2 NTT/INTT model
def fwd_NTT2x2(poly_r):
    global KYBER_Q
    global KYBER_N
    global KYBER_LOGN
    global zetas

    r = copy.deepcopy(poly_r)

    k2={}
    zeta2={}

    for l in range(KYBER_LOGN, 0, -2):
        m = 1 << (l - 2)
        for i in range(0, KYBER_N, 1 << l):
            k1 = (KYBER_N + i) >> l
            k2[0] = (KYBER_N + i) >> (l - 1)
            k2[1] = k2[0] + 1
            zeta1 = zetas[k1]
            zeta2[0] = zetas[k2[0]]
            zeta2[1] = zetas[k2[1]]

            for j in range(i, i + m):
                u00 = r[j]
                u01 = r[j + m]
                v00 = r[j + 2 * m]
                v01 = r[j + 3 * m]

                u10, u11 = ct_bf(u00, v00, zeta1)
                v10, v11 = ct_bf(u01, v01, zeta1)

                u20, v20 = ct_bf(u10, v10, zeta2[0])
                u21, v21 = ct_bf(u11, v11, zeta2[1])

                r[j] = u20
                r[j + m] = v20
                r[j + 2 * m] = u21
                r[j + 3 * m] = v21

    return r

def inv_NTT2x2(poly_r):
    global KYBER_Q
    global KYBER_N
    global KYBER_LOGN
    global zetas_inv

    r = copy.deepcopy(poly_r)
    
    k1={}
    zeta1={}

    for l in range(0, KYBER_LOGN - (KYBER_LOGN & 1), 2):
        m = 1 << l
        for i in range(0, KYBER_N, 1 << (l + 2)):
            k1[0] = ((KYBER_N - (i >> 1)) >> l) - 1
            k1[1] = k1[0] - 1
            k2 = ((KYBER_N - (i >> 1)) >> (l + 1)) - 1
            zeta1[0] = zetas_inv[k1[0]]
            zeta1[1] = zetas_inv[k1[1]]
            zeta2 = zetas_inv[k2]

            for j in range(i, i + m):
                u00 = r[j]
                v00 = r[j + m]
                u01 = r[j + 2 * m]
                v01 = r[j + 3 * m]

                u10, u11 = gs_bf(u00, v00, zeta1[0])
                v10, v11 = gs_bf(u01, v01, zeta1[1])

                u20, u21 = gs_bf(u10, v10, zeta2)
                v20, v21 = gs_bf(u11, v11, zeta2)

                r[j] = u20
                r[j + m] = v20
                r[j + 2 * m] = u21
                r[j + 3 * m] = v21
            
    # f = 8347681  # 256^-1 mod DILITHIUM_Q
    f = 3303 # 128^-1 mod KYBER_Q
    for j in range(KYBER_N):
        r[j] = f*r[j] % KYBER_Q

    return r


def inv_NTT2x2_div2(poly_r):
    global KYBER_Q
    global KYBER_N
    global KYBER_LOGN
    global zetas_inv

    r = copy.deepcopy(poly_r)
    
    k1={}
    zeta1={}

    for l in range(0, KYBER_LOGN - (KYBER_LOGN & 1), 2):
        m = 1 << l
        for i in range(0, KYBER_N, 1 << (l + 2)):
            k1[0] = ((KYBER_N - (i >> 1)) >> l) - 1
            k1[1] = k1[0] - 1
            k2 = ((KYBER_N - (i >> 1)) >> (l + 1)) - 1
            zeta1[0] = zetas_inv[k1[0]]
            zeta1[1] = zetas_inv[k1[1]]
            zeta2 = zetas_inv[k2]

            for j in range(i, i + m):
                u00 = r[j]
                v00 = r[j + m]
                u01 = r[j + 2 * m]
                v01 = r[j + 3 * m]

                u10, u11 = gs_bf_div2(u00, v00, zeta1[0])
                v10, v11 = gs_bf_div2(u01, v01, zeta1[1])

                u20, u21 = gs_bf_div2(u10, v10, zeta2)
                v20, v21 = gs_bf_div2(u11, v11, zeta2)                

                r[j] = u20
                r[j + m] = v20
                r[j + 2 * m] = u21
                r[j + 3 * m] = v21

    return r


def print_table(label, data, rows, cols):
    print(label)
    values = list(data.values())
    for i in range(0, len(values), cols):
        row_values = values[i:i + cols]
        print(" ".join(f"{value:06X}" for value in row_values))

zetas, zetas_inv = zeta_generator()

# print kyber zeta values for NTT
print("Kyber zeta=")
for i in range (KYBER_N+128):
    print(hex(zetas[i])[2:].upper().zfill(3))
    # print("assign kyber_zeta[",i,"] = 12'h", hex(zetas[i])[2:].upper().zfill(3),";")
    
## print kyber zeta_inv values for INTT
print("Kyber zetas_inv=")
for i in range (KYBER_N+128):
    print(hex(zetas_inv[i])[2:].upper().zfill(3))
    # print("assign kyber_zetainv[",i,"] = 12'h", hex(zetas_inv[i])[2:].upper().zfill(3),";")

# for i in range(256):
#     print(f'assign kyber_ntt_twiddle_mem[{i}] = ', "{",f'kyber_zeta[], kyber_zeta[], kyber_zeta[]',"};")

### Test
test_no = 1
for test_i in range(test_no):
    r_init = {}
    for i in range (256): #(KYBER_N):
        r_init[i] = i % KYBER_Q #random.randrange(KYBER_Q)  #
        print(i, ":", r_init[i])

    #using ref model
    r_in_ntt = fwd_NTT(r_init)
    print("---------------------------------------------------")
    r_from_ntt = inv_NTT(r_in_ntt)
    #check ref model
    if (r_init != r_from_ntt):
        print("Error in ref model")

    # #using 2x2 architecture
    # r_in_ntt2x2 = fwd_NTT2x2(r_init)
    # r_from_ntt2x2 = inv_NTT2x2(r_in_ntt2x2)
    # #check 2x2 architecture
    # if (r_in_ntt != r_in_ntt2x2):
    #     print("Error in ntt2x2 model")
    # if (r_from_ntt2x2 != r_init):
    #     print("Error in inv_ntt2x2 model")

    # #using 2x2 div2 architecture
    # r_from_ntt2x2_div2 = inv_NTT2x2_div2(r_in_ntt2x2)
    # #check 2x2 div2 architecture
    # if (r_from_ntt2x2_div2 != r_init):
    #     print("Error in inv_ntt2x2 div2 model")

    
print_table("r_init=", r_init, rows=16, cols=16)
print_table("r_in_ntt=", r_in_ntt, rows=16, cols=16)
# print_table("r_in_ntt2x2=", r_in_ntt2x2, rows=16, cols=16)
print_table("r_from_ntt=", r_from_ntt, rows=16, cols=16)
# print_table("r_from_ntt2x2=", r_from_ntt2x2, rows=16, cols=16)
# print_table("r_from_ntt2x2_div2=", r_from_ntt2x2_div2, rows=16, cols=16)
