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
from MLKEM_mask_params import *
from custom_data_types import *
from masked_gadgets import AND_DOM, maskedFullAdder


def one_share_mult_with_24(a0, a1, b):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r1 = int(randomness.value) #optional
    #refresh the shares
    a00 = int(a0+r1) % MultMod
    a10 = int(a1-r1) % MultMod
    c0 = int(a00*b) % MultMod
    c1 = int(a10*b) % MultMod
    return c0, c1

def one_share_mult_with_37(a0, a1, b):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, (2**37)-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r1 = int(randomness.value) #optional
    #refresh the shares
    a00 = int(a0+r1) % ((2**37))
    a10 = int(a1-r1) % ((2**37))
    c0 = int(a00*b) % ((2**37))
    c1 = int(a10*b) % ((2**37))
    return c0, c1

def two_share_mult_with_24(a0, a1, b0, b1):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r1 = int(randomness.value)
    #multiply the shares
    c0 = int(a0*b0) % MultMod
    d0 = int(a1*b0) % MultMod
    c1 = int(a0*b1) % MultMod
    d1 = int(a1*b1) % MultMod
    #share the randomness
    e0 = int(c1+r1) % MultMod
    e1 = int(d0-r1) % MultMod
    #combine the shares
    final_res0 = int(c0+e0) % MultMod
    final_res1 = int(d1+e1) % MultMod
    return final_res0, final_res1

def A2BConv_wth_param(Arith0, Arith1, bit_length_param, tunn_off_randomness=0):    
    randomness = CustomUnsignedInteger(0, 0, 1)
    # Split an integer into its bits
    splitter = BitSplitter(Arith0, bit_length_param)
    x0Bits = splitter.bits
    splitter = BitSplitter(Arith1, bit_length_param)
    x1Bits = splitter.bits
    X0 = np.zeros(bit_length_param, dtype=np.uint8)
    X1 = np.zeros(bit_length_param, dtype=np.uint8)
    # Initialize the carry bits with zero
    c0 = c1 = 0
    for i in range (bit_length_param-1,-1,-1):
        randomness.generate_random()
        r0 = int(randomness.value)
        randomness.generate_random()
        r1 = int(randomness.value)
        x0=x0Bits[i] ^ r0
        x1=r0
        y0=x1Bits[i] ^ r1
        y1=r1
        c0, c1, X0[i], X1[i] = maskedFullAdder(x0, x1, y0, y1, c0, c1)

    Boolean0 = splitter.bits_to_int(X0)
    Boolean1 = splitter.bits_to_int(X1)

    if tunn_off_randomness:
        Boolean0 = Boolean0 ^ Boolean1
        Boolean1 = 0

    return Boolean0, Boolean1

def B2AConv_wth_param(x0, x1, modulus_param, turn_off_randomness=0):
    randomness = CustomUnsignedInteger(0, 0, modulus_param-1)
    randomness.generate_random()
    r0 = int(randomness.value)
    if turn_off_randomness:
        r0 = 0 # Hard-coded values
    x0 = x0 ^ r0
    x1 = x1 ^ r0
    randomness.generate_random()
    Gamma = int(randomness.value)
    if turn_off_randomness:
        Gamma = 0 # Hard-coded values
    T0 = x0 ^ Gamma
    T1 = int(T0 - Gamma) % modulus_param
    T2 = T1 ^ x0
    Gamma0 = (Gamma ^ x1)
    A0 = x0 ^ Gamma0
    A1 = int(A0 - Gamma0) % modulus_param
    a0 = A1 ^ T2
    a1 = x1    
    return a0, a1

def OR_DOM(x0, x1, y0, y1, turn_off_randomness=0):
    inv_x0 = x0 ^ 1
    inv_y0 = y0 ^ 1
    z0, z1 = AND_DOM(inv_x0, x1, inv_y0, y1)
    if turn_off_randomness:
        x= inv_x0 ^ x1
        y= inv_y0 ^ y1
        z0 = x & y
        z1 = 0
    return z0, z1 ^ 1

def barret_if_cond_mask(rolled_y0, rolled_y1, r0, turn_off_randomness=0, debug=0):
    
    # Perform A2B conversion
    BooleanY0, BooleanY1 = A2BConv_wth_param(rolled_y0, rolled_y1, 14, turn_off_randomness)
    if debug:
        print(f"BooleanY0: {BooleanY0}, BooleanY1: {BooleanY1} and combined: {(BooleanY0^BooleanY1)}")
        print(f"BooleanY0 (binary): {bin(BooleanY0)}, BooleanY1 (binary): {bin(BooleanY1)} and combined (binary): {bin(BooleanY0^BooleanY1)}")
    
    # Extract the 14th and 13th bits of y0 and y1
    y0_13 = (BooleanY0 >> 12) & 0x1
    y0_14 = (BooleanY0 >> 13) & 0x1
    y1_13 = (BooleanY1 >> 12) & 0x1
    y1_14 = (BooleanY1 >> 13) & 0x1
    if debug:
        print(f"y0_13: {y0_13}, y0_14: {y0_14}, y1_13: {y1_13}, y1_14: {y1_14} and combined y13: {(y0_13^y1_13)} and y14: {(y0_14^y1_14)}")
    
    # Perform OR operation to check if y is larger than 2**13
    y_carry0, y_carry1 = OR_DOM(y0_13, y1_13, y0_14, y1_14, turn_off_randomness)
    if debug:
        print(f"y_carry0: {y_carry0}, y_carry1: {y_carry1} and combined: {(y_carry0^y_carry1)}")
    
    # Step 6.7: randomize Q with a 12-bit random number
    Q0 = MLKEM_Q ^ r0
    Q1 = r0
    if debug:
        print(f"Random r0: {r0}, Q0: {Q0}, Q1: {Q1} and combined: {(Q0^Q1)}")
    
    # Step 6.8: OR Q with the y_carries
    Boelan_y0 =  np.zeros(12, dtype=np.uint8)
    Boelan_y1 =  np.zeros(12, dtype=np.uint8)
    for i in range(12):
        Q0_bit = (Q0 >> i) & 1
        Q1_bit = (Q1 >> i) & 1
        Boelan_y0[i], Boelan_y1[i] = AND_DOM(y_carry0, y_carry1, Q0_bit, Q1_bit)
        if turn_off_randomness:
            Boelan_y0[i] = Boelan_y0[i] ^ Boelan_y1[i]
            Boelan_y1[i] = 0

    
    # Convert Boelan_y0 and Boelan_y1 from boolean arrays to integers
    Boolean0 = 0
    Boolean1 = 0
    for i in range(12):  # Iterate from 0 to 11
        Boolean0 = (Boolean0 << 1) | int(Boelan_y0[11-i])
        Boolean1 = (Boolean1 << 1) | int(Boelan_y1[11-i])

    Arith_Q0, Arith_Q1 = B2AConv_wth_param(int(Boolean0), int(Boolean1), 2**14, turn_off_randomness)
    if debug:
        print(f"Q0: {int(Boolean0)}, Q1: {int(Boolean1)} and combined: {int(Boolean0)^int(Boolean1)}")
        print("==============================================")
    Arith_Q0 = Arith_Q0 & 0x1FFF  # Mask to 13 bits
    Arith_Q1 = Arith_Q1 & 0x1FFF  # Mask to 13 bits
    
    return Arith_Q0, Arith_Q1

def masked_barret_with_vuln_shift(x0, x1, r_12_bit, r_24_bit, debug=0, turn_off_randomness = 0):
    # Perform the masked equivalent of the given unmasked C code
    # Step 3: t = t >> K
    carry = ((x0 & 0x1FFFFFF) + (x1 & 0x1FFFFFF)) >> 24
    if debug:
        print(f"x0: {x0}, x1: {x1} and x: {(x0+x1) & ((1 << 24)-1)} and carry : {carry}")
    t0 = (x0 << 12) + (x0 << 9) + (x0 << 8) + (x0 << 7) + (x0 << 5) + (x0 << 3) + (x0 << 2) + (x0 << 1) + x0
    t1 = (x1 << 12) + (x1 << 9) + (x1 << 8) + (x1 << 7) + (x1 << 5) + (x1 << 3) + (x1 << 2) + (x1 << 1) + x1

    carry = carry << 24
    correction0 = (carry << 5) + (carry << 3) + (carry << 2) + (carry << 1) + carry
    correction1 = (carry << 12) + (carry << 9) + (carry << 8) + (carry << 7)
    if debug:
        print(f"correction0: {correction0}, correction1: {correction1} and correction: {(correction0+correction0) & ((1 << 37)-1)}")
    t0 = (t0 - correction0) & 0x1FFFFFFFFF  # Mask to 37 bits
    t1 = (t1 - correction1) & 0x1FFFFFFFFF  # Mask to 37 bits
    # t0, t1 = one_share_mult_with_37(x0, x1, 5039)
    if debug:
        print(f"t0: {t0}, t1: {t1} and t: {(t0+t1) & ((1 << 37)-1)}")
    
    tmp0 = t0 & ((1 << 37) - 1)  # Mask to 37 bits
    tmp1 = t1 & ((1 << 37) - 1)  # Mask to 37 bits
    if debug:
        print(f"tmp0: {tmp0}, tmp1: {tmp1} and tmp: {(tmp0+tmp1) & ((1 << 37)-1)}")
    
    # Step 3: t = t >> K
    carry = ((tmp0 & 0xFFFFFF) + (tmp1 & 0xFFFFFF)) >> 24
    t0 = (tmp0 >> 24) & 0x1FFF  # Mask to 13 bits
    t1 = (tmp1 >> 24) & 0x1FFF  # Mask to 13 bits
    if debug:
        print(f"carry: {carry}, t0: {t0}, t1: {t1}")
    
    # If the sum of the lower 24 bits of tmp0 and tmp1 is greater than 2^24, we need to adjust t0 and t1
    if carry:
        t0 = t0 + 1
        if debug:
            print(f"Adjusted t0: {t0} and t: {(t0+t1) & ((1 << 13)-1)}")
    
    # Step 4 (q.t): t = (t << 11) + (t << 10) + (t << 8) + t
    carry = ((t0+t1)>>13) & 1
    carry = carry * 0x2000
    t0 = (t0 << 11) + (t0 << 10) + (t0 << 8) + t0 - carry - (carry<<10)
    t1 = (t1 << 11) + (t1 << 10) + (t1 << 8) + t1 - (carry<<8) - (carry<<11)
    
    
    # Step 4.5: Mask t to 25 bits
    t0 = t0 & 0x1FFFFFF
    t1 = t1 & 0x1FFFFFF
    if debug:
        print(f"t0 after step 4: {t0}, and carry:{carry}  t: {(t0+t1) & ((1 << 25)-1)}")
    
    # Step 5: c = x - t
    c0 = (x0 - t0) & 0x1FFF  # Mask to 13 bits
    c1 = (x1 - t1) & 0x1FFF  # Mask to 13 bits
    if debug:
        print(f"c0: {c0}, c1: {c1} and c: {(c0+c1) & ((1 << 13)-1)}")
    
    carry = ((c0+c1)>>13) & 1
    carry = carry * 0x2000
    
    c0_rolled = c0 + (Roller-carry)  # (2**9)+(2**8)-1
    c0_rolled = c0_rolled & 0x3FFF  # Mask to 14 bits
    c1_rolled = c1
    if debug:
        print(f"c0_rolled after adding Roller: {c0_rolled}")
        print("==============================================")
    
    # Step 6: Check if c is larger than 2**13
    # Call the new method
    Arith_Q0, Arith_Q1 = barret_if_cond_mask(c0_rolled, c1_rolled, r_12_bit, turn_off_randomness, debug=debug)
    
    # Step 7: t = y - q
    t0 = (c0 - Arith_Q0) & 0x1FFF
    t1 = (c1 - Arith_Q1) & 0x1FFF
    if debug:
        print(f"Arith_Q0: {Arith_Q0}, Arith_Q1: {Arith_Q1} and Q: {(Arith_Q0+Arith_Q1) & ((1 << 13)-1)}")
        print(f"Final t0: {t0}, Final t1: {t1} and t: {(t0+t1) & ((1 << 13)-1)}")

    t0 = t0 & 0xFFF  # Just get the 12-bit since q is 12-bit
    t1 = t1 & 0xFFF  # Just get the 12-bit since q is 12-bit
    carry = (t0 + t1) >> 12
    carry = carry << 12

    t0 = (t0 - r_24_bit - carry) & 0xFFFFFF  # Mask to 24 bits
    t1 = (t1 + r_24_bit) & 0xFFFFFF  # Mask to 24 bits

    
    return t0, t1




# ECC_PK = 96
# ECC_SIG = 96

# MLDSA_PK = 2592
# MLDSA_SIG = 4628

# print(ECC_PK+ECC_SIG+MLDSA_PK+MLDSA_SIG)

print((1 << 13)-1)
print(0x1FFF)
