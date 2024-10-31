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
from masking_params import *
from custom_data_types import *

def one_share_mult(a0, a1, b):
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

def two_share_mult(a0, a1, b0, b1):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r1 = int(randomness.value)
    # #refresh the shares
    # a00 = int(a0+r1) % MultMod
    # a10 = int(a1-r1) % MultMod
    # c0 = int(a00*b) % MultMod
    # c1 = int(a10*b) % MultMod
    c0 = int(a0*b0) % MultMod
    d0 = int(a1*b0) % MultMod
    c1 = int(a0*b1) % MultMod
    d1 = int(a1*b1) % MultMod
    e0 = int(c1+r1) % MultMod
    e1 = int(d0-r1) % MultMod
    final_res0 = int(c0+e0) % MultMod
    final_res1 = int(d1+e1) % MultMod
    return final_res0, final_res1

def maskedAdder(a0, a1, b0, b1):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r0 = int(randomness.value)
    randomness.generate_random()
    r1 = int(randomness.value)
    #refresh the shares
    a00 = int(a0+r0) % MultMod
    a10 = int(a1-r0) % MultMod
        # Each operand should have a different randomness
    b00 = int(b0+r1) % MultMod
    b10 = int(b1-r1) % MultMod
    # Perform Addition
    c0 = int(a00+b00) % MultMod
    c1 = int(a10+b10) % MultMod
    return c0, c1


def maskedGS_BFU_noReduction(u0, u1, v0, v1, twiddle):
    # Calculate the negative v (-v) = DILITHIUM_Q - v
    v00 = (DILITHIUM_Q-v0) % MultMod
    v10 = (DILITHIUM_Q-v1) % MultMod

    up0, up1 = maskedAdder(u0, u1, v0, v1)
    down0, down1 = maskedAdder(u0, u1, v00, v10)
    down00, down10 = one_share_mult(down0, down1, twiddle)    
    #
    # BE CAREFUL:
    # The result are still in mod(Q) not in mod(q)
    # Assume that we implemented a reduction circuit for it
    # First, we merge and then reduce to q and split again
    # However, the actual implementation will have a circuit
    # to perform a masked reduction routine
    down = int(down00+down10) % MultMod
    down = down % DILITHIUM_Q
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    randomness.generate_random()
    r0 = int(randomness.value)
    down01 = int(down-r0) % MultMod
    down11 = r0
    return up0, up1, down01, down11


def AND_DOM(x0, x1, y0, y1):
    randomness = CustomUnsignedInteger(0, 0, 1)
    randomness.generate_random()
    r1 = int(randomness.value)
    x0y0_clk1 = x0 & y0
    x0y1_clk1 = x0 & y1
    x1y0_clk1 = x1 & y0
    x1y1_clk1 = x1 & y1
    x0y0_clk2 = x0y0_clk1
    x0y1_clk2 = x0y1_clk1 ^ r1
    x1y0_clk2 = x1y0_clk1 ^ r1
    x1y1_clk2 = x1y1_clk1
    x0_clk3 = x0y0_clk2 ^ x0y1_clk2
    x1_clk3 = x1y0_clk2 ^ x1y1_clk2

    return x0_clk3, x1_clk3

def maskedFullAdder(x0, x1, y0, y1, c0, c1):
    randomness = CustomUnsignedInteger(0, 0, 1)
    #==================================
    # Refresh the shares
    randomness.generate_random()
    r1 = int(randomness.value)
    y0 = y0 ^ r1
    y1 = y1 ^ r1
    randomness.generate_random()
    r1 = int(randomness.value)
    x0 = x0 ^ r1
    x1 = x1 ^ r1
    #==================================
    a0 = x0 ^ y0
    a1 = x1 ^ y1
    sumBit0 = c0 ^ a0
    sumBit1 = c1 ^ a1
    and0, and1 = AND_DOM(a0, a1, (x0 ^ c0), (x1 ^ c1))
    carryBit0 = and0 ^ x0
    carryBit1 = and1 ^ x1
    return carryBit0, carryBit1, sumBit0, sumBit1

def A2BConv(Arith0, Arith1):    
    randomness = CustomUnsignedInteger(0, 0, 1)
    # Split an integer into its bits
    splitter = BitSplitter(Arith0, numOfBits)
    x0Bits = splitter.bits
    splitter = BitSplitter(Arith1, numOfBits)
    x1Bits = splitter.bits
    X0 = np.zeros(numOfBits, dtype=np.uint8)
    X1 = np.zeros(numOfBits, dtype=np.uint8)
    # Initialize the carry bits with zero
    c0 = c1 = 0
    for i in range (numOfBits-1,-1,-1):
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

    return Boolean0, Boolean1

    
def maskedN_bitAdder(x0, x1, y0, y1, num_of_bits):
    splitter = BitSplitter(x0, num_of_bits)
    x0Bits = splitter.bits
    splitter = BitSplitter(x1, num_of_bits)
    x1Bits = splitter.bits
    splitter = BitSplitter(y0, num_of_bits)
    y0Bits = splitter.bits
    splitter = BitSplitter(y1, num_of_bits)
    y1Bits = splitter.bits
    c0 = c1 = 0
    # Initialize the array for the result (sum)
    sum_result0 = np.zeros(num_of_bits+1, dtype=np.uint8) 
    sum_result1 = np.zeros(num_of_bits+1, dtype=np.uint8)
    # Perform bit-wise addition using full adder from LSB to MSB
    for i in range(num_of_bits - 1, -1, -1):
        c0, c1, sum_result0[i+1], sum_result1[i+1] = maskedFullAdder(x0Bits[i], x1Bits[i], y0Bits[i], y1Bits[i], c0, c1)

    sum_result0[0] = c0
    sum_result1[0] = c1

    Boolean0 = splitter.bits_to_int(sum_result0)
    Boolean1 = splitter.bits_to_int(sum_result1)

    return Boolean0, Boolean1


def maskedN_bitBooleanAdder(x0, x1, y0, y1, num_of_bits):
    c0 = c1 = 0
    # Initialize the array for the result (sum)
    sum_result0 = np.zeros(num_of_bits+1, dtype=np.uint8) 
    sum_result1 = np.zeros(num_of_bits+1, dtype=np.uint8)
    # Perform bit-wise addition using full adder from LSB to MSB
    for i in range(num_of_bits - 1, -1, -1):
        c0, c1, sum_result0[i+1], sum_result1[i+1] = maskedFullAdder(x0[i], x1[i], y0[i], y1[i], c0, c1)

    sum_result0[0] = c0
    sum_result1[0] = c1

    return sum_result0, sum_result1

def maskedN_bitBooleanAdder_for_normal_ops(x0, x1, y0, y1, num_of_bits, sub):
    if sub:
        c0 = 1
        c1 = 0
        y0 = np.bitwise_not(y0) & 1  # Ensure bits are in {0,1}
        y1 = y1.copy()  # y1 remains the same
    else:
        c0 = c1 = 0
    # Initialize the array for the result (sum)
    sum_result0 = np.zeros(num_of_bits+1, dtype=np.uint8) 
    sum_result1 = np.zeros(num_of_bits+1, dtype=np.uint8)
    # Perform bit-wise addition using full adder from LSB to MSB
    for i in range(num_of_bits - 1, -1, -1):
        c0, c1, sum_result0[i+1], sum_result1[i+1] = maskedFullAdder(x0[i], x1[i], y0[i], y1[i], c0, c1)

    sum_result0[0] = c0
    sum_result1[0] = c1

    return sum_result0, sum_result1

def unMaskedModAddition(x0, x1, y0, y1):
    x = x0 ^ x1
    y = y0 ^ y1
    z = (x+y) % DILITHIUM_Q
    randomness = CustomUnsignedInteger(0, 0, (2**23)-1)
    # Refresh the shares -- not optional
    randomness.generate_random()
    r1 = int(randomness.value)
    z0 = z ^ r1
    z1 = r1
    return z0, z1

def unMaskedModSub(x0, x1, y0, y1):
    x = x0 ^ x1
    y = y0 ^ y1
    z = (x-y) % DILITHIUM_Q
    randomness = CustomUnsignedInteger(0, 0, (2**23)-1)
    # Refresh the shares
    randomness.generate_random()
    r1 = int(randomness.value)
    z0 = z ^ r1
    z1 = r1
    return z0, z1


def masked_modular_add_sub_with_MUX(x0, x1, y0, y1, k=23, sub=0, debug=0):
    if debug == 1:
        print("Starting masked_modular_add_sub_with_MUX")
        print(f"x0: {x0}, x1: {x1}, y0: {y0}, y1: {y1}, k: {k}, sub: {sub}")

    splitter0 = BitSplitter(x0, k)
    x0Bits = splitter0.bits
    splitter1 = BitSplitter(x1, k)
    x1Bits = splitter1.bits

    splitter2 = BitSplitter(y0, k)
    y0Bits = splitter2.bits
    splitter3 = BitSplitter(y1, k)
    y1Bits = splitter3.bits

    splitter4 = BitSplitter(DILITHIUM_Q, k)
    Q0Bits = splitter4.bits
    splitter5 = BitSplitter(0, k)
    Q1Bits = splitter5.bits

    if debug == 1:
        print("\nBit splitting done:")
        print(f"x0Bits: {x0Bits}")
        print(f"x1Bits: {x1Bits}")
        print(f"y0Bits: {y0Bits}")
        print(f"y1Bits: {y1Bits}")
        print(f"Q0Bits: {Q0Bits}")
        print(f"Q1Bits: {Q1Bits}")

    rc0_0, rc0_1 = maskedN_bitBooleanAdder_for_normal_ops(x0Bits, x1Bits, y0Bits, y1Bits, num_of_bits = k, sub=sub)
    r0_0 = get_slice(rc0_0, high=k-1, low=0)
    r0_1 = get_slice(rc0_1, high=k-1, low=0)
    c0_0 = get_slice(rc0_0, high=k, low=k)
    c0_1 = get_slice(rc0_1, high=k, low=k)    

    if debug == 1:
        print("\nAfter first addition/subtraction:")
        print(f"rc0_0: {rc0_0}")
        print(f"rc0_1: {rc0_1}")
        print(f"r0_0: {r0_0}")
        print(f"r0_1: {r0_1}")
        print(f"c0_0: {c0_0}")
        print(f"c0_1: {c0_1}")

    rc1_0, rc1_1 = maskedN_bitBooleanAdder_for_normal_ops(r0_0, r0_1, Q0Bits, Q1Bits, num_of_bits = k, sub=(not sub))
    r1_0 = get_slice(rc1_0, high=k-1, low=0)
    r1_1 = get_slice(rc1_1, high=k-1, low=0)
    c1_0 = get_slice(rc1_0, high=k, low=k)
    c1_1 = get_slice(rc1_1, high=k, low=k) 

    if debug == 1:
        print("\nAfter second addition/subtraction:")
        print(f"rc1_0: {rc1_0}")
        print(f"rc1_1: {rc1_1}")
        print(f"r1_0: {r1_0}")
        print(f"r1_1: {r1_1}")
        print(f"c1_0: {c1_0}")
        print(f"c1_1: {c1_1}")

    if sub:
        s0 = np.pad(c0_0, (k-1, 0), 'constant', constant_values=(c0_0[0], 0))
        s1 = np.pad(c0_1, (k-1, 0), 'constant', constant_values=(c0_1[0], 0))
        if debug == 1:
            print("\nSubtraction selected:")
            print(f"c0_0: {c0_0}")
            print(f"c0_1: {c0_1}")
            print(f"s0: {s0}")
            print(f"s1: {s1}")
    else:
        c0c1_0 = np.bitwise_xor(c0_0, c1_0)
        c0c1_1 = np.bitwise_xor(c0_1, c1_1)
        inv_c0c1_0 = np.bitwise_not(c0c1_0) & 1
        inv_c0c1_1 = c0c1_1.copy()
        s0 = np.pad(inv_c0c1_0, (k-1, 0), 'constant', constant_values=(inv_c0c1_0[0], 0))
        s1 = np.pad(inv_c0c1_1, (k-1, 0), 'constant', constant_values=(inv_c0c1_1[0], 0))
        if debug == 1:
            print("\nAddition selected:")
            print(f"c0c1_0: {c0c1_0}")
            print(f"c0c1_1: {c0c1_1}")
            print(f"inv_c0c1_0: {inv_c0c1_0}")
            print(f"inv_c0c1_1: {inv_c0c1_1}")
            print(f"s0: {s0}")
            print(f"s1: {s1}")

    x0y0 = np.bitwise_xor(r0_0, r1_0)
    x1y1 = np.bitwise_xor(r0_1, r1_1)
    #Stages before the following steps should be registered with FFs
    randomness0 = CustomUnsignedInteger(0, 0, (k**2)-1)
    randomness0.generate_random()
    k_bit_randomness = int(randomness0.value)
    splitter0 = BitSplitter(k_bit_randomness, k)
    k_bit_randomness = splitter0.bits
    x0y0k = np.bitwise_xor(x0y0, k_bit_randomness)
    x1y1k = np.bitwise_xor(x1y1, k_bit_randomness)    
    #Stages before the following steps should be registered with FFs
    if debug == 1:
        print("\nAfter XOR with randomness:")
        print(f"x0y0: {x0y0}")
        print(f"x1y1: {x1y1}")
        print(f"k_bit_randomness: {k_bit_randomness}")
        print(f"x0y0k: {x0y0k}")
        print(f"x1y1k: {x1y1k}")

    xy_and_s0 = np.zeros_like(s0, dtype=np.uint8)
    xy_and_s1 = np.zeros_like(s0, dtype=np.uint8)
    for i in range(k):
        xy_and_s0[i], xy_and_s1[i] = AND_DOM(s0[i], s1[i], x0y0k[i], x1y1k[i])
    
    if debug == 1:
        print("\nAfter AND_DOM:")
        print(f"xy_and_s0: {xy_and_s0}")
        print(f"xy_and_s1: {xy_and_s1}")
        

    k_bit_randomness = int(randomness0.value)
    splitter0 = BitSplitter(k_bit_randomness, k)
    k_bit_randomness = splitter0.bits    
    r1_0k = np.bitwise_xor(r1_0, k_bit_randomness)
    r1_1k = np.bitwise_xor(r1_1, k_bit_randomness)  
    #Stages before the following steps should be registered with FFs
    result0_bits = np.bitwise_xor(xy_and_s0, r1_0k)
    result1_bits = np.bitwise_xor(xy_and_s1, r1_1k)
    result0 = splitter0.bits_to_int(result0_bits)
    result1 = splitter1.bits_to_int(result1_bits)
    # result0 = splitter0.bits_to_int(r1_0)
    # result1 = splitter1.bits_to_int(r1_1)
    
    if debug == 1:
        print("\nFinal result:")
        print(f"result0_bits: {result0_bits}")
        print(f"result1_bits: {result1_bits}")
        print(f"result0: {result0}")
        print(f"result1: {result1}")

    return result0, result1
   
def masked_modular_add_with_conc(d0, d1, z0, z1, k=23, debug=0):
    sub = 0
    if debug == 1:
        print("Starting masked_modular_add_sub_with_MUX")
        print(f"x0: {d0}, x1: {d1}, y0: {z0}, y1: {z1}, k: {k}, sub: {sub}")

    splitter0 = BitSplitter(d0, 11)
    x0Bits = splitter0.bits
    splitter1 = BitSplitter(d1, 11)
    x1Bits = splitter1.bits

    splitter2 = BitSplitter(z0, 13)
    y0Bits = splitter2.bits
    splitter3 = BitSplitter(z1, 13)
    y1Bits = splitter3.bits

    splitter4 = BitSplitter(DILITHIUM_Q, k)
    Q0Bits = splitter4.bits
    splitter5 = BitSplitter(0, k)
    Q1Bits = splitter5.bits

    if debug == 1:
        print("\nBit splitting done:")
        print(f"x0Bits: {x0Bits}")
        print(f"x1Bits: {x1Bits}")
        print(f"y0Bits: {y0Bits}")
        print(f"y1Bits: {y1Bits}")
        print(f"Q0Bits: {Q0Bits}")
        print(f"Q1Bits: {Q1Bits}")

    # rc0_0, rc0_1 = maskedN_bitBooleanAdder_for_normal_ops(x0Bits, x1Bits, y0Bits, y1Bits, num_of_bits = k, sub=sub)
    # r0_0 = get_slice(rc0_0, high=k-1, low=0)
    # r0_1 = get_slice(rc0_1, high=k-1, low=0)
    # c0_0 = get_slice(rc0_0, high=k, low=k)
    # c0_1 = get_slice(rc0_1, high=k, low=k)  
    r0_0 = np.zeros_like(Q0Bits, dtype=np.uint8)
    r0_1 = np.zeros_like(Q0Bits, dtype=np.uint8)
    c0_0 = get_slice(x0Bits, high=10, low=10)
    c0_1 = get_slice(x1Bits, high=10, low=10)

    for i in range(10):
        # Assign values directly since they are likely scalars
        r0_0[i] = x0Bits[i+1]
        r0_1[i] = x1Bits[i+1]

    for i in range(13):
        # Assign values directly since they are likely scalars
        r0_0[i+10] = y0Bits[i]
        r0_1[i+10] = y1Bits[i]


    if debug == 1:
        print("\nAfter first addition/subtraction:")
        # print(f"rc0_0: {rc0_0}")
        # print(f"rc0_1: {rc0_1}")
        print(f"r0_0: {r0_0}")
        print(f"r0_1: {r0_1}")
        print(f"c0_0: {c0_0}")
        print(f"c0_1: {c0_1}")

    rc1_0, rc1_1 = maskedN_bitBooleanAdder_for_normal_ops(r0_0, r0_1, Q0Bits, Q1Bits, num_of_bits = k, sub=(not sub))
    r1_0 = get_slice(rc1_0, high=k-1, low=0)
    r1_1 = get_slice(rc1_1, high=k-1, low=0)
    c1_0 = get_slice(rc1_0, high=k, low=k)
    c1_1 = get_slice(rc1_1, high=k, low=k) 

    if debug == 1:
        print("\nAfter second addition/subtraction:")
        print(f"rc1_0: {rc1_0}")
        print(f"rc1_1: {rc1_1}")
        print(f"r1_0: {r1_0}")
        print(f"r1_1: {r1_1}")
        print(f"c1_0: {c1_0}")
        print(f"c1_1: {c1_1}")

    if sub:
        s0 = np.pad(c0_0, (k-1, 0), 'constant', constant_values=(c0_0[0], 0))
        s1 = np.pad(c0_1, (k-1, 0), 'constant', constant_values=(c0_1[0], 0))
        if debug == 1:
            print("\nSubtraction selected:")
            print(f"c0_0: {c0_0}")
            print(f"c0_1: {c0_1}")
            print(f"s0: {s0}")
            print(f"s1: {s1}")
    else:
        c0c1_0 = np.bitwise_xor(c0_0, c1_0)
        c0c1_1 = np.bitwise_xor(c0_1, c1_1)
        inv_c0c1_0 = np.bitwise_not(c0c1_0) & 1
        inv_c0c1_1 = c0c1_1.copy()
        s0 = np.pad(inv_c0c1_0, (k-1, 0), 'constant', constant_values=(inv_c0c1_0[0], 0))
        s1 = np.pad(inv_c0c1_1, (k-1, 0), 'constant', constant_values=(inv_c0c1_1[0], 0))
        if debug == 1:
            print("\nAddition selected:")
            print(f"c0c1_0: {c0c1_0}")
            print(f"c0c1_1: {c0c1_1}")
            print(f"inv_c0c1_0: {inv_c0c1_0}")
            print(f"inv_c0c1_1: {inv_c0c1_1}")
            print(f"s0: {s0}")
            print(f"s1: {s1}")

    x0y0 = np.bitwise_xor(r0_0, r1_0)
    x1y1 = np.bitwise_xor(r0_1, r1_1)
    #Stages before the following steps should be registered with FFs
    randomness0 = CustomUnsignedInteger(0, 0, (k**2)-1)
    randomness0.generate_random()
    k_bit_randomness = int(randomness0.value)
    splitter0 = BitSplitter(k_bit_randomness, k)
    k_bit_randomness = splitter0.bits
    x0y0k = np.bitwise_xor(x0y0, k_bit_randomness)
    x1y1k = np.bitwise_xor(x1y1, k_bit_randomness)    
    #Stages before the following steps should be registered with FFs
    if debug == 1:
        print("\nAfter XOR with randomness:")
        print(f"x0y0: {x0y0}")
        print(f"x1y1: {x1y1}")
        print(f"k_bit_randomness: {k_bit_randomness}")
        print(f"x0y0k: {x0y0k}")
        print(f"x1y1k: {x1y1k}")

    xy_and_s0 = np.zeros_like(s0, dtype=np.uint8)
    xy_and_s1 = np.zeros_like(s0, dtype=np.uint8)
    for i in range(k):
        xy_and_s0[i], xy_and_s1[i] = AND_DOM(s0[i], s1[i], x0y0k[i], x1y1k[i])
    
    if debug == 1:
        print("\nAfter AND_DOM:")
        print(f"xy_and_s0: {xy_and_s0}")
        print(f"xy_and_s1: {xy_and_s1}")
        

    k_bit_randomness = int(randomness0.value)
    splitter0 = BitSplitter(k_bit_randomness, k)
    k_bit_randomness = splitter0.bits    
    r1_0k = np.bitwise_xor(r1_0, k_bit_randomness)
    r1_1k = np.bitwise_xor(r1_1, k_bit_randomness)  
    #Stages before the following steps should be registered with FFs
    result0_bits = np.bitwise_xor(xy_and_s0, r1_0k)
    result1_bits = np.bitwise_xor(xy_and_s1, r1_1k)
    result0 = splitter0.bits_to_int(result0_bits)
    result1 = splitter1.bits_to_int(result1_bits)
    # result0 = splitter0.bits_to_int(r1_0)
    # result1 = splitter1.bits_to_int(r1_1)
    
    if debug == 1:
        print("\nFinal result:")
        print(f"result0_bits: {result0_bits}")
        print(f"result1_bits: {result1_bits}")
        print(f"result0: {result0}")
        print(f"result1: {result1}")

    return result0, result1


def maskedReduction46(x0, x1):
    splitter0 = BitSplitter(x0, numOfBits)
    x0Bits = splitter0.bits
    splitter1 = BitSplitter(x1, numOfBits)
    x1Bits = splitter1.bits
    z0_45_23 = splitter0.get_slice(high=45, low=23)
    z1_45_23 = splitter1.get_slice(high=45, low=23)
    z0_45_33 = splitter0.get_slice(high=45, low=33)
    z1_45_33 = splitter1.get_slice(high=45, low=33)
    z0_45_43 = splitter0.get_slice(high=45, low=43)
    z1_45_43 = splitter1.get_slice(high=45, low=43)
    z0_12_0 = splitter0.get_slice(high=12, low=0)
    z1_12_0 = splitter1.get_slice(high=12, low=0)
    z0_22_13 = splitter0.get_slice(high=22, low=13)
    z1_22_13 = splitter1.get_slice(high=22, low=13)
    z0_32_23 = splitter0.get_slice(high=32, low=23)
    z1_32_23 = splitter1.get_slice(high=32, low=23)
    z0_42_33 = splitter0.get_slice(high=42, low=33)
    z1_42_33 = splitter1.get_slice(high=42, low=33)

    tmp0, tmp1 = maskedN_bitBooleanAdder(z0_22_13, z1_22_13, z0_32_23, z1_32_23, 10)
    tmp00, tmp10 = maskedN_bitBooleanAdder(splitter0.leftpadding(z0_45_43, 7), 
                                           splitter1.leftpadding(z1_45_43, 7), 
                                           z0_42_33, z1_42_33, 10)
    c0_11_0, c1_11_0 = maskedN_bitBooleanAdder(tmp0, tmp1, tmp00, tmp10, 11)    
    c0_11_10 = get_slice(c0_11_0, high=11, low=10)
    c1_11_10 = get_slice(c1_11_0, high=11, low=10)
    c0_9_0 = get_slice(c0_11_0, high=9, low=0)
    c1_9_0 = get_slice(c1_11_0, high=9, low=0)
    d0_10_0, d1_10_0 = maskedN_bitBooleanAdder(splitter0.leftpadding(c0_11_10, 8), 
                                           splitter1.leftpadding(c1_11_10, 8), 
                                           c0_9_0, c1_9_0, 10)
    d0_23_0 = splitter0.rightpadding(d0_10_0, 13)
    d1_23_0 = splitter1.rightpadding(d1_10_0, 13)

    d0 = splitter0.bits_to_int(d0_23_0)
    d1 = splitter1.bits_to_int(d1_23_0)
    z0_12 = splitter0.bits_to_int(z0_12_0)
    z1_12 = splitter1.bits_to_int(z1_12_0)
    d0_22_debug, d1_22_debug = unMaskedModAddition(d0, d1, z0_12, z1_12)
    int_d0_10_0 = splitter0.bits_to_int(d0_10_0)
    int_d0_10_1 = splitter1.bits_to_int(d1_10_0)
    d0_22, d1_22 = masked_modular_add_with_conc(int_d0_10_0, int_d0_10_1, z0_12, z1_12, k=ModulArithBits, debug =0)
    if ((d0_22_debug ^d1_22_debug)!= (d0_22^d1_22)):
        print(f"Error in add model({d0 ^ d1},{z0_12 ^ z1_12}) exp={(d0_22^d1_22)} and actual={(d0_22_debug ^d1_22_debug)}")
        actual_add0, actual_add1 = masked_modular_add_with_conc(d0_10_0, d1_10_0, z0_12, z1_12, k=ModulArithBits, debug =1)
    # elif (d0 ^d1)>=DILITHIUM_Q:
    #     print(f"d ({d0 ^ d1}) is bigger than q")
    #     print(f"Error in add model({d0 ^ d1},{z0_12 ^ z1_12}) exp={(d0_22^d1_22)} and actual={(d0_22_debug ^d1_22_debug)}")

    
    tmp0, tmp1 = maskedN_bitBooleanAdder(splitter0.leftpadding(c0_11_10, 1), 
                                           splitter1.leftpadding(c1_11_10, 1), 
                                           z0_45_43, z1_45_43, 3)
    f0_13_0, f1_13_0 = maskedN_bitBooleanAdder(splitter0.leftpadding(tmp0, 9), 
                                           splitter1.leftpadding(tmp1, 9), 
                                           z0_45_33, z1_45_33, 13)
    

    
    f0 = splitter0.bits_to_int(f0_13_0)
    f1 = splitter1.bits_to_int(f1_13_0)
    z0_45 = splitter0.bits_to_int(z0_45_23)
    z1_45 = splitter1.bits_to_int(z1_45_23)
    e0_22_debug, e1_22debug = unMaskedModAddition(f0, f1, z0_45, z1_45)
    e0_22, e1_22 = masked_modular_add_sub_with_MUX(f0, f1, z0_45, z1_45, k=ModulArithBits, sub=0, debug =0)
    if (e0_22_debug ^e1_22debug)!= (e0_22^e1_22) and ((f0 ^ f1)<DILITHIUM_Q or (z0_45 ^ z1_45)<DILITHIUM_Q):
        print(f"Error in add model({f0 ^ f1},{z0_45 ^ z1_45}) exp={(e0_22_debug^e1_22debug)} and actual={(e0_22 ^e1_22)}")
        actual_add0, actual_add1 = masked_modular_add_sub_with_MUX(f0, f1, z0_45, z1_45, k=ModulArithBits, sub=0, debug =1)
    elif (f0 ^ f1)>=DILITHIUM_Q:
        print(f"f ({f0 ^ f1}) is bigger than q")
    elif (z0_45 ^ z1_45)>=DILITHIUM_Q:
        print(f"z ({(z0_45 ^ z1_45)}) is bigger than q")
    # ab0, ab1 = unMaskedModSub(d0_22, d1_22, e0_22, e1_22)
    ab0, ab1 = masked_modular_add_sub_with_MUX(d0_22, d1_22, e0_22, e1_22, k=ModulArithBits, sub=1, debug =0)

    return ab0, ab1




def B2A(x0, x1):
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    randomness.generate_random()
    r0 = int(randomness.value)
    x0 = x0 ^ r0
    x1 = x1 ^ r0
    randomness.generate_random()
    Gamma = int(randomness.value)    
    T0 = x0 ^ Gamma
    T1 = int(T0 - Gamma) % MultMod
    T2 = T1 ^ x0
    Gamma0 = (Gamma ^ x1)
    A0 = x0 ^ Gamma0
    A1 = int(A0 - Gamma0) % MultMod
    a0 = A1 ^ T2
    a1 = x1    
    return a0, a1


def maskedAdderReduction(u0, u1):
    uRolled0 = (u0 + Roller) % MultMod
    uRolled1 = u1
    # We need its only int(1+numOfBits/2)-bit so the adder size
    # can be reduced from 46 to 24
    uBoolean0, uBoolean1 = A2BConv(uRolled0, uRolled1)
    c0 = (uBoolean0 >> int(numOfBits/2)) & 1
    c1 = (uBoolean1 >> int(numOfBits/2)) & 1
    red0, red1 = B2A(c0, c1)
    q0 = red0 * ((0-DILITHIUM_Q)% MultMod)
    q1 = red1 * ((0-DILITHIUM_Q)% MultMod)
    uReduced0 = (u0+q0) % MultMod
    uReduced1 = (u1+q1) % MultMod
    return uReduced0, uReduced1

def maskedBFUAdder(x0, x1, y0, y1):
    u0, u1 = maskedAdder(x0, x1, y0, y1)
    uReduced0, uReduced1 = maskedAdderReduction(u0, u1)
    return uReduced0, uReduced1


def maskedBFUSub(x0, x1, y0, y1):
    y_new0 = (DILITHIUM_Q-y0) % MultMod
    y_new1 = (0-y1) % MultMod
    v0, v1 = maskedAdder(x0, x1, y_new0, y_new1)
    vReduced0, vReduced1 = maskedAdderReduction(v0, v1)
    return vReduced0, vReduced1

def maskedBFUMult(x0, x1, omega):
    v0, v1 = one_share_mult(x0, x1, omega)
    vBoolean0, vBoolean1 = A2BConv(v0, v1)
    v23Boolean0, v23Boolean1 = maskedReduction46(vBoolean0, vBoolean1)
    vArith0, vArith1 = B2A(v23Boolean0, v23Boolean1)
    return vArith0, vArith1


def maskedBFU_GS(u0, u1, v0, v1, omega):
    t0, t1 = maskedBFUSub(u0, u1, v0, v1)
    u0, u1 = maskedBFUAdder(u0, u1, v0, v1)
    v0, v1 = maskedBFUMult(t0, t1, omega)
    return u0, u1, v0, v1

def maskedBFU_CT(u0, u1, v0, v1, omega):
    t0, t1 = maskedBFUMult(v0, v1, omega)
    v0, v1 = maskedBFUSub(u0, u1, t0, t1)
    u0, u1 = maskedBFUAdder(u0, u1, t0, t1)
    return u0, u1, v0, v1

def maskedBFU_GS_div2(u0, u1, v0, v1, omega):
    t0, t1 = maskedBFUSub(u0, u1, v0, v1)
    t0, t1 = nonMaksed_div2(t0, t1)
    u0, u1 = maskedBFUAdder(u0, u1, v0, v1)
    u0, u1 = nonMaksed_div2(u0, u1)
    v0, v1 = maskedBFUMult(t0, t1, omega)
    return u0, u1, v0, v1

def nonMaksed_div2(x0, x1):
    x= (x0+x1) % MultMod
    if x & 1:
        x = (x >> 1) + ((DILITHIUM_Q + 1) // 2)
    else:
        x = x >> 1
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    randomness.generate_random()
    r1 = int(randomness.value)
    x0 = int(x-r1) % MultMod
    x1 = r1
    return x0, x1

def masked_inv_NTT2x2_div2(poly_r):
    zetas, zetas_inv = zeta_generator()

    r = copy.deepcopy(poly_r)
    
    k1={}
    zeta1={}

    for l in range(0, DILITHIUM_LOGN - (DILITHIUM_LOGN & 1), 2):
        m = 1 << l
        for i in range(0, DILITHIUM_N, 1 << (l + 2)):
            k1[0] = ((DILITHIUM_N - (i >> 1)) >> l) - 1
            k1[1] = k1[0] - 1
            k2 = ((DILITHIUM_N - (i >> 1)) >> (l + 1)) - 1
            zeta1[0] = zetas_inv[k1[0]]
            zeta1[1] = zetas_inv[k1[1]]
            zeta2 = zetas_inv[k2]

            for j in range(i, i + m):                
                randomness = CustomUnsignedInteger(0, 0, MultMod-1)
                u00 = r[j]
                v00 = r[j + m]
                u01 = r[j + 2 * m]
                v01 = r[j + 3 * m]

                randomness.generate_random()
                r1 = int(randomness.value)
                u00_0 = int(u00-r1) % MultMod
                u00_1 = r1
                randomness.generate_random()
                r1 = int(randomness.value)
                v00_0 = int(v00-r1) % MultMod
                v00_1 = r1

                randomness.generate_random()
                r1 = int(randomness.value)
                u01_0 = int(u01-r1) % MultMod
                u01_1 = r1
                randomness.generate_random()
                r1 = int(randomness.value)
                v01_0 = int(v01-r1) % MultMod
                v01_1 = r1
                u10_0, u10_1, u11_0, u11_1 = maskedBFU_GS_div2(u00_0, u00_1, v00_0, v00_1, zeta1[0])
                v10_0, v10_1, v11_0, v11_1 = maskedBFU_GS_div2(u01_0, u01_1, v01_0, v01_1, zeta1[1])

                u20_0, u20_1, u21_0, u21_1 = maskedBFU_GS_div2(u10_0, u10_1, v10_0, v10_1, zeta2)
                v20_0, v20_1, v21_0, v21_1  = maskedBFU_GS_div2(u11_0, u11_1, v11_0, v11_1, zeta2)                

                r[j] = (u20_0 + u20_1) % MultMod
                r[j + m] = (v20_0 + v20_1) % MultMod
                r[j + 2 * m] = (u21_0 + u21_1) % MultMod
                r[j + 3 * m] = (v21_0 + v21_1) % MultMod

    return r

import copy

def inv_NTT2x2_div2(poly_r):
    zetas, zetas_inv = zeta_generator()

    r = copy.deepcopy(poly_r)
    
    k1={}
    zeta1={}

    for l in range(0, DILITHIUM_LOGN - (DILITHIUM_LOGN & 1), 2):
        m = 1 << l
        for i in range(0, DILITHIUM_N, 1 << (l + 2)):
            k1[0] = ((DILITHIUM_N - (i >> 1)) >> l) - 1
            k1[1] = k1[0] - 1
            k2 = ((DILITHIUM_N - (i >> 1)) >> (l + 1)) - 1
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

def bit_reversal(x):  
    binary_string = format(x, '08b')    
    reversed_binary_string = binary_string[::-1]    
    reversed_decimal = int(reversed_binary_string, 2)
    return reversed_decimal
    
def zeta_generator():
    
    tree=np.zeros(DILITHIUM_N)
    for i in range (DILITHIUM_N):
        tree[i] = bit_reversal(i)

    tmp={}
    tmp[0] = 1

    zetas={}
    zetas_inv={}

    for i in range (1, DILITHIUM_N, 1):
        tmp[i] = (tmp[i-1] * DILITHIUM_ROOT_OF_UNITY)  % DILITHIUM_Q

    for i in range (0, DILITHIUM_N, 1):
        zetas[i] = tmp[tree[i]]
        zetas[i] = zetas[i]
        zetas_inv[i] = -zetas[i] % DILITHIUM_Q

    return zetas, zetas_inv

def gs_bf_div2(u, v, z):
    t = div2((u - v) % DILITHIUM_Q)
    u = div2((u + v) % DILITHIUM_Q)
    v = (t * z) % DILITHIUM_Q
    return u, v

def div2(x):
    if x & 1:
        return (x >> 1) + ((DILITHIUM_Q + 1) // 2)
    else:
        return x >> 1
    
def fwd_NTT(poly_r):

    r = copy.deepcopy(poly_r)    
    zetas, zetas_inv = zeta_generator()
    
    k = 0
    m = 128
    while (m > 0):
        start = 0
        while (start < DILITHIUM_N):
            k += 1
            zeta = zetas[k]
            for j in range(start, start+m):
                r[j], r[j + m] = ct_bf(r[j], r[j + m], zeta)
            start = start + 2 * m
        m >>= 1

    return r

def ct_bf(u, v, z):
    t = (v * z) % DILITHIUM_Q
    v = (u - t) % DILITHIUM_Q
    u = (u + t) % DILITHIUM_Q
    return u, v

def modular_add_with_MUX(a, b, debug =0):
    rc0 = (a+b) 
    r0 = rc0 & ((2**ModulArithBits)-1)
    c0 = rc0 >> ModulArithBits
    rc1 = (r0 - DILITHIUM_Q)
    r1 = rc1 & ((2**ModulArithBits)-1)
    c1 = rc1 >> ModulArithBits
    c0c1 = (c1 ^ c0) &1
    if debug:
        print(f"r0={r0}, r1={r1} and c0={c0}, c1={c1} and c0^c1= {c0c1}")
    if c0c1 == 1:
        return r0
    else:
        return r1
    
def modular_sub_with_MUX(a, b, debug =0):
    rc0 = int(a-b)
    r0 = rc0 & ((2**ModulArithBits)-1)
    c0 = rc0 >> ModulArithBits
    rc1 = r0 + DILITHIUM_Q
    r1 = rc1 & ((2**ModulArithBits)-1)
    if debug:
        print(f"r0={r0}, r1={r1} and c0={c0}")
    c0 = c0 &1
    if c0 == 1:
        return r1
    else:
        return r0

