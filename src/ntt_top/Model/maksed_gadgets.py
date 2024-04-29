
from masking_params import *
from custom_data_types import *

def one_share_mult(a0, a1, b):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)    
    #get a random number ranging [0, MultMod-1]
    randomness.generate_random()
    r1 = int(randomness.value)
    #refresh the shares
    a00 = int(a0+r1) % MultMod
    a10 = int(a1-r1) % MultMod
    c0 = int(a00*b) % MultMod
    c1 = int(a10*b) % MultMod
    return c0, c1

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

def unMaskedModAddition(x0, x1, y0, y1):
    x = x0 ^ x1
    y = y0 ^ y1
    z = (x+y) % DILITHIUM_Q
    randomness = CustomUnsignedInteger(0, 0, (2**23)-1)
    # Refresh the shares
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
    d0_22, d1_22 = unMaskedModAddition(d0, d1, z0_12, z1_12)
    
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
    e0_22, e1_22 = unMaskedModAddition(f0, f1, z0_45, z1_45)

    ab0, ab1 = unMaskedModSub(d0_22, d1_22, e0_22, e1_22)

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


