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
from maksed_gadgets import *


def test_one_share_mult(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)   
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        a = int(operands.value)
        operands.generate_random()
        b = int(operands.value)
        expected = a*b
        randomness.generate_random()
        r1 = int(randomness.value)
        a0 = int(a-r1) % MultMod
        a1 = r1
        c0,c1 = one_share_mult(a0, a1, b)
        gotten = int(c0+c1) % MultMod
        if gotten != expected:
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {expected}")


# test_one_share_mult(numTest=10000)


def test_maskedAdder(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)   
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        a = int(operands.value)
        operands.generate_random()
        b = int(operands.value)
        expected = a+b
        randomness.generate_random()
        r0 = int(randomness.value)
        a0 = int(a-r0) % MultMod
        a1 = r0
        randomness.generate_random()
        r1 = int(randomness.value)
        b0 = int(b-r1) % MultMod
        b1 = r1
        c0,c1 = maskedAdder(a0, a1, b0, b1)
        gotten = int(c0+c1) % MultMod
        if gotten != expected:
            print(f"Adder gives an Error; gotten = {gotten}, while exp = {expected}")

# test_maskedAdder(numTest=100000)


def test_maskedSubtractor(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)   
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        a = int(operands.value)
        operands.generate_random()
        b = (int(operands.value))
        #
        # BE CAREFUL:
        # The result are still in mod(Q) not in mod(q)
        #
        expected = (a-b) % DILITHIUM_Q
        randomness.generate_random()
        r0 = int(randomness.value)
        a0 = int(a-r0) % MultMod
        a1 = r0
        
        b_new = (DILITHIUM_Q-b) % MultMod
        randomness.generate_random()
        r1 = int(randomness.value)
        b0 = int(b_new-r1) % MultMod
        b1 = r1
        c0,c1 = maskedAdder(a0, a1, b0, b1)
        gotten = int(c0+c1) % MultMod
        gotten = gotten % DILITHIUM_Q
        if gotten != expected:
            print(f"Subtractor gives an Error; gotten = {gotten}, while exp = {expected}")

# test_maskedSubtractor(numTest=1000)


def test_maskedGS_BFU_noReduction(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)  
    twiddles = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1) 
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        u = int(operands.value)
        operands.generate_random()
        v = (int(operands.value))
        twiddles.generate_random()
        omega = int(twiddles.value)
        #
        # BE CAREFUL:
        # The result are still in mod(Q) not in mod(q)
        #
        t = (u - v) % DILITHIUM_Q
        u_exp = (u + v) % DILITHIUM_Q
        v_exp = (t * omega) % DILITHIUM_Q

        randomness.generate_random()
        r0 = int(randomness.value)
        u0 = int(u-r0) % MultMod
        u1 = r0
        
        randomness.generate_random()
        r1 = int(randomness.value)
        v0 = int(v-r1) % MultMod
        v1 = r1

        u00, u10, v00, v10 = maskedGS_BFU_noReduction(u0, u1, v0, v1, omega)
        u_gotten = int(u00+u10) % MultMod
        # This one is for upper bridge
        if u_gotten>= DILITHIUM_Q:
            u_gotten = u_gotten-DILITHIUM_Q
        v_gotten = int(v00+v10) % MultMod
        if u_gotten != u_exp:
            print(f"Upper branch of gives an Error; gotten = {u_gotten}, while exp = {u_exp}")
        if v_gotten != v_exp:
            print(f"Upper branch of gives an Error; gotten = {v_gotten}, while exp = {v_exp}")

# test_maskedGS_BFU_noReduction(numTest=1000000)


def test_maskedFullAdder(numTest = 10):
    # Construct randomness class
    operands = CustomUnsignedInteger(0, 0, 1)
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        x = int(operands.value)
        operands.generate_random()
        y = int(operands.value)
        operands.generate_random()
        c = int(operands.value)
        operands.generate_random()
        r0 = int(operands.value)
        operands.generate_random()
        r1 = int(operands.value)
        operands.generate_random()
        r2 = int(operands.value)
        x0 = x ^ r0
        y0 = y ^ r1
        c0 = c ^ r2
        x1 = r0
        y1 = r1
        c1 = r2

        c0,c1, s0,s1 = maskedFullAdder(x0, x1, y0, y1, c0, c1)
        carry = (c0 ^ c1) << 1
        sum = (s0 ^ s1)
        gotten = carry + sum
        if gotten != (x+y+c):
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {(x+y+c)}")

# test_maskedFullAdder(numTest=1000000)



def test_A2BConv(numTest = 10):
    # Construct randomness class
    operands = CustomUnsignedInteger(0, 0, MultMod-1)
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        a = int(operands.value)
        operands.generate_random()
        r0 = int(operands.value)
        a0 = (a-r0) % MultMod
        a1 = r0 
        c0,c1 = A2BConv(a0, a1)
        gotten = c0 ^ c1
        if gotten != a:
            print(f"A2B gives an Error; gotten = {gotten}, while exp = {a}")

# test_A2BConv(numTest=1000)

def test_maskedN_bitAdder(numTest = 10):
    # Construct randomness class
    operands = CustomUnsignedInteger(0, 0, MultMod-1)
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        x = int(operands.value)
        operands.generate_random()
        y = int(operands.value)
        operands.generate_random()
        r0 = int(operands.value)
        operands.generate_random()
        r1 = int(operands.value)
        x0 = x ^ r0
        y0 = y ^ r1
        x1 = r0
        y1 = r1

        s0,s1 = maskedN_bitAdder(x0, x1, y0, y1, numOfBits)
        gotten = (s0 ^ s1)
        if gotten != (x+y):
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {(x+y)}")

# test_maskedN_bitAdder(numTest=100000)





# test_ModularReductionMult(numTest = 1000000)

def test_maskedReduction46(numTest = 10):
    # Construct randomness class
    operands = CustomUnsignedInteger(0, 0, (2**23)-1)
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        x = int(operands.value)
        # x = 2638949
        operands.generate_random()
        y = int(operands.value)
        # y = 3599593
        excepted = int(x*y) % DILITHIUM_Q
        z = x*y
        randomness.generate_random()
        r0 = int(randomness.value)
        z0 = z ^ r0
        z1 = r0
        ab0, ab1 = maskedReduction46(z0, z1)
        gotten = ab0 ^ ab1
        if gotten != excepted:
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {excepted}")


# test_maskedReduction46(numTest = 1000000)


def test_B2A(numTest = 10):
    # Construct randomness class
    operands = CustomUnsignedInteger(0, 0, BooleanMod-1)
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        x = int(operands.value)
        operands.generate_random()
        r = int(operands.value)
        x0 = x ^ r
        x1 = r
        excepted = x
        a0, a1 = B2A(x0, x1)
        gotten = int(a0 + a1) % MultMod
        if gotten != excepted:
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {excepted}")

# test_B2A(numTest = 1000000)

def test_maskedBFUAdder(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)   
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        a = int(operands.value)
        operands.generate_random()
        b = int(operands.value)
        expected = (a+b) % DILITHIUM_Q
        randomness.generate_random()
        r0 = int(randomness.value)
        a0 = int(a-r0) % MultMod
        a1 = r0
        randomness.generate_random()
        r1 = int(randomness.value)
        b0 = int(b-r1) % MultMod
        b1 = r1
        a0, a1 = maskedBFUAdder(a0, a1, b0, b1)
        gotten = int(a0 + a1) % MultMod
        if gotten != expected:
            print(f"Multiplication gives an Error; gotten = {gotten}, while exp = {expected}")

# test_maskedBFUAdder(numTest = 1000)

def gs_bf(u, v, z):
    t = (u - v) % DILITHIUM_Q
    u = (u + v) % DILITHIUM_Q
    v = (t * z) % DILITHIUM_Q
    return u, v


def ct_bf(u, v, z):
    t = (v * z) % DILITHIUM_Q
    v = (u - t) % DILITHIUM_Q
    u = (u + t) % DILITHIUM_Q
    return u, v


def test_maskedBFU_GS(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1) 
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        u = int(operands.value)
        operands.generate_random()
        v = int(operands.value)
        operands.generate_random()
        omega = int(operands.value)
        exp_u, exp_v = gs_bf(u, v, omega)
        randomness.generate_random()
        r0 = int(randomness.value)
        u0 = int(u-r0) % MultMod
        u1 = r0
        randomness.generate_random()
        r1 = int(randomness.value)
        v0 = int(v-r1) % MultMod
        v1 = r1
        uNew0, uNew1, vNew0, vNew1 = maskedBFU_GS(u0, u1, v0, v1, omega)
        uNew = int(uNew0 + uNew1) % MultMod
        vNew = int(vNew0 + vNew1) % MultMod
        if uNew != exp_u:
            print(f"GS Upper branch gives an Error; gotten = {uNew}, while exp = {exp_u}")
        if vNew != exp_v:
            print(f"GS Lower branch gives an Error; gotten = {vNew}, while exp = {exp_v}")




def test_maskedBFU_CT(numTest = 10):
    # Construct randomness class
    randomness = CustomUnsignedInteger(0, 0, MultMod-1)
    operands = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1) 
    for i in range(0, numTest):         
        #get a random number ranging [0, DILITHIUM_Q-1]
        operands.generate_random()
        u = int(operands.value)
        operands.generate_random()
        v = int(operands.value)
        operands.generate_random()
        omega = int(operands.value)
        exp_u, exp_v = ct_bf(u, v, omega)
        randomness.generate_random()
        r0 = int(randomness.value)
        u0 = int(u-r0) % MultMod
        u1 = r0
        randomness.generate_random()
        r1 = int(randomness.value)
        v0 = int(v-r1) % MultMod
        v1 = r1
        uNew0, uNew1, vNew0, vNew1 = maskedBFU_CT(u0, u1, v0, v1, omega)
        uNew = int(uNew0 + uNew1) % MultMod
        vNew = int(vNew0 + vNew1) % MultMod
        if uNew != exp_u:
            print(f"CT Upper branch gives an Error; gotten = {uNew}, while exp = {exp_u}")
        if vNew != exp_v:
            print(f"CT Lower branch gives an Error; gotten = {vNew}, while exp = {exp_v}")


test_maskedBFU_CT(numTest = 100000)
test_maskedBFU_GS(numTest = 100000)

def test_masked_inv_NTT2x2_div2(numTest = 10):
    for test_i in range(numTest):
        r_init = {}
        for i in range (DILITHIUM_N):
            r_init[i] = random.randrange(DILITHIUM_Q)  #

        #using ref model
        r_in_ntt = fwd_NTT(r_init)

        #using 2x2 div2 architecture
        r_from_ntt2x2_div2 = inv_NTT2x2_div2(r_in_ntt)
        r_from_ntt2x2_div2_masked = masked_inv_NTT2x2_div2(r_in_ntt)
        #check 2x2 div2 architecture
        if (r_from_ntt2x2_div2 != r_init):
            print("Error in inv_ntt2x2 div2 model")
        if (r_from_ntt2x2_div2_masked != r_init):
            print("Error in masked inv_ntt2x2 div2 model")

def test_nonMaskedmodularOps(numTest = 10):
    randomness = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)
    for i in range(numTest):
        randomness.generate_random()
        a = int(randomness.value)
        randomness.generate_random()
        b = int(randomness.value)
        exp_sub = (a-b) % DILITHIUM_Q
        exp_add = (a+b) % DILITHIUM_Q
        actual_sub = modular_sub_with_MUX(a, b)
        actual_add = modular_add_with_MUX(a, b)
        if (exp_sub != actual_sub):
            print(f"Error in sub model({a},{b}) exp={exp_sub} and actual={actual_sub}")
            actual_sub = modular_sub_with_MUX(a, b, 1)
        if (exp_add != actual_add):
            print(f"Error in add model({a},{b}) exp={exp_add} and actual={actual_add}")
            actual_add = modular_add_with_MUX(a, b, 1)

# test_masked_inv_NTT2x2_div2(numTest = 100)
# test_nonMaskedmodularOps(numTest = 100000)

def test_MaskedmodularOps(numTest = 10):
    randomness0 = CustomUnsignedInteger(0, 0, DILITHIUM_Q-1)
    randomness1 = CustomUnsignedInteger(0, 0, BooleanMod-1)
    for i in range(numTest):
        randomness0.generate_random()
        a = int(randomness0.value)
        randomness1.generate_random()
        r0 = int(randomness1.value)
        a1 = r0
        a0 = a ^ r0
        randomness0.generate_random()
        b = int(randomness0.value)
        randomness1.generate_random()
        r0 = int(randomness1.value)
        b1 = r0
        b0 = b ^ r0
        #### TBD #############
        exp_sub = (a-b) % DILITHIUM_Q
        exp_add = (a+b) % DILITHIUM_Q
        actual_sub0, actual_sub1 = masked_modular_add_sub_with_MUX(a0, a1, b0, b1, k=ModulArithBits, sub=1, debug =0)
        actual_add0, actual_add1 = masked_modular_add_sub_with_MUX(a0, a1, b0, b1, k=ModulArithBits, sub=0, debug =0)
        if (exp_sub != (actual_sub0 ^ actual_sub1)):
            print(f"Error in sub model({a},{b}) exp={exp_sub} and actual={(actual_sub0 ^ actual_sub1)}")
            actual_sub0, actual_sub1 = masked_modular_add_sub_with_MUX(a0, a1, b0, b1, k=ModulArithBits, sub=1, debug =1)
        if (exp_add != (actual_add0 ^ actual_add1)):
            print(f"Error in add model({a},{b}) exp={exp_add} and actual={(actual_add0 ^ actual_add1)}")
            actual_add0, actual_add1 = masked_modular_add_sub_with_MUX(a0, a1, b0, b1, k=ModulArithBits, sub=0, debug =1)



# test_MaskedmodularOps(numTest = 100000)
test_maskedReduction46(numTest = 1000000)


