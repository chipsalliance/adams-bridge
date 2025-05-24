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

import unittest
from MLKEM_mask_params import *
from MLKEM_masked_gadgets import masked_barret_with_vuln_shift
import random
from custom_data_types import *

class TestMaskedBarrettReduction(unittest.TestCase):
    def setUp(self):
        # Define constants used in the tests
        self.MLKEM_Q = MLKEM_Q  # Example modulus value

    def test_masked_barret_with_vuln_shift_small_values(self):
        # Test case 1: x0 and x1 in range [0, 10]
        for x in range(11):
            cm = x*5039
            t = cm>>24
            c = x-t*MLKEM_Q
            if c >= MLKEM_Q:
                c -= MLKEM_Q
            randomness = CustomUnsignedInteger(0, 0, (2**37)-1)
            randomness.generate_random()
            r1 = int(randomness.value) #optional
            x0 = int(x-r1) % (2**37)
            x1 = int(r1) % (2**37)
            print(f"merged x is {(x0+x1)%(2**37)}")
            
            randomness = CustomUnsignedInteger(0, 0, (2**12)-1)
            randomness.generate_random()
            r_12_bit = int(randomness.value)
            t0, t1 = masked_barret_with_vuln_shift(x0, x1, r_12_bit, turn_off_randomness=0)
            expected_t = (x % self.MLKEM_Q)
            actual_t = ((t0 + t1) & 0x1FFF)
            if actual_t != expected_t:
                print(f"Assertion failed: Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
                print(f"x={x}, cm={cm}, t={t}, c={c}")
                print("Running masked_barret_with_vuln_shift with debug=1")
                t0_debug, t1_debug = masked_barret_with_vuln_shift(x0, x1, r_12_bit, debug=1, turn_off_randomness=0)
                print(f"Debug output: t0_debug={t0_debug}, t1_debug={t1_debug}")
                self.fail(f"Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
            else:
                print(f"Success: t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")

    def test_masked_barret_with_vuln_shift_near_modulus(self):
        # Test case 2: x0 and x1 in range [Q-5, Q+5]
        for x in range(self.MLKEM_Q - 5, self.MLKEM_Q + 6):
            cm = x * 5039
            t = cm >> 24
            c = x - t * self.MLKEM_Q
            if c >= self.MLKEM_Q:
                c -= self.MLKEM_Q
            randomness = CustomUnsignedInteger(0, 0, (2**37)-1)
            randomness.generate_random()
            r1 = int(randomness.value)
            x0 = int(x - r1) % (2**37)
            x1 = int(r1) % (2**37)
            print(f"merged x is {(x0 + x1) % (2**37)}")

            randomness = CustomUnsignedInteger(0, 0, (2**12)-1)
            randomness.generate_random()
            r_12_bit = int(randomness.value)
            t0, t1 = masked_barret_with_vuln_shift(x0, x1, r_12_bit, turn_off_randomness=0)
            expected_t = (x % self.MLKEM_Q)
            actual_t = ((t0 + t1) & 0x1FFF)
            if actual_t != expected_t:
                print(f"Assertion failed: Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
                print(f"x={x}, cm={cm}, t={t}, c={c}")
                print("Running masked_barret_with_vuln_shift with debug=1")
                t0_debug, t1_debug = masked_barret_with_vuln_shift(x0, x1, r_12_bit, debug=1, turn_off_randomness=0)
                print(f"Debug output: t0_debug={t0_debug}, t1_debug={t1_debug}")
                self.fail(f"Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
            else:
                print(f"Success: t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")

    def test_masked_barret_with_vuln_shift_large_values(self):
        # Test case 3: x0 and x1 in range [(Q^2)-10, (Q^2)-1]
        Q_squared = self.MLKEM_Q ** 2
        for x in range(Q_squared - 10, Q_squared):
            cm = x * 5039
            t = cm >> 24
            c = x - t * self.MLKEM_Q
            if c >= self.MLKEM_Q:
                c -= self.MLKEM_Q
            randomness = CustomUnsignedInteger(0, 0, (2**37)-1)
            randomness.generate_random()
            r1 = int(randomness.value)
            x0 = int(x - r1) % (2**37)
            x1 = int(r1) % (2**37)
            print(f"merged x is {(x0 + x1) % (2**37)}")

            randomness = CustomUnsignedInteger(0, 0, (2**12)-1)
            randomness.generate_random()
            r_12_bit = int(randomness.value)
            t0, t1 = masked_barret_with_vuln_shift(x0, x1, r_12_bit, turn_off_randomness=0)
            expected_t = (x % self.MLKEM_Q)
            actual_t = ((t0 + t1) & 0x1FFF)
            if actual_t != expected_t:
                print(f"Assertion failed: Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
                print(f"x={x}, cm={cm}, t={t}, c={c}")
                print("Running masked_barret_with_vuln_shift with debug=1")
                t0_debug, t1_debug = masked_barret_with_vuln_shift(x0, x1, r_12_bit, debug=1, turn_off_randomness=0)
                print(f"Debug output: t0_debug={t0_debug}, t1_debug={t1_debug}")
                self.fail(f"Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
            else:
                print(f"Success: t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")

    def test_masked_barret_with_vuln_shift_random_values(self):
        # Test case 4: Random values
        Q_squared = self.MLKEM_Q ** 2
        for _ in range(50000):  # Run 500 random tests
            x = random.randint(0, Q_squared - 1)
            cm = x * 5039
            t = cm >> 24
            c = x - t * self.MLKEM_Q
            if c >= self.MLKEM_Q:
                c -= self.MLKEM_Q
            randomness = CustomUnsignedInteger(0, 0, (2**37)-1)
            randomness.generate_random()
            r1 = int(randomness.value)
            x0 = int(x - r1) % (2**37)
            x1 = int(r1) % (2**37)
            # print(f"merged x is {(x0 + x1) % (2**37)}")

            randomness = CustomUnsignedInteger(0, 0, (2**12)-1)
            randomness.generate_random()
            r_12_bit = int(randomness.value)
            t0, t1 = masked_barret_with_vuln_shift(x0, x1, r_12_bit, turn_off_randomness=0)
            expected_t = (x % self.MLKEM_Q)
            actual_t = ((t0 + t1) & 0x1FFF)
            if actual_t != expected_t:
                print(f"Assertion failed: Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
                print(f"x={x}, cm={cm}, t={t}, c={c}")
                print("Running masked_barret_with_vuln_shift with debug=1")
                t0_debug, t1_debug = masked_barret_with_vuln_shift(x0, x1, r_12_bit, debug=1, turn_off_randomness=0)
                print(f"Debug output: t0_debug={t0_debug}, t1_debug={t1_debug}")
                self.fail(f"Failed for t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")
            # else:
            #     print(f"Success: t0={t0}, t1={t1}, expected_t={expected_t}, actual_t0={actual_t}")

if __name__ == "__main__":
    unittest.main()