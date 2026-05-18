# SPDX-License-Identifier: Apache-2.0
#
# Python model of barrett_reduction.sv
# Fixed for MLDSA prime (8380417)

PRIME = 8380417
REG_SIZE = PRIME.bit_length()   # equivalent to $clog2(PRIME)
K = 2 * REG_SIZE

# Precomputed M = floor(2^K / PRIME)
M = (1 << K) // PRIME


def barrett_reduction(x: int):
    """
    Barrett reduction: compute quotient (inv) and remainder (r)
    such that: x = inv * PRIME + r, with 0 <= r < PRIME
    """
    # Step 1: Multiply by M
    mult_full = x * M

    # Step 2: Estimate quotient
    u_est = mult_full >> K

    # Step 3: Compute estimated remainder
    u_prime = u_est * PRIME
    r_est = x - u_prime

    # Step 4: Check if remainder >= PRIME
    if r_est >= PRIME:
        r = r_est - PRIME
        inv = u_est + 1
    else:
        r = r_est
        inv = u_est

    # Mask results to REG_SIZE bits (for SV alignment)
    r &= (1 << REG_SIZE) - 1
    inv &= (1 << REG_SIZE) - 1

    return inv, r


# ---------------- Example test ----------------
if __name__ == "__main__":
    import random

    # Try 10 random samples
    for _ in range(20_000_000):
        op_a = random.randrange(PRIME)
        op_b = random.randrange(PRIME)
        x = op_a * op_b

        inv, r = barrett_reduction(x)

        # Reference division
        inv_ref = x // PRIME
        r_ref = x % PRIME

        if inv != inv_ref or r != r_ref:
            print(f"FAIL: x={x}, inv={inv} (ref {inv_ref}), r={r} (ref {r_ref})")
        assert inv == inv_ref and r == r_ref

    print("All tests passed")
