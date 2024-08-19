import numpy as np

DILITHIUM_Q = 8380417 # 2**23 - 2**13 + 1
DILITHIUM_N = 256
DILITHIUM_D = 13


class Poly:
    def __init__(self, coeffs):
        self.coeffs = coeffs

def generate_random_poly():
    coeffs = np.random.randint(0, DILITHIUM_Q, DILITHIUM_N, dtype=np.uint32)
    return Poly(coeffs)

def poly_power2round(poly):
    r1_coeffs = []
    r0_coeffs = []
    for coeff_i in poly:
        r1, r0 = power2round(coeff_i)
        r1_coeffs.append(r1)
        r0_coeffs.append(r0)    
    return r1_coeffs, r0_coeffs

def power2round(coeff):
    power_2 = (1 << DILITHIUM_D-1)
    r  = coeff % DILITHIUM_Q
    r1 = (r + (power_2 - 1)) >> DILITHIUM_D
    r0 = r - (r1 << DILITHIUM_D)
    return r1, r0

def write_hex_file(filename, data):
    with open(filename, 'w') as f:
        for value in data:
            f.write(f"{value:X}\n")

def main():
    # Generate random inputs
    poly_i = generate_random_poly()

    # Run the pack function
    r1, r0 = poly_power2round(poly_i)

    write_hex_file("input_poly.hex", poly_i.coeffs)

    write_hex_file("output_r1.hex", r1)
    write_hex_file("output_r0.hex", r0)

if __name__ == "__main__":
    main()