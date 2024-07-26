import numpy as np

# Constants
N = 256  # Assuming N is 256; adjust as necessary
L = 7
GAMMA1 = (1 << 19)
MASK_20BIT = (1 << 20) - 1
Q = 8380417

class Poly:
    def __init__(self, coeffs):
        self.coeffs = coeffs

def polyz_pack(a):
    t = np.zeros(2, dtype=np.uint32)
    r = np.zeros(N*L, dtype=np.uint32)
    for i in range((N*L) // 2):
        if GAMMA1 >= a.coeffs[2*i+0]:
            t[0] = (GAMMA1 - a.coeffs[2*i+0])
        else:
            t[0] = ((GAMMA1+Q) - a.coeffs[2*i+0])
        
        if GAMMA1 >= a.coeffs[2*i+1]:
            t[1] = (GAMMA1 - a.coeffs[2*i+1])
        else:
            t[1] = ((GAMMA1+Q) - a.coeffs[2*i+1])

        r[2*i+0] = t[0]
        r[2*i+1] = t[1]
    
    return r

def generate_random_inputs():
    coeffs = np.random.randint(0, GAMMA1, N*L, dtype=np.uint32)
    return Poly(coeffs)

def write_hex_file(filename, data):
    with open(filename, 'w') as f:
        for value in data:
            f.write(f"{value:X}\n")

def main():
    # Generate random inputs
    poly_a = generate_random_inputs()

    # Run the pack function
    r = polyz_pack(poly_a)

    # Write input coefficients to input_z.hex
    write_hex_file("input_z.hex", poly_a.coeffs)

    # Write output encoded coefficients to output_encoded_z.hex
    write_hex_file("output_decoded_z.hex", r)

if __name__ == "__main__":
    main()
