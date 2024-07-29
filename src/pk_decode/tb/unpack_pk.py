import random

# Constants
COEFF_BIT_WIDTH = 10
SHIFT_LEFT_BITS = 13
NUM_COEFFS = 256  # Adjust based on the number of coefficients needed
K= 8
SEED = 12345  # Fixed seed for reproducibility

def generate_random_coefficients(num_coeffs):
    """Generate a list of random 10-bit coefficients."""
    random.seed(SEED)  # Set the seed for reproducibility
    coefficients = []
    for _ in range(num_coeffs):
        coef = random.randint(0, (1 << COEFF_BIT_WIDTH) - 1)
        coefficients.append(coef)
    return coefficients

def process_coefficients(coefficients):
    """Shift the coefficients left and mask to 24 bits."""
    processed = []
    for coef in coefficients:
        # Shift left by 13 bits and mask to ensure 24-bit result with MSB zero
        processed_value = (coef << SHIFT_LEFT_BITS) & 0xFFFFFF
        processed.append(processed_value)
    return processed

def write_to_hex_file(data, filename, width):
    """Write the data to a hex file with specified width."""
    with open(filename, 'w') as f:
        for value in data:
            f.write(f"{value:0{width}X}\n")  # width controls hex digits

# Generate random coefficients
coefficients = generate_random_coefficients(NUM_COEFFS*K)

# Process coefficients for expected output
processed_coefficients = process_coefficients(coefficients)

# Write the coefficients and processed outputs to the respective files
write_to_hex_file(coefficients, 'input_pk.hex', 3)  # 10-bit coefficients
write_to_hex_file(processed_coefficients, 'output_decoded_pk.hex', 6)  # 24-bit processed values
