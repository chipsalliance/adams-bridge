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
import random

# Constants
Q = 8380417
VALID_COEFFICIENTS = [Q - 2, Q - 1, 0, 1, 2]
INVALID_COEFFICIENTS = [Q + 1, -1, Q + 2, 123456]  # Example invalid values
K = 8
L = 7
N = 256
TOTAL_COEFFICIENTS = (K + L) * N

def map_coefficient(coef):
    """Map the input coefficient to the corresponding 3-bit value."""
    mapping = {
        Q - 2: 4,
        Q - 1: 3,
        0: 2,
        1: 1,
        2: 0
    }
    return mapping.get(coef, None)

def generate_random_coefficients(num_coeffs, include_invalid=False):
    """Generate a list of random coefficients, including invalid ones if specified."""
    coefficients = []
    for _ in range(num_coeffs):
        if include_invalid and random.random() < 0.2:
            # 20% chance to pick an invalid coefficient
            coefficients.append(random.choice(INVALID_COEFFICIENTS))
        else:
            # 80% chance to pick a valid coefficient
            coefficients.append(random.choice(VALID_COEFFICIENTS))
    return coefficients

def generate_files(input_coefficients, input_file, output_file):
    """Generate files for the input coefficients and their expected outputs."""
    output_lines = []

    # Write input coefficients to input file
    with open(input_file, 'w') as f_input:
        for coef in input_coefficients:
            f_input.write(f"{coef:X}\n")

    # Process coefficients for expected output
    for i in range(0, len(input_coefficients), 32):
        current_line = 0
        for j in range(32):
            if i + j < len(input_coefficients):
                coef = input_coefficients[i + j]
                mapped_value = map_coefficient(coef)
                if mapped_value is not None:
                    # Shift the current line to the right by 3 and add the mapped value to the left
                    current_line = (mapped_value << (j * 3)) | current_line
        
        if current_line is not None:
            # Convert the line to a 96-bit hex string
            final_hex = f"{current_line:024X}"
            # Add the line to output lines
            output_lines.append(final_hex)

    # Write expected output lines to the output file
    with open(output_file, 'w') as f_output:
        for line in output_lines:
            f_output.write(f"{line}\n")

# Generate normal and error test vectors
normal_coefficients = generate_random_coefficients(TOTAL_COEFFICIENTS)
error_coefficients = generate_random_coefficients(TOTAL_COEFFICIENTS, include_invalid=True)

# Output the files with specified names
generate_files(normal_coefficients, 'input_sk.hex', 'output_encoded_sk.hex')
generate_files(error_coefficients, 'error_input_sk.hex', 'error_output_encoded_sk.hex')
