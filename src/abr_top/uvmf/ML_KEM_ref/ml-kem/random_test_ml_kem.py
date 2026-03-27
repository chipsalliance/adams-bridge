# python3 ml_kem_vectors.py 1 \
#     -o tv/keygen_ext_output.txt \
#     -i tv/keygen_ext_input.txt


import unittest
import json
from ml_kem import ML_KEM
import os

"""
The parameters defined in the FIPS 203 document.

Includes the ML-KEM-512, ML-KEM-768, and ML-KEM-1024 parameters
and initialised objects with them.
"""



# TODO: we can only allow a user to select one of the following three
# we should maybe put these into the class and only allow a user to
# select 128, 192 or 256 bit security.
DEFAULT_PARAMETERS = {
    "ML512": {"k": 2, "eta_1": 3, "eta_2": 2, "du": 10, "dv": 4},
    "ML768": {"k": 3, "eta_1": 2, "eta_2": 2, "du": 10, "dv": 4},
    "ML1024": {"k": 4, "eta_1": 2, "eta_2": 2, "du": 11, "dv": 5},
}
"""Parameters for the :py:obj:`.ML_KEM` objects."""


ML_KEM_1024 = ML_KEM(DEFAULT_PARAMETERS["ML1024"])
"""
Key exchange object that uses ML-KEM-1024 parameters internally.

Provides about 256 bit level of security.

Part of stable API.
"""

class TestML_KEM(unittest.TestCase):
    """
    Test ML_KEM levels for internal
    consistency by generating key pairs
    and shared secrets.
    """

    def generic_test_ML_KEM(self, ML_KEM, count):
        for _ in range(count):
            (ek, dk) = ML_KEM.keygen()
            for _ in range(count):
                (K, c) = ML_KEM.encaps(ek)
                K_prime = ML_KEM.decaps(dk, c)
                self.assertEqual(K, K_prime)

    def test_ML_KEM_1024(self):
        self.generic_test_ML_KEM(ML_KEM_1024, 1)


def default_random_bytes(length):
    """
    Default random bytes generator using os.urandom
    
    :param int length: number of random bytes to generate
    :return: random bytes
    :rtype: bytes
    """
    return os.urandom(length)

import os

def write_ml_kem_vectors(operation: int,
                         output_filename: str,
                         use_external_input: bool = False,
                         input_filename: str = None,
                         compare_decapsulation: bool = False):
    # ————————————————————————
    # 1) READ OR GENERATE YOUR INPUTS
    # ————————————————————————
    if use_external_input:
        if not input_filename:
            raise ValueError("When use_external_input=True you must pass input_filename")
        with open(input_filename, "r") as f:
            # strip blank lines
            lines = [l.strip() for l in f if l.strip()]

        # First line *is* the op-code:
        op_from_file = int(lines[0])
        if op_from_file not in (1,2,3,4):
            raise ValueError(f"Bad op code {op_from_file} in {input_filename}")
        operation = op_from_file

        # Next lines are the hex values in the order you specified:
        data_lines = lines[1:]

        if operation == 1:
            # keygen: 2 lines → z, d
            if len(data_lines) < 2:
                raise ValueError("Need at least 2 lines for operation=1")
            z = bytes.fromhex(data_lines[0])
            d = bytes.fromhex(data_lines[1])
            m = default_random_bytes(32)
            # ————————————————————————
            # 2) RUN THE KEM OPERATIONS
            # ————————————————————————
            # keygen
            ek, dk = ML_KEM_1024.keygen_with_d_z(d, z)
            K, c = ML_KEM_1024.encaps_with_m(ek, m)
            K_prime = ML_KEM_1024.decaps(dk, c)

        elif operation == 2:
            # encap: 2 lines → m, ek
            if len(data_lines) < 2:
                raise ValueError("Need at least 2 lines for operation=2")
            m  = bytes.fromhex(data_lines[0])
            ek = bytes.fromhex(data_lines[1])
            # ————————————————————————
            # 2) RUN THE KEM OPERATIONS
            # ————————————————————————
            K, c = ML_KEM_1024.encaps_with_m(ek, m)

        elif operation == 3:
            # decap: 2 lines → dk, c
            if len(data_lines) < 2:
                raise ValueError("Need at least 2 lines for operation=3")
            dk = bytes.fromhex(data_lines[0])
            c  = bytes.fromhex(data_lines[1])
            # ————————————————————————
            # 2) RUN THE KEM OPERATIONS
            # ————————————————————————
            K_prime = ML_KEM_1024.decaps(dk, c)
            m = default_random_bytes(32)

        elif operation == 4:
            # full: 3 lines → z, d, m
            if len(data_lines) < 3:
                raise ValueError("Need at least 3 lines for operation=4")
            z = bytes.fromhex(data_lines[0])
            d = bytes.fromhex(data_lines[1])
            m = bytes.fromhex(data_lines[2])
            # ————————————————————————
            # 2) RUN THE KEM OPERATIONS
            # ————————————————————————
            # keygen
            ek, dk = ML_KEM_1024.keygen_with_d_z(d, z)
            K, c = ML_KEM_1024.encaps_with_m(ek, m)
            K_prime = ML_KEM_1024.decaps(dk, c)

    else:
        # generate fresh random inputs
        z = default_random_bytes(32)
        d = default_random_bytes(32)
        m = default_random_bytes(32)
        # ————————————————————————
        # 2) RUN THE KEM OPERATIONS
        # ————————————————————————
        # keygen
        ek, dk = ML_KEM_1024.keygen_with_d_z(d, z)
        K, c = ML_KEM_1024.encaps_with_m(ek, m)
        K_prime = ML_KEM_1024.decaps(dk, c)


    # decaps
    if compare_decapsulation:
        assert K_prime == K, "decapsulation did not recover the same K"

    # ————————————————————————
    # 3) DUMP TO YOUR OUTPUT FILE
    # ————————————————————————
    os.makedirs(os.path.dirname(output_filename), exist_ok=True)
    with open(output_filename, "w") as f:
        f.write(f"{operation}\n")
        if operation == 1:
            # keygen only: z, d → ek, dk
            f.write("\n".join([z.hex(), d.hex(), ek.hex(), dk.hex()]) + "\n")

        elif operation == 2:
            # encaps only: m, ek → K, c
            f.write("\n".join([m.hex(), ek.hex(), K.hex(), c.hex()]) + "\n")

        elif operation == 3:
            # decaps only: dk, c → K′
            f.write("\n".join([dk.hex(), c.hex(), K_prime.hex()]) + "\n")

        elif operation == 4:
            # full: z,d,m → ek,dk,K,c,K′
            f.write("\n".join([
                z.hex(), d.hex(), m.hex(),
                ek.hex(), dk.hex(),
                K.hex(), c.hex(), K_prime.hex()
            ]) + "\n")

        else:
            raise ValueError(f"Unsupported operation {operation}")



# if __name__ == '__main__':
#     unittest.main()

# # just keygen:
# write_ml_kem_vectors(1, "tv/keygen.txt")


# write_ml_kem_vectors(1,
#                      output_filename="tv/keygen_ext_output.txt",
#                      use_external_input=True,
#                      input_filename="tv/keygen_ext_input.txt")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(
        description="Generate ML-KEM test vectors (operations 1-4)."
    )
    parser.add_argument(
        "operation",
        type=int,
        choices=[1,2,3,4],
        help="Which operation to perform: 1=keygen, 2=encap, 3=decap, 4=full"
    )
    parser.add_argument(
        "-o", "--output",
        default="tv/output.txt",
        help="Output filename"
    )
    parser.add_argument(
        "-i", "--input",
        default=None,
        help="Optional input filename (for external inputs)"
    )
    parser.add_argument(
        "--compare",
        action="store_true",
        help="Enable decapsulation check"
    )
    args = parser.parse_args()

    write_ml_kem_vectors(
      operation=args.operation,
      output_filename=args.output,
      use_external_input=(args.input is not None),
      input_filename=args.input,
      compare_decapsulation=args.compare
    )





