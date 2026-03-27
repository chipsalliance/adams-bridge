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

def default_random_bytes(length):
    """
    Default random bytes generator using os.urandom
    
    :param int length: number of random bytes to generate
    :return: random bytes
    :rtype: bytes
    """
    return os.urandom(length)

def write_kat_vectors_from_json(ML_KEM, operation: int, output_dir: str):
    group_idx = int(2)
    """
    operation:
      1 = keygen only
      2 = encaps only
      3 = decap only
    group_idx: 0→512, 1→768, 2→1024
    output_dir: dir to write one .hex file per test
    """

    # pick the right JSON and offset
    if operation == 1:
        json_path = "assets/ML-KEM-keyGen-FIPS203/internalProjection.json"
        group_offset = 0
    else:
        json_path = "ML-KEM/assets/ML-KEM-encapDecap-FIPS203/internalProjection.json"
        # encap lives in testGroups[0..2], decap in [3..5]
        group_offset = 0 if operation == 2 else 3

    # load all test groups
    with open(json_path, "r") as f:
        data = json.load(f)

    # select the one group
    tg = data["testGroups"][group_offset + group_idx]
    tests = tg["tests"]

    os.makedirs(output_dir, exist_ok=True)

    for test in tests:
        tcid = test.get("tcId", tests.index(test))
        fname = os.path.join(output_dir,
            f"op{operation}_g{group_idx}_t{tcid}.hex"
        )

        with open(fname, "w") as out:
            # first line = the operation code
            out.write(f"{operation}\n")

            if operation == 1:
                # keygen: d, z → ek, dk
                d   = bytes.fromhex(test["d"])
                z   = bytes.fromhex(test["z"])
                ek  = bytes.fromhex(test["ek"])
                dk  = bytes.fromhex(test["dk"])
                out.write("\n".join([
                    d.hex(),
                    z.hex(),
                    ek.hex(),
                    dk.hex()
                ]) + "\n")

            elif operation == 2:
                # encaps: m, ek → K, c
                m   = bytes.fromhex(test["m"])
                ek  = bytes.fromhex(test["ek"])
                k   = bytes.fromhex(test["k"])
                c   = bytes.fromhex(test["c"])
                out.write("\n".join([
                    m.hex(),
                    ek.hex(),
                    k.hex(),
                    c.hex()
                ]) + "\n")

            elif operation == 3:
                # decap: dk, c → K′
                # Note: for decap the group has a shared dk at tg["dk"]
                dk_hex = tg.get("dk")
                if dk_hex is None:
                    raise ValueError("Missing shared 'dk' in testGroups for decap")
                dk = bytes.fromhex(dk_hex)

                c   = bytes.fromhex(test["c"])
                k   = bytes.fromhex(test["k"])
                out.write("\n".join([
                    dk.hex(),
                    c.hex(),
                    k.hex()
                ]) + "\n")

            else:
                raise ValueError(f"Unsupported operation {operation}")

    print(f"Wrote {len(tests)} test‐vector files for op={operation}, group={group_idx} → {output_dir}")




    """
    operation:
      1 = keygen only
      2 = encaps only
      3 = decap only
    """
write_kat_vectors_from_json(
    ML_KEM_1024,
    operation=2,
    output_dir="tv/encap_KAT.txt"
)
