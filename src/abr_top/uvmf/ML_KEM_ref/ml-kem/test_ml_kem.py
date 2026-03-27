import unittest
import json
from ml_kem import ML_KEM

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


class TestML_KEM_KAT(unittest.TestCase):
    """
    Test ML-KEM against test vectors collected from
    https://github.com/usnistgov/ACVP-Server/releases/tag/v1.1.0.35
    """

    def generic_keygen_kat(self, ML_KEM, index):
        with open("assets/ML-KEM-keyGen-FIPS203/internalProjection.json") as f:
            data = json.load(f)
        kat_data = data["testGroups"][index]["tests"]

        for test in kat_data:
            d_kat = bytes.fromhex(test["d"])
            z_kat = bytes.fromhex(test["z"])
            ek_kat = bytes.fromhex(test["ek"])
            dk_kat = bytes.fromhex(test["dk"])

            ek, dk = ML_KEM._keygen_internal(d_kat, z_kat)
            print(f"ek: {ek.hex()}")
            print(f"dk: {dk.hex()}")
            self.assertEqual(ek, ek_kat)
            self.assertEqual(dk, dk_kat)

    def generic_encap_kat(self, ML_KEM, index):
        with open(
            "assets/ML-KEM-encapDecap-FIPS203/internalProjection.json"
        ) as f:
            data = json.load(f)
        kat_data = data["testGroups"][index]["tests"]

        for test in kat_data:
            ek_kat = bytes.fromhex(test["ek"])
            dk_kat = bytes.fromhex(test["dk"])
            c_kat = bytes.fromhex(test["c"])
            k_kat = bytes.fromhex(test["k"])
            m_kat = bytes.fromhex(test["m"])

            K, c = ML_KEM._encaps_internal(ek_kat, m_kat)
            self.assertEqual(K, k_kat)
            self.assertEqual(c, c_kat)

            K_prime = ML_KEM.decaps(dk_kat, c_kat)
            self.assertEqual(K_prime, k_kat)

    def generic_decap_kat(self, ML_KEM, index):
        with open(
            "assets/ML-KEM-encapDecap-FIPS203/internalProjection.json"
        ) as f:
            data = json.load(f)
        kat_data = data["testGroups"][3 + index]["tests"]

        # Parse out the decaps key
        dk_hex = data["testGroups"][3 + index]["dk"]
        dk_kat = bytes.fromhex(dk_hex)

        # Ensure that decaps works
        for test in kat_data:
            c_kat = bytes.fromhex(test["c"])
            k_kat = bytes.fromhex(test["k"])
            K = ML_KEM.decaps(dk_kat, c_kat)
            self.assertEqual(K, k_kat)

    def test_ML_KEM_1024_keygen(self):
        print("Running ML-KEM-1024 keygen KAT")
        self.generic_keygen_kat(ML_KEM_1024, 2)
        print("Completed ML-KEM-1024 keygen KAT")

    def test_ML_KEM_1024_encap(self):
        print("Running ML-KEM-1024 encap KAT")
        self.generic_encap_kat(ML_KEM_1024, 2)
        print("Completed ML-KEM-1024 encap KAT")


    def test_ML_KEM_1024_decap(self):
        print("Running ML-KEM-1024 decap KAT")
        self.generic_decap_kat(ML_KEM_1024, 2)
        print("Completed ML-KEM-1024 decap KAT")


if __name__ == '__main__':
    unittest.main()
