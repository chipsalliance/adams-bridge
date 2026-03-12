# ML-KEM Reference Model

This is a pure-Python implementation of ML-KEM (FIPS 203), used as a
reference model for RTL verification test-vector generation.

## Origin

Derived from **kyber-py** by Giacomo Pope:
  https://github.com/GiacomoPope/kyber-py

Licensed under MIT OR Apache-2.0 (dual-licensed). See [LICENSE](LICENSE) for details.

## Modifications

The following changes were made to adapt the upstream code for hardware
verification use:

- **Flat imports**: changed package-relative imports to flat file imports so
  the model can run standalone without `pip install`.
- **Deterministic entry points**: added `keygen_with_d_z(d, z)` and
  `encaps_with_m(ek, m)` methods to accept explicit seeds/randomness from
  UVM test sequences for RTL comparison.
- **Python 3.9 compatibility**: removed Python 3.10+ type hints.
- **Standalone `Module.py`**: merged upstream `modules/` and `polynomials/`
  packages into a single file.
