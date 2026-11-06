_*SPDX-License-Identifier: Apache-2.0<BR>
<BR>
<BR>
Licensed under the Apache License, Version 2.0 (the "License");<BR>
you may not use this file except in compliance with the License.<BR>
You may obtain a copy of the License at<BR>
<BR>
http://www.apache.org/licenses/LICENSE-2.0 <BR>
<BR>
Unless required by applicable law or agreed to in writing, software<BR>
distributed under the License is distributed on an "AS IS" BASIS,<BR>
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
See the License for the specific language governing permissions and<BR>
limitations under the License.*_<BR>

# **Release Notes** #
_*Last Update: 2026/11/03*_

### Rev 3p0 ###

#### Rev 3p0 release date: TBD (in development) ####
MLDSA_CORE_VERSION and MLKEM_CORE_VERSION report "3.0.0". Rev 3p0 changes the
masking architecture and the integration interface relative to Rev 2p0. The
Rev 2p0 verification statements below do not apply to Rev 3p0; Rev 3p0
verification status will be recorded at release sign-off per the
[release checklist](docs/AdamsBridgeReleaseChecklist.md).
- Architecture
    - Architectural-level arithmetic masking: coefficients are stored as two
      shares and recombined in downstream consumers (#278, #282, #292)
    - Masked Keccak (two-share, DOM-based), enabled by default (#293)
    - ML-KEM ByteDecode12 applies full modular reduction (#310)
    - LFSR configuration corrected (#306)
- Integration interface and compatibility
    - New `abr_top` parameters `MASKING_EN` (default 1), `SHA3_MASKING_EN`
      (default 1) and `SRAM_LATENCY` (default 1) (#233, #293)
    - `MASKING_EN = 1` requires four additional `_masked` SRAM instances; see
      the [Hardware Specification](docs/AdamsBridgeHardwareSpecification.md)
    - Technology primitive swap via `ABR_PRIM_MODULE_PREFIX`/`ABR_PRIM_ROOT`, or
      shared Caliptra cells when integrated with Caliptra (#300, #304); see the
      [Integration Specification](docs/AdamsBridgeIntegrationSpecification.md)
    - `MLDSA_STATUS.VERIFY_PASS` reports the ML-DSA verification result (#297)
    - Firmware must issue ZEROIZE after every completed operation before the
      next command (#283)
    - Key vault read-side length-mismatch handling for ML-DSA/ML-KEM (#294)
- Documentation
    - ML-KEM decapsulation key reuse restriction (#311)

### Rev 2p0 ###

#### Rev 2p0 release date: 2025/10/07 ####
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- ML-DSA-87 – Based on FIPS204
- ML-KEM-1024 – Based on FIPS203
- Verification
    - Smoke tests for all scenarios described in test plan passing
    - Nightly regressions on-going
    - UVM for ML-DSA-87 and ML-KEM 1024
    - Formal Verification sign off for ML-KEM complete

## Previous Releases ##

### Rev 2p0-rc1 ###
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- ML-DSA-87 – Based on FIPS204
- ML-KEM-1024 – Based on FIPS203
- Verification
    - Smoke tests for all scenarios described in test plan passing
    - Nightly regressions on-going
    - UVM for ML-DSA-87 and ML-KEM 1024
    - Formal Verification sign off for ML-KEM in progress

## Previous Releases ##

### Rev 1p0 ###

#### Rev 1p0 release date: 2025/04/29 ####
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- Variable message signing and data swizzling

### Rev 1p0-rc1 ###

#### Rev 1p0-rc1 release date: 2025/03/05 ####
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- AdamsBridge README updates to clarify test cases and running with VCS
- ML-DSA-87 – Based on FIPS204
    - Supporting Pure ML-DSA
    - Embedded shuffling and masking countermeasures
    - AHB register interface
    - Keyvault interface
- Verification
    - Smoke tests for all scenarios described in test plan passing
    - Nightly regression on ML-DSA-87 block on-going
    - UVM for ML-DSA-87
    - Formal Verification
