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
_*Last Update: 2025/09/04*_

### Rev 1.0.2 ###

#### Rev 1.0.2 release date: 2025/09/04 ####
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- [BUG FIX] Harden key vault read logic with swwe, limiting control access during engine operation (#204)
- [BUG FIX] Fix zeroize logic to prevent read/write collision in SRAMs [#203](https://github.com/chipsalliance/adams-bridge/issues/203)


## Previous Releases ##

### Rev 1.0.1 ###

#### Rev 1.0.1 release date: 2025/05/23 ####
- AdamsBridge Hardware Specification: see docs/ folder
- AdamsBridge SCA Specification: see docs/ folder
- AdamsBridge testplan: see docs/ folder
- [BUG FIX] Fix variable message byte drop bug [#145](https://github.com/chipsalliance/adams-bridge/issues/145)

### Rev 1.0 ###

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
