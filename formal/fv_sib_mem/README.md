<!--
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# sib_mem - Formal Verification
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files are part of the main directory **formal/fv_sib_mem**:

- **fv_sib_mem_top.sv**: Top-level assertion IP (AIP) and wrapper for the sib_mem block
- **fv_sib_mem_memory.sv**: Memory model utility used by the AIP to track and validate read/write data integrity


## DUT Overview

The DUT `sib_mem` implements the sample-in-ball memory buffer used within the MLDSA sampler pipeline. It stores intermediate sampling data and exposes a read/write interface to the surrounding datapath.

Typical interface signals exercised by the AIP include:
- `clk`, `reset_n`: Clock and active-low reset.
- Memory read/write request signals, addresses, and data buses.
- Chip-select and enable controls.


## Assertion IP Overview

The Assertion IP validates correct memory read/write protocol behavior:

- Reset correctness: memory outputs are initialized properly after reset.
- Write protocol: data written at a given address is subsequently readable at that address.
- Read protocol: no stale or out-of-bounds data is returned.
- The `fv_sib_mem_memory.sv` model tracks the expected memory state and compares it against observed DUT outputs.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
