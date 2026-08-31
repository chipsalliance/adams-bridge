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

# sigencode_z_top - Formal Verification
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_sigencode_z_top**

- **fv_sigencode_z_top_m.sv**: Main assertion IP containing the FSM properties
- **fv_sigencode_z_top_pkg.sv**: Package definitions and shared types
- **fv_sigencode_z_top_functions.sv**: Helper functions for the AIP
- **fv_sigencode_z_top_binding.sv**: AIP binding file
- **fv_sigencode_z_top_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model
  - `model/sigencode_z_top.h`: High-level abstracted model
  - `model/sigencode_z_top.luref`: LUBIS coverage and liveness reference


## DUT Overview

The DUT `sigencode_z_top` implements the signature coefficient encode logic for the **z** component used during MLDSA sign operations. It encodes polynomial coefficients read from memory into a packed bit representation suitable for inclusion in the signature.

Typical interface signals exercised by the AIP include:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- `sigencode_z_enable`: Enable signal that starts the encode operation.
- `src_base_addr`: Base address for reading input coefficients from memory.
- `dest_base_addr`: Base address for writing encoded output to memory.
- Memory read/write interfaces: request channels, addresses, and data buses.
- `sigencode_z_done`: Done flag indicating operation completion.
- `sigencode_z_error`: Error flag indicating an out-of-range coefficient.


## Assertion IP Overview

The Assertion IP validates the FSM sequencing, memory read/write protocol, and correct encoding of z-coefficients. Properties cover:

- Reset and initialization correctness.
- FSM state transitions from idle through encode to done.
- Sequential memory read address generation and correct output packing.
- Liveness: the operation eventually completes or raises a controlled error.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
