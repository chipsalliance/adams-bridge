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

# sigdecode_z_top - Formal Verification
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_sigdecode_z_top**

- **fv_sigdecode_z_top_m.sv**: Main assertion IP containing the FSM properties
- **fv_sigdecode_z_top_pkg.sv**: Package definitions and shared types
- **fv_sigdecode_z_top_functions.sv**: Helper functions for the AIP
- **fv_sigdecode_z_top_binding.sv**: AIP binding file
- **fv_sigdecode_z_top_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model
  - `model/sigdecode_z_top.h`: High-level abstracted model
  - `model/sigdecode_z_top.luref`: LUBIS coverage and liveness reference


## DUT Overview

The DUT `sigdecode_z_top` implements the signature coefficient decode logic for the **z** component used during MLDSA verify operations. It decodes encoded polynomial coefficients from the signature into their original representation and writes the results to memory.

Typical interface signals exercised by the AIP include:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- `sigdecode_z_enable`: Enable signal that starts the decode operation.
- `dest_base_addr`: Base address for writing decoded output to memory.
- Memory write interface: request channel, address, and data buses.
- `sigdecode_z_done`: Done flag indicating operation completion.
- `sigdecode_z_error`: Error flag indicating an out-of-range input value.


## Assertion IP Overview

The Assertion IP validates the FSM sequencing, memory write protocol, and correct decoding of encoded z-coefficients. Properties cover:

- Reset and initialization correctness.
- FSM state transitions from idle through decode to done.
- Sequential memory write address generation and data correctness.
- Liveness: the operation eventually completes or raises a controlled error.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
