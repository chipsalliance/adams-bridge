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

# abr_keccak_round - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The `fv_abr_keccak_round` directory contains formal assertion IP for the Keccak round function within the SHA3 datapath.

- `model`: Contains formal model and reference files for the Keccak round verification environment.
  - `abr_sha3_round.h`: Header file used by the formal tool and compilation flow.
  - `abr_sha3_round.luref`: Liveness and coverage reference file for the Keccak round assertion IP.
  - `project.lutar`: Tool-specific project file for the formal verification flow.
- `properties`: Contains the main assertion files, constraints, and package definitions.
  - `fv_abr_keccak_round_binding.sv`: Binding module that connects the Keccak round assertions to DUT signals.
  - `fv_abr_keccak_round_constraints.sv`: Environment constraints to restrict input stimuli and enforce valid protocol behavior.
  - `fv_abr_keccak_round_functions.sv`: Helper functions used by assertions and property checks.
  - `fv_abr_keccak_round_pkg.sv`: Package definitions, parameter declarations, and shared types for the assertion IP.
  - `fv_abr_keccak_round_top.sv`: Top-level assertion IP module for the Keccak round verification environment.

## DUT Overview
The DUT under verification is the Keccak round function and associated control logic used in the SHA3 permutation stage.

This assertion IP verifies that:
- Keccak round inputs and outputs follow the expected data transformation sequence
- internal state updates and round operations behave correctly
- control and handshake signals are stable and valid during round execution
- the Keccak round function does not violate protocol or state invariants

## Assertion IP Overview
The Keccak round assertion IP is organized into the following verification areas:

### Initialization and Reset Assertions
- Ensure the Keccak round logic and control state are reset properly.
- Confirm that the DUT begins in a safe state after reset.
- Verify that input and control signals are stable across reset boundaries.

### Keccak Round Function Assertions
- Validate the round function state transitions and data transformations.
- Confirm that each round operates on the correct internal state.
- Verify that round outputs are produced only when inputs are valid and the handshake is complete.

### Protocol and Handshake Assertions
- Check valid-ready handshake semantics on the Keccak round interface.
- Ensure that `ready` is asserted only when the DUT can accept a new round input.
- Confirm that `valid` and `ready` interactions follow the expected transaction model.

### Function and Package Support
- `fv_abr_keccak_round_functions.sv` provides reusable helper functions for formal checks.
- `fv_abr_keccak_round_pkg.sv` defines shared types, constants, and parameters for the assertion IP.

### Additional Properties
- Verify the design is deadlock-free during Keccak round processing.
- Confirm liveness properties so valid inputs eventually produce valid outputs.
- Check for illegal internal state combinations and invalid round sequencing.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
