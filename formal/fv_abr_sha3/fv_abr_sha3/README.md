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

# abr_sha3 - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The `fv_abr_sha3` directory contains the formal assertion IP for the SHA3 support logic in the Adams Bridge design.

- `model`: Contains abstracted model files and binding wrappers for the SHA3 verification environment.
- `properties`: Contains environment constraints and ancillary formal files.
  - `abr_sha3.luref`: Liveness and coverage reference file for the SHA3 assertion IP.
  - `fv_abr_sha3.h`: Helper header file for formal compilation and tool integration.

The root directory contains the main verification files:
- `fv_abr_sha3.sv`: Main assertion IP for SHA3 control and data-flow verification.
- `fv_abr_sha3_binding.sv`: DUT signal binding and connection of properties to the SHA3 module interface.
- `fv_abr_sha3_constraints.sv`: Environment constraints that restrict input stimuli to valid SHA3 protocol behavior.
- `fv_abr_sha3_pkg.sv`: Package definitions, parameter declarations, and shared types used by the SHA3 properties.
- `fv_abr_sha3_whitebox.sv`: White-box assertions for internal state and pipeline verification.
- `lubis_incr_counter.sv`: Supporting helper module used for counter and handshake verification.
- `waiver_list_done_i_disabled.tcl`: Waiver list for coverage items that are intentionally excluded or out of scope.

## DUT Overview
The DUT under verification is the SHA3 interface/control logic within the Adams Bridge cryptographic datapath. It is responsible for managing the SHA3 hash engine handshake, data flow, and timing interaction with the broader MLDSA pipeline.

The SHA3 assertion IP verifies:
- proper initialization and reset behavior
- valid-ready handshake protocol with the SHA3 engine
- correct sequencing of SHA3 request, digest, and done signaling
- stability and integrity of control and status outputs

## Assertion IP Overview
The SHA3 assertion IP is organized into the following verification areas:

### Initialization and Reset Assertions
- Ensure all control registers and internal state are reset on reset.
- Confirm that reset and secure clear signals properly initialize the SHA3 logic.
- Verify that mode and control inputs are stable during reset.

### Handshake and Protocol Assertions
- Validate the SHA3 valid-ready handshake protocol semantics.
- Confirm that the module asserts `ready` only when it can consume valid SHA3 data.
- Verify that `valid` and `ready` are never simultaneously asserted incorrectly.
- Check for no-data-loss and proper flow control across the SHA3 interface.

### FSM and Sequence Assertions
- Verify valid state transitions in the SHA3 control FSM.
- Confirm that SHA3 operation sequences follow the expected order from request to completion.
- Ensure operation modes remain consistent while the SHA3 transaction is in progress.

### White-box Assertions
- Observe key internal state elements and pipeline registers.
- Validate intermediate control signals used by the SHA3 datapath.
- Detect invalid internal state combinations and illegal transitions.

### Output Control and Data Integrity Assertions
- Check that `done` and `error` outputs are asserted only in valid conditions.
- Ensure SHA3 output data is stable and correctly latched when presented.
- Verify that control outputs corresponding to SHA3 enable/disable are coherent with the FSM state.

### Additional Properties
- Confirm that the SHA3 interface does not deadlock.
- Verify liveness properties so that a valid request eventually completes or raises an error.
- Check that handshake and control signals are mutually exclusive where required.
- Ensure counter and timing assertions capture expected protocol behavior.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
