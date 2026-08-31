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

# abr_sha3pad - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The `fv_abr_sha3pad` directory contains formal assertion IP for the SHA3 padding and handshake logic in the Adams Bridge SHA3 datapath.

- `waiver_list.tcl`: Waiver list for coverage items that are intentionally excluded or considered out of scope for formal coverage.
- `fv_abr_sha3pad_constraints.sv`: Environment constraints that restrict input stimuli to valid SHA3 padding and protocol behavior.
- `fv_abr_sha3pad.sv`: Main property file containing assertions that verify the SHA3 padding controller and related protocol semantics.
- `lubis_incr_counter.sv`: Supporting counter module used by the formal assertions and flow control checks.
- `lubis_scoreboard.sv`: Scoreboard model that tracks expected protocol transactions and data flow.
- `lubis_scoreboard_properties.sv`: Assertions and properties that validate scoreboard behavior and protocol conformance.
- `lubis_scoreboard_tracking.sv`: Tracking helpers for scoreboard state and transaction sequences.

## DUT Overview
The DUT under verification is the SHA3 padding and control logic responsible for managing message block padding, handshake sequencing, and valid-ready interfacing for the SHA3 engine.

This assertion IP verifies that:
- SHA3 padding requests are generated and consumed correctly
- valid-ready handshake semantics are respected throughout SHA3 transactions
- the SHA3 padding controller transitions through legal states only
- control outputs, data flow, and ready/valid timing behave correctly

## Assertion IP Overview
The SHA3 padding assertion IP is organized into these verification areas:

### Initialization and Reset Assertions
- Validate that control state and handshake signals are reset properly.
- Confirm that the design begins in a safe idle state after reset.
- Verify stability of inputs across reset boundaries.

### Padding and Protocol Assertions
- Ensure padding requests follow the correct SHA3 padding protocol.
- Verify that message block boundaries are handled properly.
- Confirm that padding generation does not violate valid-ready handshakes.

### Handshake and Flow Control Assertions
- Validate the `valid`/`ready` handshake protocol on SHA3 request and response interfaces.
- Confirm that `ready` is only asserted when the module can accept a transaction.
- Ensure that transaction completion occurs only when both sides agree.

### Scoreboard and Tracking Assertions
- Track expected protocol behavior using the scoreboard model.
- Confirm that observed transactions match the expected handshake sequence.
- Detect protocol violations, missing transactions, and unexpected state changes.

### Additional Properties
- Check for deadlock-free operation in the SHA3 padding controller.
- Validate liveness: valid requests eventually complete or raise a controlled error.
- Ensure no illegal internal state combinations or invalid transitions occur.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
