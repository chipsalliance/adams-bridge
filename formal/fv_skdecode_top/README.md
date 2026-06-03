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

# skdecode_top - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The `fv_skdecode_top` directory contains assertion IP and helper files for formal verification of the secret-key decode top-level logic used in the MLDSA pipeline.

- `fv_skdecode_top_m.sv`: Main assertion IP containing the FSM and sequencing properties
- `fv_skdecode_top_pkg.sv`: Package definitions and shared types
- `fv_skdecode_top_functions.sv`: Helper functions for the AIP
- `fv_skdecode_top_binding.sv`: AIP binding file
- `fv_skdecode_top_scoreboard.sv`: Scoreboard and transaction-tracking properties used to validate end-to-end protocol behavior and data consistency.
- `fv_skdecode_top_wrapper.sv`: Wrapper that instantiates constraints, scenarios, covers, and the AIP for tool flows.
- model: Contains the high level abstracted model
  - `model/skdecode_top.h`: High-level abstracted model and interface description for the DUT used by the formal flow.

## DUT Overview
The DUT `skdecode_top` implements the secret-key decode logic used during MLDSA signature operations. It interfaces with memory, the sampler/NTT datapath, and control logic to reconstruct secret-key related values. The AIP monitors the handshake, memory accesses, and internal consistency of the decoding flow.

Typical interface signals exercised by the AIP include:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- Mode and control inputs: mode selection, start/enable signals relevant to decode operation.
- Memory interfaces: read/write request channels, addresses, and data buses.
- Handshake signals with sampler/NTT blocks and any scoreboard-driven interfaces.
- Status outputs: `busy`, `done`, and error/status indicators.

## Assertion IP Overview
The assertion IP is organized to validate initialization, FSM sequencing, memory and handshake protocols, scoreboard consistency, and liveness.

### Initialization and Reset Assertions
- Verify that control registers and pipeline state are reset on `reset_n` or `zeroize`.
- Confirm the DUT starts in a safe idle state after reset.

### FSM and Sequence Assertions
- Check legal FSM states and transitions for the decode operation.
- Ensure sequencing between memory reads, internal processing, and finalization follows the expected protocol.
- Validate `busy`/`done` assertions relative to operation completion.

### Memory and Interface Assertions
- Validate correct generation of memory read requests and address sequencing.
- Ensure memory handshake semantics are respected (no data-loss, no races).
- Confirm that decoded data is written or propagated correctly to downstream modules.

### Scoreboard and Transaction Tracking
- `fv_skdecode_top_scoreboard.sv` models expected protocol transactions and compares observed behavior against expected sequences.
- Scoreboard properties detect missing transactions, unexpected re-orderings, and data mismatches.

### Additional Properties and SVA
- Internal SVA artifacts in `model/sva/` provide additional checks and reference behaviors for state machines and data paths.
- Supplementary combinational and timing assertions validate pointer arithmetic, counters, and auxiliary logic.

### Liveness and Coverage
- Liveness properties ensure operations eventually complete or raise a controlled error.
- Coverage references in the model guide proof targets and demonstrate feature coverage.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
