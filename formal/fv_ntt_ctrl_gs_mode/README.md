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

# ntt_ctrl - gs_mode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectories are part of the `formal/fv_ntt_ctrl_gs_mode` directory:

- `fv_ntt_ctrl_gs_mode_m.sv`: Main assertion IP for GS-mode behavior and protocol checks
- `fv_ntt_ctrl_gs_mode_pkg.sv`: Package definitions, parameters, and shared types used by the AIP
- `fv_ntt_ctrl_gs_mode_functions.sv`: Helper functions used by assertions and checks
- `fv_ntt_ctrl_gs_mode_binding.sv`: Binding module that connects the assertions to DUT signals
- `fv_ntt_ctrl_gs_mode_constraints.sv`: Environment constraints that restrict input stimuli to valid GS-mode protocol and scenarios.
- `fv_ntt_ctrl_gs_mode_additional_properties.sv`: Additional properties and checks that complement the main AIP.
- model: Contains reference model and tool project files
  - `model/ntt_ctrl_gs_mode.h`: High-level abstracted model used by the formal flow.
  - `model/ntt_ctrl_gs_mode.luref`: Liveness and coverage reference for GS-mode assertions.
  - `model/project.lutar`: Tool-specific project file for formal runs.

## DUT overview
The DUT `NTT_CTRL` in GS mode manages read/write sequencing, memory addresses, and control flow for the Gentleman-Sande (GS) NTT variant within the MLDSA pipeline. GS mode behavior differs from CT mode primarily in sequencing, buffer usage, and interactions with sampler/accumulate signals.

Typical primary ports and signals exercised by the GS-mode AIP include:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- `ntt_mode`: Selects operation mode (ct, gs, pwm, pwo, pws); GS-mode properties assume `ntt_mode == gs`.
- `ntt_enable`: Starts an NTT operation when asserted.
- `butterfly_ready` / internal readiness signals: Indicate readiness for butterfly computation.
- `buf0_valid`, `buf*_valid`: Buffer-valid signals used to gate read/write stages.
- `sampler_valid`: In GS mode the sampler interaction may be exercised depending on configuration.
- `accumulate`: Accumulation control used in certain GS workflows.
- `ntt_mem_base_addr`, `shuffle_en`, `random`: Addressing and control inputs that affect scheduling and bufferring.
- Outputs such as `bf_enable`, `opcode`, `buf_*` control signals, `twiddle_addr`, `mem_rd_addr`, `mem_wr_addr`, `mem_rd_en`, `mem_wr_en`, `pw_rden`, `pw_wren`, `busy`, and `done` are monitored by the AIP.

The GS-mode AIP focuses on verifying that address generation, buffer management, and sequencing conform to GS-mode semantics while respecting handshake and memory protocols.

## Assertion IP overview
The GS-mode AIP binds its properties to the DUT signals (reset bound to `(!ntt_ctrl.reset_n || ntt_ctrl.zeroize)`) and is organized similarly to the CT-mode AIP: read FSM assertions, write FSM assertions, protocol and combinational checks, and eventuality/liveness properties.

### Read and Write FSM Assertions
- Read FSM assertions ensure correct transitions from `read_idle` -> `read_stage` -> `read_buf` -> `read_exec` (and related wait states) under GS-specific conditions.
- Write FSM assertions ensure write sequencing (`write_idle` -> `write_stage` -> `write_mem`) and that `wr_valid_count`/`rd_valid_count` and buffer counts drive the expected transitions.
- Properties assert both that required transitions occur and that state encodings remain one-hot/consistent.

### Mode-Specific and Sequence Assertions
- Verify GS-specific sequencing for address calculation and twiddle index progression.
- Ensure appropriate use of `accumulate` and `sampler_valid` signals where applicable.
- Check that GS-mode does not assert PWM/PWO control signals unexpectedly.

### Additional/Combinational Properties
- Buffer and pointer assertions (enable, write/read pointers, reset counters).
- Memory request and write-data correctness for GS-mode transfers.
- `busy` / `done` correctness and timing relative to FSM progression.
- Twiddle address and buffer pointer integrity checks.

### Liveness and Eventuality
- The AIP includes eventuality properties ensuring that every transient state is eventually left and that progress is made (no permanent stalls).
- Coverage reference (`.luref`) is provided to measure property coverage and guide proof efforts.

## Additional properties
The `fv_ntt_ctrl_gs_mode_additional_properties.sv` file contains supplementary checks that may include:

- Assertion of combinational signal invariants: `assert_buf_wren_a`, `assert_buf_wren_intt_reg_a`, `assert_buf_rden_a`, `assert_twiddle_addr_a`, `assert_mem_rd_en_a`, `assert_mem_wr_en_a`, `assert_buf_wr_rst_count_a`, `assert_buf_rd_rst_count_a`, `assert_busy_a`, `assert_rst_rounds_a`, `assert_different_rd_wr_addrs_a`.
- Protocol-specific checks not covered by the main FSM properties.
- Miscellaneous correctness and safety properties tailored to GS-mode.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
