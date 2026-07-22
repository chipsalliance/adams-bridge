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

# ntt_top - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The `fv_ntt_top` directory contains assertion IP and helper files for formal verification of the NTT top-level controller and datapath.

- `fv_ntt_top_constraints.sv`: Environment constraints that restrict input stimuli to valid protocol and operational scenarios.
- `fv_ntt_top_covers.sv`: Coverage and liveness check definitions used to measure proof progress and feature coverage.
- `fv_ntt_top.sv`: Main assertion IP containing top-level properties that verify control, memory, and handshake behavior.
- `fv_ntt_top_internal.sv`: Internal white-box assertions and checks for submodules and pipeline state.
- `fv_ntt_top_wrapper.sv`: Wrapper module that instantiates constraints, scenarios, covers, and the top-level AIP for tool flows.
- `fv_ntt_top_scenarios.sv`: Scenario generators and environment models used to exercise different NTT modes and corner cases.

## DUT Overview
The DUT under verification is the NTT top-level controller and associated datapath used in the MLDSA pipeline. The NTT controller manages memory accesses, round scheduling, PWM/PWO interfaces, shuffling, sampling interactions, and mode-specific behavior (e.g., CT, GS, PWM modes).

Key interface signals (high-level):
- `pi_clk`, `pi_reset_n`, `pi_zeroize`: Clock, active-low reset, and secure clear.
- `pi_mode`: Operation mode (ct, gs, pwm, pwm_intt, etc.).
- `pi_ntt_enable`: Overall enable for NTT operation.
- Memory interfaces: `po_mem_wr_req`, `po_mem_rd_req`, `po_mem_wr_data`, `pi_mem_rd_data` for external memory transactions.
- PWM/PWO interfaces: `po_pwm_a_rd_req`, `po_pwm_b_rd_req`, `pi_pwm_a_rd_data`, `pi_pwm_b_rd_data`.
- Control/status outputs: `po_ntt_busy`, `po_ntt_done`.
- Additional inputs: `pi_shuffle_en`, `pi_sampler_valid`, `pi_masking_en`, random seeds and helper signals.

## Assertion IP Overview
The NTT AIP is structured to validate control correctness, protocol conformance, memory integrity, and liveness across all supported modes.

### Initialization and Reset Assertions
- Verify all control registers and FSM states are properly reset on `pi_reset_n` or `pi_zeroize`.
- Confirm that the DUT enters a safe idle state after reset and that inputs are stable across reset boundaries.

### FSM and Sequence Assertions
- Check legal FSM states and valid state transitions for mode-specific flows (CT, GS, PWM, PWM_INTT).
- Validate sequencing for round scheduling, shuffling, accumulation, and finalization.
- Ensure `po_ntt_done` is asserted only after the full operation completes.

### Memory Interface Assertions
- Validate `po_mem_wr_req`/`po_mem_rd_req` generation, address sequencing, and write-data correctness across modes.
- Ensure memory handshake semantics are respected and no read/write races occur.
- Check that PWM/PWO memory accesses follow the expected address and timing patterns.

### Handshake and Flow Control Assertions
- Confirm valid-ready-like semantics for sampler and PWM interfaces (`pi_sampler_valid`, `po_pwm_*_rd_req`).
- Ensure enables are asserted only when downstream modules are ready to accept data.
- Detect data-loss and ordering violations across handshake boundaries.

### White-box/Internal Assertions
- `fv_ntt_top_internal.sv` contains visibility into internal registers, counters, and helper modules.
- Verify intermediate pipeline registers, counter behavior, and submodule interactions.
- Detect illegal internal state combinations and timing violations.

### Scenarios and Coverage
- `fv_ntt_top_scenarios.sv` exercises the AIP with typical and corner-case transaction sequences.
- `fv_ntt_top_covers.sv` measures coverage and liveness; use it to guide proof bound increases and constraint relaxation.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
