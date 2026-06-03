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

# ntt_ctrl - pwm_intt_mode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectories are part of the `formal/fv_ntt_ctrl_pwm_intt` directory:

- `model/ntt_ctrl_pwm_intt.h`: High-level abstracted model used by the formal flow.
- `model/ntt_ctrl_pwm_intt.luref`: Liveness and coverage reference for PWM_INTT-mode assertions.
- `model/project.lutar`: Tool-specific project file for formal runs.
- `fv_ntt_ctrl_pwm_intt_pkg.sv`: Package definitions, parameters, and shared types used by the AIP.
- `fv_ntt_ctrl_pwm_intt_functions.sv`: Helper functions used by assertions and checks.
- `fv_ntt_ctrl_pwm_intt_binding.sv`: Binding module that connects the assertions to DUT signals.
- `fv_ntt_ctrl_pwm_intt_m.sv`: Main assertion IP for PWM_INTT-mode behavior and protocol checks.
- `fv_ntt_ctrl_pwm_intt_constraints.sv`: Environment constraints that restrict input stimuli to valid PWM_INTT scenarios.
- `fv_ntt_ctrl_pwm_intt_additional_properties.sv`: Supplementary properties validating combinational logic and protocol nuances.

## DUT overview
The DUT `NTT_CTRL` in PWM_INTT mode manages interactions between the NTT engine and the PWM/PWO memory interfaces during inverse NTT (INTT) workflows. PWM_INTT mode combines aspects of PWM memory access with INTT sequencing and has specific requirements for read/write ordering, buffer usage, and handshake behavior.

Primary signals exercised by the PWM_INTT-mode AIP include:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- `ntt_mode`: Operation mode selector — PWM_INTT-mode properties assume `ntt_mode == pwm_intt`.
- `ntt_enable`: Start signal for NTT operations.
- PWM/PWO interfaces: `pw_rden`, `pw_wren`, `po_pwm_a_rd_req`, `po_pwm_b_rd_req`, and associated data ports.
- Memory interfaces and signals: `mem_rd_addr`, `mem_wr_addr`, `mem_rd_en`, `mem_wr_en`, and `mem_wr_data`.
- Control/status outputs: `busy`, `done`, and intermediate buffer/pointer signals.
- Additional inputs: `shuffle_en`, `sampler_valid`, `accumulate`, randomization signals.

The AIP verifies correct sequencing of PWM reads/writes in INTT operations, ensuring data integrity across the permutation and accumulation steps unique to PWM_INTT.

## Assertion IP overview
The PWM_INTT-mode AIP binds properties to DUT signals (reset bound to `(!ntt_ctrl.reset_n || ntt_ctrl.zeroize)`) and is organized into FSM, protocol, memory, and combinational checks similar to other NTT-mode AIPs.

### FSM and Sequence Assertions
- Read and write FSM assertions validate transitions and legal state encodings for PWM_INTT workflows.
- Ensure proper coordination between PWM read phases and INTT round scheduling.
- Verify `busy`/`done` signaling aligns with completed INTT transactions.

### PWM/PWO and Memory Interface Assertions
- Validate `po_pwm_*_rd_req` generation, addresses, and read/write enables specific to PWM_INTT behavior.
- Check memory write data correctness when results are committed to memory during INTT sequences.
- Ensure no read/write races and correct address sequencing across PWM and main memory.

### Handshake and Flow Control Assertions
- Confirm valid-ready-like semantics for sampler and PWM interfaces.
- Ensure `po_pwm_b_rd_req` timing honors `shuffle_en` and `sampler_valid` semantics where applicable.
- Detect data-loss, ordering violations, and improper enable assertions.

### Helper Functions and Packages
- `fv_ntt_ctrl_pwm_intt_functions.sv` contains reusable helpers used by several properties.
- `fv_ntt_ctrl_pwm_intt_pkg.sv` provides shared parameterization and type definitions for the AIP.

### Additional/Combinational Properties
- Supplementary assertions in `fv_ntt_ctrl_pwm_intt_additional_properties.sv` check buffer pointers, twiddle address calculations, and combinational invariants.
- Coverage and liveness are guided by `model/ntt_ctrl_pwm_intt.luref`.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
