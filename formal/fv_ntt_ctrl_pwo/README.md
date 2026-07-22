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

# ntt_ctrl - pwo_mode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectories are part of the `formal/fv_ntt_ctrl_pwo` directory:

- `fv_ntt_ctrl_pwo_m.sv`: Main assertion IP for PWO-mode behavior and protocol checks
- `fv_ntt_ctrl_pwo_pkg.sv`: Package definitions, parameters, and shared types used by the AIP
- `fv_ntt_ctrl_pwo_functions.sv`: Helper functions used by assertions and checks
- `fv_ntt_ctrl_pwo_binding.sv`: Binding module that connects the assertions to DUT signals
- `fv_ntt_ctrl_pwo_constraints.sv`: Environment constraints that restrict input stimuli to valid PWO-mode protocol and scenarios
- `fv_ntt_ctrl_pwo_additional_properties.sv`: Supplementary properties validating combinational logic and protocol nuances
- model: Contains reference model and tool project files
  - `model/ntt_ctrl_pwo.h`: High-level abstracted model used by the formal flow
  - `model/ntt_ctrl_pwo.luref`: Liveness and coverage reference for PWO-mode assertions
  - `model/project.lutar`: Tool-specific project file for formal runs


## DUT Overview

The DUT `NTT_CTRL` in PWO (Point-Wise Operation) mode manages the NTT engine's memory interface for point-wise multiplication and output operations within the MLDSA pipeline. PWO mode handles direct memory read/write sequencing without the butterfly computation stages used in CT/GS modes.

Key interface signals:
- `clk`, `reset_n`, `zeroize`: Clock, active-low reset, and secure clear.
- `ntt_mode`: Mode selector (CT, GS, PWM, PWO, PWM_INTT).
- `ntt_enable`: Start signal for the NTT operation.
- `butterfly_ready`: Readiness signal from the butterfly computation unit.
- `buf0_valid`, `sampler_valid`, `accumulate`: Datapath control inputs.
- `ntt_mem_base_addr`: Base address inputs for source, destination, and interim memory.
- `bf_enable`, `opcode`, `mem_rd_en`, `mem_wr_en`: Datapath control outputs.
- `busy`, `done`: Status outputs.


## Assertion IP Overview

The Assertion IP validates FSM state transitions, memory address sequencing, and control signal correctness for PWO mode. Properties cover:

- Reset assertions verifying all registers and outputs initialize correctly.
- FSM transitions for read and write sub-FSMs (idle → stage → mem → stage cycle).
- Memory address generation and read/write enable sequencing.
- Additional combinational properties for opcode, buffer enables, and pointer arithmetic.
- Liveness: each FSM state is eventually left; the operation eventually completes.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
