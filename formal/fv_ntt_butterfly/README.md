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

# ntt_butterfly - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure

The following files are part of the main directory **formal/fv_ntt_butterfly**

- `fv_ntt_butterfly_m.sv`: Main assertion IP with mode transition and computation verification
- `fv_ntt_butterfly_pkg.sv`: Package definitions for NTT butterfly types and parameters
- `fv_ntt_butterfly_functions.sv`: Helper functions for NTT butterfly computations
- `fv_ntt_butterfly_binding.sv`: Binding of assertions to DUT signals
- `fv_ntt_butterfly_top.sv`: Top-level wrapper instantiating constraints and binding the AIP
- `fv_ntt_butterfly_constraints.sv`: Constraints for formal verification
- model: Contains reference model and FSM artifacts
  - `model/ntt_butterfly.dot`: FSM state diagram in DOT format
  - `model/ntt_butterfly.h`: C header file with reference model
  - `model/ntt_butterfly.luref`: LUBIS reference documentation

## DUT Overview

The DUT `NTT_Butterfly` is a configurable butterfly processing unit used in the Number Theoretic Transform (NTT) computation for the MLDSA algorithm. It performs modular arithmetic operations on pairs of operands and supports multiple transformation modes with pipelined architecture.

| S.No | Port              | Direction | Description                                                                  |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------- |
| 1    | clk               | input     | Clock signal for synchronous operation                                      |
| 2    | rst_n             | input     | Active-high reset signal                                                     |
| 3    | opu_i             | input     | First operand (u value) - 23-bit unsigned                                   |
| 4    | opv_i             | input     | Second operand (v value) - 23-bit unsigned                                  |
| 5    | opw_i             | input     | Third operand (w value) - 23-bit unsigned                                   |
| 6    | mode              | input     | Mode select (3-bit): CT(0), GS(1), PWA(3), PWS(4), PWM(2)                  |
| 7    | accumulate        | input     | Accumulate flag for PWM mode (1-bit)                                        |
| 8    | u_o               | output    | Output result for u - 23-bit unsigned                                       |
| 9    | v_o               | output    | Output result for v - 23-bit unsigned                                       |
| 10   | pwm_res_o         | output    | PWM mode result output - 23-bit unsigned                                    |
| 11   | u_reg             | internal  | Register holding u operand (stage 1)                                        |
| 12   | u_reg_d2          | internal  | Register holding u operand (stage 2)                                        |
| 13   | u_reg_d3          | internal  | Register holding u operand (stage 3)                                        |
| 14   | u_reg_d4          | internal  | Register holding u operand (stage 4)                                        |
| 15   | w_reg             | internal  | Register holding w operand (stage 1)                                        |
| 16   | w_reg_d2          | internal  | Register holding w operand (stage 2)                                        |
| 17   | w_reg_d3          | internal  | Register holding w operand (stage 3)                                        |
| 18   | w_reg_d4          | internal  | Register holding w operand (stage 4)                                        |
| 19   | add_res           | internal  | Addition result (stage 1)                                                   |
| 20   | add_res_d1        | internal  | Addition result (stage 2)                                                   |
| 21   | add_res_d2        | internal  | Addition result (stage 3)                                                   |
| 22   | mul_opa           | internal  | Multiplier operand A                                                        |
| 23   | mul_opb           | internal  | Multiplier operand B                                                        |

## FSM States

The NTT_Butterfly module implements a 6-state FSM:

- **INIT**: Initial state, ready to accept operands and mode selection
- **CT**: Cooley-Tukey butterfly mode (mode=0)
  - Standard NTT forward transform butterfly
  - 5-cycle pipeline
  - Multiplier inputs: mul_opa = opv_i, mul_opb = opw_i
  
- **GS**: Gentleman-Sande butterfly mode (mode=1)
  - NTT inverse transform butterfly
  - 5-cycle pipeline
  - Multiplier inputs: mul_opa = (u-v)/2, mul_opb = opw_i
  
- **PWA_PWS**: Pointwise arithmetic/subtraction mode (mode=3 or 4)
  - Fast path for pointwise operations
  - 1-cycle pipeline
  - Multiplier not used (mul_opa=0, mul_opb=0)
  
- **PWM_ACC**: Pointwise multiply with accumulation mode (mode=2, accumulate=1)
  - Multiplies operands with accumulation
  - 5-cycle pipeline
  - Multiplier inputs: mul_opa = opu_i, mul_opb = opv_i
  
- **PWM_NOT_ACC**: Pointwise multiply without accumulation mode (mode=2, accumulate=0)
  - Multiplies operands without accumulation
  - 4-cycle pipeline
  - Multiplier inputs: mul_opa = opu_i, mul_opb = opv_i

## Computation Functions

The verification module uses helper functions imported from `ntt_butterfly_functions`:

- `compute_u()`: Computes output u value based on mode and operands
- `compute_v()`: Computes output v value based on mode and operands
- `compute_pwm()`: Computes PWM mode result
- `compute_a_min_b()`: Computes (u-v) for GS mode division
- `div2()`: Divides value by 2 for GS mode normalization

## Assertion IP Overview

### Reset Assertions

- **run_reset_a**: On reset deassertion, FSM enters INIT state with all pipeline registers and outputs cleared to zero

### Mode Transition Assertions

#### CT Mode (mode=0)
- **run_INIT_to_CT_a**: 
  - Transitions from INIT to CT when mode=0
  - 5-cycle pipeline for operand staging (u_reg, w_reg progression through d2, d3, d4)
  - Multiplier inputs set to: mul_opa = opv_i, mul_opb = opw_i
  - Output results computed and available after 5 cycles: u_o, v_o, pwm_res_o

#### GS Mode (mode=1)
- **run_INIT_to_GS_a**:
  - Transitions from INIT to GS when mode≠2 and mode≠0 and mode≤2
  - 5-cycle pipeline for operand staging
  - Multiplier inputs: mul_opa = (u-v)/2 (computed and registered), mul_opb = opw_i
  - Output results computed and available after 5 cycles
  - Implements Gentleman-Sande transform with normalization division

#### PWA/PWS Mode (mode=3 or 4)
- **run_INIT_to_PWA_PWS_a**:
  - Transitions from INIT to PWA_PWS when mode>2
  - Fast path with 1-cycle latency
  - Multiplier disabled: mul_opa = 0, mul_opb = 0
  - Results immediately available: u_o, v_o, pwm_res_o
  - Direct pointwise arithmetic without multiplication

#### PWM Accumulate Mode (mode=2, accumulate=1)
- **run_INIT_to_PWM_ACC_a**:
  - Transitions from INIT to PWM_ACC when mode=2 and accumulate≠0
  - 5-cycle pipeline for operand staging
  - Multiplier inputs: mul_opa = opu_i, mul_opb = opv_i
  - Output results computed and available after 5 cycles
  - Supports accumulation in PWM computation

#### PWM Non-Accumulate Mode (mode=2, accumulate=0)
- **run_INIT_to_PWM_NOT_ACC_a**:
  - Transitions from INIT to PWM_NOT_ACC when mode=2 and accumulate=0
  - 4-cycle pipeline (one cycle shorter than accumulate mode)
  - Multiplier inputs: mul_opa = opu_i, mul_opb = opv_i
  - Output results available after 4 cycles
  - u_reg_d4 and w_reg_d4 still valid at output stage

## Pipeline Architecture

The module implements a multi-stage pipelined architecture:

- **Stage 1**: Input operands latched into u_reg, w_reg; add_res computed
- **Stage 2**: u_reg_d2, w_reg_d2, add_res_d1 available
- **Stage 3**: u_reg_d3, w_reg_d3, add_res_d2 available (multiplier setup occurs here)
- **Stage 4**: u_reg_d4, w_reg_d4 available; multiplication results ready
- **Stage 5**: Final output results u_o, v_o, pwm_res_o (only for CT/GS/PWM modes)

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
