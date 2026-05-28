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

# ntt_masked_BFU_mult
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_masked_BFU_mult**

- **fv_ntt_masked_BFU_mult_m.sv** contains the assertion IP(AIP) for ntt_masked_BFU_mult submodule

- **fv_ntt_masked_BFU_mult_constraints.sv** contains the assumptions/constraints for fv_ntt_masked_BFU_mult module

- **fv_ntt_masked_BFU_mult_functions.sv** contains the functions used in fv_ntt_masked_BFU_mult module

- **fv_ntt_masked_BFU_mult_pkg.sv** contains the variable declarations used in fv_ntt_masked_BFU_mult module

- **fv_ntt_masked_BFU_mult_binding.sv** contains the binding file between the AIP instance (fv_ntt_masked_BFU_mult) & DUT (ntt_masked_BFU_mult)

- **fv_ntt_masked_BFU_mult_top.sv** is the wrapper file for all the above.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | u [1:0][45:0]              | input     | The operand1 input shares (u)                                                     |
| 5    | v [1:0][45:0]              | input     | The operand2 input shares (v)                                                     |
| 6    | rnd [3:0][45:0]            | input     | Randomized input for masking purpose                                              |
| 8    | res[1:0][45:0]             | output    | The result output shares                                                          |

The ntt_masked_BFU_mult computes masked multiplication of two input shares (u0,u1) and (v0,v1) 

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares (res) are zero upon reset

- run_COMPUTE_to_COMPUTE_a: End-to-End checks of the output for multiplication operation between input shares u and v (res[0]+res[1] == (u[0]+u[1]) * (v[0]+v[1])) (expanded version)

- run_COMPUTE_to_COMPUTE_1_a: End-to-End checks of the output for multiplication operation between input shares u and v (res[0]+res[1] == (u[0]+u[1]) * (v[0]+v[1]))

- run_COMPUTE_to_COMPUTE_mult_two_share_a: Property to check the abr_masked_N_bit_mult_two_share submodule used in ntt_masked_BFU_mult (with truncation)

- run_COMPUTE_to_COMPUTE_mult_two_share_1_a: Property to check the abr_masked_N_bit_mult_two_share submodule used in ntt_masked_BFU_mult (without truncation)

- run_COMPUTE_to_COMPUTE_mult_redux46_a: Property to check ntt_masked_mult_redux46 submodule used in ntt_masked_BFU_mult

- run_COMPUTE_to_COMPUTE_b2a_a: Property to check abr_masked_B2Aconv submodule used in ntt_masked_BFU_mult

- run_COMPUTE_to_COMPUTE_a2b_a: Property to check abr_masked_A2Bconv submodule used in ntt_masked_BFU_mult

- run_COMPUTE_to_COMPUTE_masked_adder_11_a: Property to check abr_masked_N_bit_Boolean_adder submodule used in ntt_masked_mult_redux46

- run_COMPUTE_to_COMPUTE_masked_delay_a: Property to check abr_delay_masked_shares submodule used in ntt_masked_mult_redux46 

- run_COMPUTE_to_COMPUTE_add_sub_boolean_1_a: Property to check abr_masked_add_sub_mod_Boolean submodule used in ntt_masked_mult_redux46 (sub = 0)

- run_COMPUTE_to_COMPUTE_add_sub_boolean_2_a: Property to check abr_masked_add_sub_mod_Boolean submodule used in ntt_masked_mult_redux46 (sub = 1)

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
