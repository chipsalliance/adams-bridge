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

# ntt_masked_pwm
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_masked_pwm**

- **fv_ntt_masked_pwm_m.sv** contains the assertion IP(AIP) for ntt_masked_pwm submodule

- **fv_ntt_masked_pwm_constraints.sv** contains the assumptions/constraints for fv_ntt_masked_pwm module

- **fv_ntt_masked_pwm_functions.sv** contains the functions used in fv_ntt_masked_pwm module

- **fv_ntt_masked_pwm_pkg.sv** contains the variable declarations used in fv_ntt_masked_pwm module

- **fv_ntt_masked_pwm_binding.sv** contains the binding file between the AIP instance (fv_ntt_masked_pwm) & DUT (ntt_masked_pwm)

- **fv_ntt_masked_pwm_top.sv** is the wrapper file for all the above.


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
| 7    | accumulate                 | input     | The input to indicate accumulate case                                             |
| 8    | res[1:0][45:0]             | output    | The result output shares                                                          |

The ntt_masked_pwm performs masked pwm operation with or without accumulate on input shares.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares are zero upon reset

- run_INIT_to_PWM_a: Property to check the output of ntt_masked_pwm (not accumulate mode)

- run_INIT_to_PWMA_a: Property to check the output of ntt_masked_pwm (accumulate mode)

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
