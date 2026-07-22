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

# ntt_masked_gs_butterfly
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_masked_gs_butterfly**

- **fv_ntt_masked_gs_butterfly_m.sv** contains the assertion IP(AIP) for ntt_masked_gs_butterfly submodule

- **fv_ntt_masked_gs_butterfly_constraints.sv** contains the assumptions/constraints for fv_ntt_masked_gs_butterfly module

- **fv_ntt_masked_gs_butterfly_functions.sv** contains the functions used in fv_ntt_masked_gs_butterfly module

- **fv_ntt_masked_gs_butterfly_pkg.sv** contains the variable declarations used in fv_ntt_masked_gs_butterfly module

- **fv_ntt_masked_gs_butterfly_binding.sv** contains the binding file between the AIP instance (fv_ntt_masked_gs_butterfly) & DUT (ntt_masked_gs_butterfly)

- **fv_ntt_masked_gs_butterfly_top.sv** is the wrapper file for all the above.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | opu_i [1:0][45:0]          | input     | The coefficient input shares (u)                                                  |
| 5    | opv_i [1:0][45:0]          | input     | The coefficient input shares (v)                                                  |
| 6    | opw_i [1:0][45:0]          | input     | The ROM input shares (v)                                                          |
| 7    | rnd_i [4:0][45:0]          | input     | Randomized input for masking purpose                                              |
| 8    | u_o[1:0][45:0]             | output    | Output shares U : (opu_i + opv_i)                                                 |
| 9    | v_o[1:0][45:0]             | output    | Output shares V : (opu_i - opv_i) * (opw_i)                                       |
| 10   | mode                       | input     | The input for pwm mode selection                                                  |
| 11   | accumulate                 | input     | The input to indicate accumulate case                                             |

The ntt_masked_gs_butterfly performs GS masked mode of operation of the input shares opu_i, opv_i, opw_i

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares (u_o and v_o) are zero upon reset

- run_INIT_to_NON_PWM_a: Property to check GS butterfly output when mode is not PWM

- run_INIT_to_PWM_a: Property to check GS butterfly output when mode is PWM but not ACC

- run_INIT_to_PWMA_a: Property to check GS butterfly output when mode is PWM and ACC

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
