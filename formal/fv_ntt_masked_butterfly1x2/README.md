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

# ntt_masked_butterfly1x2
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_masked_butterfly1x2**

- **fv_ntt_masked_butterfly1x2_m.sv** contains the assertion IP(AIP) for ntt_masked_butterfly1x2 submodule

- **fv_ntt_masked_butterfly1x2_constraints.sv** contains the assumptions/constraints for fv_ntt_masked_butterfly1x2 module

- **fv_ntt_masked_butterfly1x2_functions.sv** contains the functions used in fv_ntt_masked_butterfly1x2 module

- **fv_ntt_masked_butterfly1x2_pkg.sv** contains the variable declarations used in fv_ntt_masked_butterfly1x2 module

- **fv_ntt_masked_butterfly1x2_binding.sv** contains the binding file between the AIP instance (fv_ntt_masked_butterfly1x2) & DUT (ntt_masked_butterfly1x2)

- **fv_ntt_masked_butterfly1x2_top.sv** is the wrapper file for all the above.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                                    |
| ---- | ---------------------      | --------- | -----------------------------------------------------------------------------------------------|
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                                       |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                           |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                           |
| 4    | uvw_i                      | input     | A struct input consists of two pairs of (opu_i, opv_i, opw_i) gs_butterfly input shares        |
| 5    | rnd_i [4:0][23:0]          | input     | Randomized input for masking purpose                                                           |
| 6    | mode                       | input     | The input for pwm mode selection                                                               |
| 7    | accumulate                 | input     | The input to indicate accumulate case                                                          |
| 8    | uv_o                       | output    | A struct output consists of two pairs of (u_o, v_o) gs_butterfly output shares                 |
| 9    | bf_pwm_uv_o                | output    | A struct output consists of 4 pwm output shares                                                |

The ntt_masked_butterfly1x2 performs the following:

1. Compute 1st stage of masked INTT operation using mlkem_masked_gs_butterfly module
2. Combines output shares
3. Perform div2 on the combine outputs

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares (u_o and v_o) are zero upon reset

- run_COMPUTE_to_COMPUTE_CUT_a: Perform the check on the primary outputs u_o and v_o after cutting the output signals (v11_int,u11_int,u10_int,v10_int) of ntt_masked_gs_butterfly instances.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
