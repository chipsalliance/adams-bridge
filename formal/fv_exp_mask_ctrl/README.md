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

# Expand Mask
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_exp_mask_ctrl**
- **fv_exp_mask_ctrl_m.sv**: The assertion IP (AIP) for exp_mask_ctrl block
- **fv_exp_mask_ctrl_pkg.sv**: The assertion IP (AIP) package file for exp_mask_ctrl block
- **fv_exp_mask_ctrl_binding.sv**: The assertion IP (AIP) binding file for exp_mask_ctrl block
- model: Folder contains the high level abstracted model (exp_mask_ctrl.h) and the Lubis app refinement file (exp_mask_ctrl.luref)



## DUT Overview

The DUT exp_mask_ctrl has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | rst_b                      | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | data_valid_i               | input     | The input signal indicating data validity                                         |
| 5    | data_i[3:0][19:0]          | input     | The 4*20-bit coefficient data input                                               |
| 6    | data_valid_o               | output    | The output signal indicating data validity                                        |
| 7    | data_o[3:0][23:0]          | output    | The 4*23-bit sampled data output to be saved to the memory                        |
| 8    | data_hold_o                | output    | The output indicating data hold (currently not used)                              |

Expand Mask is used in signing operation of Dilithium. The output of expand mask sampler is stored into memory and will be used as an input for NTT module. In every clock cycle, the block takes in  4 20-bit samples from the Keccak core and returns 4*23 coefficient calculated by the function 2^19-a%q.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality. There is no fsm in the block, only one COMPUTE state that continuously samples the data.

- reset_a: Checks that all the registers are resetted. 

- COMPUTE_to_COMPUTE_a: Checks the correctness of the computed data as well as the data validity.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
