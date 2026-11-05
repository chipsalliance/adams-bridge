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

# ntt_hybrid_butterfly_2x2

## Folder Structure
The following files are part of the main directory **formal/fv_ntt_hybrid_butterfly_2x2**

- **fv_ntt_hybrid_butterfly_2x2.sv** contains the assertion IP(AIP) for ntt_hybrid_butterfly_2x2 submodule

- **fv_ntt_hybrid_butterfly_2x2_constraints.sv** contains the assumptions/constraints for ntt_hybrid_butterfly_2x2 submodule

- **fv_ntt_hybrid_butterfly_2x2_top.sv** is the wrapper file for both.

- **fv_ntt_hybrid_butterfly_2x2.cpp** is the C++ reference model used for C2RTL/DPV equivalence checking.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                                                    |
| ---- | ---------------------      | --------- | ---------------------------------------------------------------------------------------------------------------|
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                                                       |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                                           |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                                           |
| 4    | mode                       | input     | The input for ntt mode selection (ct, gs, pwm, pwa, pws, pairwm)                                               |
| 5    | enable                     | input     | The input for enabling ntt                                                                                     |
| 6    | shuffle_en                 | input     | The input for enabling shuffling operation                                                                     |
| 7    | mlkem                      | input     | The input for enabling mlkem operation.                                                                        |
| 8    | uvw_i                      | input     | A struct input consists of two pairs of (opu_i, opv_i, opw_i) gs_butterfly input shares                        |
| 9    | pw_uvw_i                   | input     | A struct input consists of four pairs of (opu_i, opv_i, opw_i) input shares for pwo_mode                       |
| 10   | accumulate                 | input     | The input to indicate accumulate case                                                                          |
| 11   | mlkem_pairwm_zeta13_i      | input     | A struct input consists of two [MLKEM_REG_SIZE-1:0] for zeta input                                             |
| 12   | ntt_passthrough            | input     | The input for enabling ntt_passthrough in CT mode                                                              |
| 13   | intt_passthrough           | input     | The input for enabling intt_passthrough in GS mode                                                             |
| 14   | uv_o                       | output    | A struct output consists of two pairs of (u_o, v_o) gs_butterfly outputs                                       |
| 15   | pwo_uv_o                   | output    | A struct output consists of four signals (uv0, uv1, uv2, uv3) of pwm outputs                                   |
| 16   | ready_o                    | output    | A logic output indicating butterfly ready signal                                                               |

The ntt_hybrid_butterfly_2x2 consists of PWMs followed by two stages of BFUs. Final outputs are 23-bit values.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that all outputs (butterfly, pwm, ready signal) are zero upon reset

- run_CT_ntt_passthrough_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode with ntt_passthrough and mlkem enabled

- run_CT_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode

- run_CT_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mlkem mode

- run_GS_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mode

- run_GS_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mlkem mode

- run_GS_mlkem_intt_passthrough_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mlkem mode with intt_passthrough

- run_PWM_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM not accumulate mode

- run_PWMA_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM accumulate mode

- run_PWA_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA mode

- run_PWA_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA mlkem mode

- run_PWS_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS mode

- run_PWS_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS mlkem mode

- run_pairwm_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 in pairwm mode (with outputs of ntt_karatsuba & ntt_masked_pairwm blocks are cut)

- run_pairwm_accumulate_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 in pairwm accumulate mode (with outputs of ntt_karatsuba & ntt_masked_pairwm blocks are cut)

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
