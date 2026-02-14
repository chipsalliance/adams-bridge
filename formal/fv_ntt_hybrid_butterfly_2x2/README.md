# ntt_masked_hybrid_butterfly_2x2
Date: 08.08.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_hybrid_butterfly_2x2**

- **fv_ntt_hybrid_butterfly_2x2.sv** contains the assertion IP(AIP) for ntt_hybrid_butterfly_2x2 submodule

- **fv_ntt_hybrid_butterfly_2x2_constraints.sv** contains the assumptions/constraints for ntt_hybrid_butterfly_2x2 submodule

- **fv_ntt_hybrid_butterfly_2x2_top.sv** is the wrapper file for both.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                                                    |
| ---- | ---------------------      | --------- | ---------------------------------------------------------------------------------------------------------------|
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                                                       |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                                           |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                                           |
| 4    | mode                       | input     | The input for ntt mode selection (ct, gs, pwm, pwa, pws, pairwm)                                               |
| 5    | enable                     | input     | The input for enabling ntt                                                                                     |
| 6    | masking_en                 | input     | The input for enabling masked operation                                                                        |
| 7    | shuffle_en                 | input     | The input for enabling shuffling operation                                                                     |
| 8    | mlkem                      | input     | The input for enabling mlkem operation.                                                                        |
| 9    | uvw_i                      | input     | A struct input consists of two pairs of (opu_i, opv_i, opw_i) gs_butterfly input shares                        |
| 10   | pw_uvw_i                   | input     | A struct input consists of four pairs of (opu_i, opv_i, opw_i) input shares for pwo_mode                       |
| 11   | pwm_shares_uvw_i           | input     | A struct input consists of four pairs of (opu_i, opv_i, opw_i) input shares for masked PWM/Pairwm inputs       |
| 12   | rnd_i [4:0][45:0]          | input     | Randomized input for masking purpose                                                                           |
| 13   | accumulate                 | input     | The input to indicate accumulate case                                                                          |
| 14   | bf_shares_uvw_i            | input     | A struct input consists of eight [1:0][MASKED_WIDTH-1:0] input signals for MLDSA masked INTT                   |
| 15   |  mlkem_pairwm_zeta13_i     | input     | A struct input consists of two [MLKEM_REG_SIZE-1:0] for zeta input                                             |
| 16   | mlkem_shares_pairwm_zeta13_i| input    | A struct input consists of two [1:0][MLKEM_MASKED_WIDTH-1:0] for mlkem masked zeta input shares                |
| 17   | ntt_passthrough            | input     | The input for enabling ntt_passthrough in CT mode                                                              |
| 18   | intt_passthrough           | input     | The input for enabling intt_passthrough in GS mode                                                             |
| 19   | uv_o                       | output    | A struct output consists of two pairs of (u_o, v_o) gs_butterfly outputs                                       |
| 20   | pwo_uv_o                   | output    | A struct output consists of four signals (uv0, uv1, uv2, uv3) of pwm outputs                                   |
| 21   | pwm_shares_uvo             | output    | A struct output consists of four signals (uv0, uv1, uv2, uv3) of pwm output shares                             |
| 22   | ready_o                    | output    | A logic output indicating butterfly ready signal                                                               |

The ntt_hybrid_butterfly_2x2 consists of masked PWMs, followed by 1st stage of masked and unmasked BFUs, followed by unmasked BFUs. In case of masking_en, PWMs are triggered and masked branch is taken for computing 1st stage outputs. In case of unmasked operation, both branches are enabled but unmasked outputs are passed to next stage. Final outputs are 23-bit values

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that all outputs (butterfly, pwm, ready signal) are zero upon reset

- run_CT_ntt_passthrough_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode with ntt_passthrough and mlkem enabled

- run_CT_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mode

- run_CT_unmasked_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in CT mlkem mode

- run_GS_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS unmasked mode

- run_GS_unmasked_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mlkem unmasked mode

- run_GS_mlkem_intt_passthrough_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS mode mlkem with intt_passthrough

- run_GS_masked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mode (with outputs of ntt_mlkem_masked_bfu1x2 cut)

- run_GS_masked_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mlkem mode (with outputs of ntt_mlkem_masked_bfu1x2 cut)

- run_GS_masked_mlkem_intt_passthrough_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in GS masked mlkem & intt_passthrough mode (with outputs of ntt_mlkem_masked_bfu1x2 cut)

- run_PWM_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM unmasked not accumulate mode

- run_PWMA_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM unmasked accumulate mode

- run_PWM_masked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM masked mode

- run_PWMA_masked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWM masked accumulate mode

- run_PWA_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA unmasked mode

- run_PWA_unmasked_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWA unmasked mlkem mode

- run_PWS_unmasked_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS unmasked mode

- run_PWS_unmasked_mlkem_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 module in PWS unmasked mlkem mode

- run_pairwm_a: Assertion to check the outputs of ntt_hybrid_butterfly_2x2 in pairwm mode (with outputs of ntt_karatsuba & ntt_masked_pairwm blocks are cut)

- run_pairwm_accumulate_a: Assertion to check the ready output of ntt_hybrid_butterfly_2x2 in pairwm mode accumulate mode 

## Reproduce results

The AIP has been tested and proven with Onespin & Jasper formal tool. 

To reproduce the results:
Load the design, AIP file, and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 