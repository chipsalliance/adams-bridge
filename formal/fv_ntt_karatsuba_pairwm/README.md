# ntt_karatsuba_pairwm
Date: 08-08-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **properties**. Under this directory, we have a directory named **fv_ntt_karatsuba_pairwm** 

The **properties/fv_ntt_karatsuba_pairwm**  contains the top level verification assertion IP(AIP) named as **fv_ntt_karatsuba_pairwm_top.sv** where the properties are written, and the constraints are written in **fv_ntt_karatsuba_pairwm_constraints.sv**. 


## DUT Overview

The DUT ntt_karatsuba_pairwm has the primary inputs and primary outputs as shown below.

| S.No | Port                | Direction | Description                                                                            |
| ---- | -----------------   | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk                 | input     | The positive edge of the clk is used for all the signals                               |
| 2    | rst_n               | input     | The reset signal is active low and resets the core                                     |
| 3    | zeroize             | input     | The core is reseted when this signal is triggered.                                     |
| 4    | accumulate          | input     | The input signal which indicates an accumulate feature                                 |
| 5    | pwo_uvw_i           | input     | The input struct which holds the coefficients for the karatsuba pairwise multiplication|
| 6    | pwo_z_i             | input     | The zeta input needed for the karatsuba pairwise multiplication                        |
| 7    | pwo_uv_o            | output    | The output result of the karatsuba pairwise multiplication                             |


The design performs a Karatsuba technique for an optimized implementation of pairwise multiplication. It also supports accumulation as an additional input.


## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut. There assertions inside **fv_ntt_karatsuba_pairwm_top.sv** perform end-to-end checks for the ntt_karatsuba_pairwm module.

### fv_ntt_karatsuba_pairwm_top.sv

- assert_ntt_karatsuba_pwm_uv0_o_no_accumulate: Checks that the output "pwo_uv_o.uv0_o" is calculated properly according to the c2i karatsuba pairwm equation, in the case of the accumulate feature being disabled. The assertion is performed end-to-end after the latency of MLKEM_UNMASKED_PAIRWM_LATENCY.

- assert_ntt_karatsuba_pwm_uv1_o_no_accumulate: Checks that the output "pwo_uv_o.uv1_o" is calculated properly according to the c2i+1 karatsuba pairwm equation, in the case of the accumulate feature being disabled. The assertion is performed end-to-end after the latency of MLKEM_UNMASKED_PAIRWM_LATENCY.

- assert_ntt_karatsuba_pwm_uv0_o_accumulate: Checks that the output "pwo_uv_o.uv0_o" is calculated properly according to the c2i karatsuba pairwm equation, in the case of the accumulate feature being enabled. The assertion is performed end-to-end after the latency of MLKEM_UNMASKED_PAIRWM_ACC_LATENCY.

- assert_ntt_karatsuba_pwm_uv1_o_accumulate: Checks that the output "pwo_uv_o.uv1_o" is calculated properly according to the c2i+1 karatsuba pairwm equation, in the case of the accumulate feature being enabled. The assertion is performed end-to-end after the latency of MLKEM_UNMASKED_PAIRWM_ACC_LATENCY.

- assert_ntt_karatsuba_pwm_reset: Checks that the output "pwo_uv_o" is reset properly.


## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load the AIP, the design and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 
