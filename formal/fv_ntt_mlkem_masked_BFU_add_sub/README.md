# ntt_mlkem_masked_add_sub
Date: 08.08.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory **<project_root>/formal/fv_ntt_mlkem_masked_BFU_add_sub**

- **fv_ntt_mlkem_masked_BFU_add_sub.sv** contains the assertion IP(AIP) for ntt_mlkem_masked_BFU_add_sub submodule

- **fv_ntt_mlkem_masked_BFU_add_sub_constraints.sv** contains the assumptions/constraints for ntt_mlkem_masked_BFU_add_sub submodule

- **fv_ntt_mlkem_masked_BFU_add_sub_top.sv** is the wrapper file for both.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | sub                        | input     | The signal indicating substraction operation                                      |
| 5    | u [1:0][23:0]              | input     | The operand1 input shares (u)                                                     |
| 6    | v [1:0][23:0]              | input     | The operand2 input shares (v)                                                     |
| 7    | rnd [3:0][13:0]            | input     | Randomized input for masking purpose                                              |
| 8    | rnd_24bit [23:0]           | input     | Randomized input for masking purpose (24-bit)                                     |
| 9    | res[1:0][23:0]             | output    | The result output shares                                                          |

The ntt_mlkem_masked_BFU_add_sub computes masked addition or substraction of two input shares (u0,u1) and (v0,v1) 

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares (res) are zero upon reset

- run_sub_a: End-to-End checks of the output during the substraction operation between input shares u and v (res[0]+res[1] == (u[0]+u[1]) - (v[0]+v[1]))

- run_add_a: End-to-End checks of the output during the addition operation between input shares u and v (res[0]+res[1] == (u[0]+u[1]) + (v[0]+v[1]))

## Reproduce results

The AIP has been tested and proven with Onespin & Jasper formal tool. 

To reproduce the results:
Load the design, AIP file, and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 