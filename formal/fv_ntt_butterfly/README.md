# ntt_butterfly
Date: 28.10.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_butterfly**

- **fv_ntt_butterfly.sv** contains the assertion IP(AIP) for ntt_butterfly submodule

- **fv_ntt_butterfly_constraints.sv** contains the assumptions/constraints for fv_ntt_butterfly module

- **fv_ntt_butterfly_functions.sv** contains the functions used in fv_ntt_butterfly module

- **fv_ntt_butterfly_pkg.sv** contains the variable declarations used in fv_ntt_butterfly module

- **fv_ntt_butterfly_binding.sv** contains the binding file between the AIP instance (fv_ntt_butterfly) & DUT (ntt_butterfly)

- **fv_ntt_butterfly_top.sv** is the wrapper file for all the above.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | opu_i [23:0]               | input     | The coefficient input (u)                                                         |
| 5    | opv_i [23:0]               | input     | The coefficient input (v)                                                         |
| 6    | opw_i [23:0]               | input     | The ROM input (v)                                                                 |
| 7    | pwm_res_o [23:0]           | output    | Output butterfly pwm                                                              |
| 8    | u_o [23:0]                 | output    | Output butterfly U                                                                |
| 9    | v_o[23:0]                  | output    | Output butterfly V                                                                |

The ntt_butterfly module consists of butterfly unit operations (modular). This unit operates in 5 modes - CT, GS, PWM, PWA, PWS. Inputs u and v are fetched from the memory, w values come from ROM containing required twiddle factors. PWM mode performs point-wise multiplication and accumulation

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that all outputs are zero upon reset

- run_INIT_to_CT_a: Assertion to check all outputs during CT mode

- run_INIT_to_GS_a: Assertion to check all outputs during GS mode

- run_INIT_to_PWA_PWS_a: Assertion to check all outputs during PWA/PWS mode

- run_INIT_to_PWM_ACC_a: Assertion to check all outputs during PWM accumulate mode

- run_INIT_to_PWM_NOT_ACC_a: Assertion to check all outputs during PWM non-accumulate mode

## Reproduce results

The AIP has been tested and proven with Onespin & Jasper formal tool. 

To reproduce the results, load the tcl script in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 