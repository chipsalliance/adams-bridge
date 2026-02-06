# ntt_mlkem_masked_gs_butterfly
Date: 08.08.2025
Author: LUBIS EDA

## Folder Structure
The following files are part of the main directory **<project_root>/properties/fv_ntt_mlkem_masked_gs_butterfly**

- **fv_ntt_mlkem_masked_gs_butterfly.sv** contains the assertion IP(AIP) for ntt_mlkem_masked_gs_butterfly submodule

- **fv_ntt_mlkem_masked_gs_butterfly_constraints.sv** contains the assumptions/constraints for ntt_mlkem_masked_gs_butterfly submodule

- **fv_ntt_mlkem_masked_gs_butterfly_top.sv** is the wrapper file for both.


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | opu_i [1:0][23:0]          | input     | The coefficient input shares (u)                                                  |
| 5    | opv_i [1:0][23:0]          | input     | The coefficient input shares (v)                                                  |
| 6    | opw_i [1:0][23:0]          | input     | The ROM input shares (v)                                                          |
| 7    | rnd_i [4:0][13:0]          | input     | Randomized input for masking purpose                                              |
| 8    | u_o[1:0][23:0]             | output    | Output shares U : (opu_i + opv_i)                                                 |
| 9    | v_o[1:0][23:0]             | output    | Output shares V : (opu_i - opv_i) * (opw_i)                                       |

The ntt_mlkem_masked_gs_butterfly performs GS (INTT) mode of operation of the input shares opu_i, opv_i, opw_i

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- run_reset_a: Checks that output shares (u_o and v_o) are zero upon reset

- run_gs_butterfly_u_a: End-to-End checks of the output shares u_o (opu_i + opv_i) 

- run_gs_butterfly_v_a: End-to-End checks of the output shares v_o (opu_i - opv_i) * (opw_i) 

## Reproduce results

The AIP has been tested and proven with Onespin & Jasper formal tool. 

To reproduce the results:
Load the design, AIP file, and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 