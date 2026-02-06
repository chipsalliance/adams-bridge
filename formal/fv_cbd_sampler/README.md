# CBD Sampler
Date: 26-09-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_cbd_sampler** for the module **cbd_sampler_ctrl**. 

The **formal/fv_cbd_sampler** contains the top level verification assertion IP(AIP) named as **fv_cbd_sampler_top.sv**, containing the properties. The constraints are written in **fv_cbd_sampler_constraints.sv**.

## DUT Overview

The DUT **cbd_sampler_ctrl** has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                               |
| 2    | rst_b             | input     | The reset signal is active low and resets the design                                   |
| 3    | zeroize           | input     | The design is reset when this signal is triggered.                                     |
| 4    | data_valid_i      | input     | Indicates valid input data                                                              |
| 5    | data_hold_o       | output    | Hold signal for input data                                                              |
| 6    | data_i            | input     | Input data for sampling                                                                 |
| 7    | data_valid_o      | output    | Indicates valid output data                                                             |
| 8    | data_o            | output    | Output sampled data                                                                     |

The design serves as a CBD sampler unit that computes the centered binomial distribution for ML-KEM, processing multiple samples per clock cycle.

## Assertion IP Overview
The Assertion IP signals are bound with the respective signals in the dut. The assertions checks the behavior of all outputs using standard assertions.

### fv_cbd_sampler_top.sv
- check_reset: Checks reset behavior when zeroize is asserted.
- check_if_the_result_is_correct: Verifies the correctness of the sampled output data.
- check_the_data_doesnt_change_if_data_valid_o_is_stable: Ensures output stability when input is stable.
- check_data_in_valid_implies_data_out_valid: Checks that output valid follows input valid.
- check_hold_is_always_zero: Asserts that hold output is always zero.

### fv_cbd_sampler_constraints.sv
Contains constraints to drive the inputs appropriately for formal verification.

## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load the AIP, the design and fv_cbd_sampler_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts.