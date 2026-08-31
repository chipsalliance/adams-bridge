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

# rej_bounded
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_rej_bounded**

- **fv_rej_bounded_ctrl_m.sv**: Assertion IP (AIP) for the rej_bounded_ctrl block
- **fv_rej_bounded_ctrl_pkg.sv**: Assertion IP package
- **fv_rej_bounded_ctrl_functions.sv**: Helper functions for the AIP
- **fv_rej_bounded_ctrl_binding.sv**: AIP binding file
- **fv_rej_bounded_ctrl_aip.sv**: Additional in-place assertions
- **fv_rej_bounded_ctrl_scoreboard.sv**: Scoreboard for FIFO data integrity and ordering checks
- **fv_rej_bounded_ctrl_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model


## DUT Overview

The DUT rej_bounded_ctrl has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                                   |
| 2    | rst_b             | input     | The reset signal is active low and resets the core                                         |
| 3    | zeroize           | input     | The core is reseted when this signal is triggered.                                         |
| 4    | data_valid_i      | input     | Control signal, that indicates that the input data is valid and is rejected accordingly.   |
| 5    | data_i            | input     | Input data to the design, array of 8 x 4-bit values.                                       | 
| 6    | data_hold_o       | output    | Control signal, that stops the previous connected PISO buffer from popping data.           |
| 7    | data_valid_o      | output    | Control signal, that enables the subsequent multiplier to process the designs output.      |
| 8    | data_o            | output    | Output data from the design, array of 4 x 24-bit values.                                   |

The design takes eight values in each CC which range from 0 to 15 and rejectes value 15. It performs computations on the remaining values such that each value results in 24-bit ranging from -eta to 2. The design outputs four 24-bit values in each CC to a multiplier.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** in binded with the DUT (rst_b && !zeroize), which ensures the reset functionality. As the design has no states but is combinational, the properties check for different scenarios based on the state of the fifo, as it determines, if there are enough values to forward or the design should wait. The output is always computed, the only difference is in the control signals.

- run_reset_a: Checks that all the control signals are set correctly and the output is set to [2, 2, 2, 2] (due to computation).

- run_buffer_full_state_to_buffer_full_state_a: Checks that the output is correctly computed and the design asserts the data_hold_o signal to stop new inputs and data_valid_o signal to empty the fifo and read from it. This state is reached, when the buffer holds more than 8 valid values.

- run_no_valid_data_state_to_no_valid_data_state_a: Checks that the output is correctly computed and the design deasserts the data_hold_o signal to receive new inputs and deasserts data_valid_o signal to fill the fifo and not read from it. This state is reached, when the buffer holds less than 4 valid values.

- run_regular_state_to_regular_state_a: Checks that the output is correctly computed and the design deasserts the data_hold_o signal to receive new inputs and asserts data_valid_o signal to empty the fifo and read from it. This state is reached, when the buffer holds between 4 and 8 valid values.

- run_buffer_full_state_eventually_left_a: Checks if the design leaves the state where the buffer is full. This situation is possible, as through the hold and valid signals, the buffer is read while no new values are written.

- run_regular_state_eventually_left_a: Checks if the design leaves from the regular state (4 to 8 buffer entries). This can never happen, as theoretically the input can be composed of values that make the buffer stay in the range of 4 to 8 valid entries.

- run_no_valid_data_state_eventually_left_p: Checks if the design leaves from the no_valid_data state (less than 4 buffer entries). This can never happen, as theoretically the input can be composed of only invalid values that make the buffer stay empty of only have less than 4 valid entries.

## Additional Assertion IP

- data_ordering_and_integrity, data_ordering_and_integrity_liveness, L0_only_pop_after_push, L1_depth_is_sufficient, L2_data_not_in_then_never_at_output and L3_tracking_counter_not_zero_if_data_in are assertions from the LUBIS scoreboard AIP in combination with the LUBIS counter AIP. These assertions have been used to verfiy the FIFO buffer used in the design. The scoreboard was used to track, whether items, that are pushed to it, will eventually be popped from it. Therefore, verfiying that no data is lost and the correctness of the FIFO holds. The counter was used to count the amount of valid data, that are stored in the FIFO, to replicate the conditions of pops and pushed from/to the FIFO.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
