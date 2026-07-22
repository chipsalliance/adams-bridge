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

# skencode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_skencode**

- **fv_skencode_m.sv**: Main assertion IP containing the FSM properties
- **fv_skencode_pkg.sv**: Package definitions and shared types
- **fv_skencode_functions.sv**: Helper functions for the AIP
- **fv_skencode_binding.sv**: AIP binding file
- **fv_skencode_aip.sv**: Additional in-place assertions
- **fv_skencode_constraints.sv**: Constraints for formal verification
- **fv_skencode.dot**: FSM diagram
- model: Contains the high level abstracted model
  - `model/skencode.h`: High-level abstracted model
  - `model/skencode.luref`: LUBIS coverage and liveness reference


## DUT Overview

The DUT skencode has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                                   |
| 2    | reset_n           | input     | The reset signal is active low and resets the core                                         |
| 3    | zeroize           | input     | The core is reseted when this signal is triggered.                                         |
| 4    | skencode_enable   | input     | The core is initialised with respective state transitions and starts reading inputs.       |
| 5    | dest_base_addr[14:0] | input     | The destination base address for the encoded output.                                   | 
| 6    | src_base_addr[14:0] | input     | The source base address for the input polynomials.                                     |
| 7    | mem_a_rd_data[3:0][23:0] | input     | The 4-element array of 24 bit input polynomials.                                   |
| 8    | mem_b_rd_data[3:0][23:0] | input     | Another 4-element array of 24 bit input polynomials.                               |
| 9    | keymem_a_wr_req | output    | The write request, specific type that includes modes of request and address.        |
| 10   | mem_a_rd_req       | output    | The read request, specific type that includes modes of requests and address.     |
| 11   | mem_b_rd_req       | output    | Another read request, specific type that includes modes of requests and address.  |
| 12   | keymem_a_wr_data[31:0]       | output    | The encoded output data. |
| 13   | skencode_error      | output    | The error flag, in case an input value is out of the specified range. |
| 14   | skencode_done       | output    | The done flag, indicating, that all inputs have been encoded. |

When the enable signal arrives, the design starts reading eight 24 bit inputs at once and encoding each 24 bit element into a 3 bit value. These values are concatenated into 24 bit-wide strings and stored in a buffer. The output is set to 32 bit, extracting the encoded and buffered values. While reading happens each clock cycle, the output is set only for 3 clock cycles and 1 clock cycle being idle, to counterbalance the difference between 24 bit produced data, and 32 bit outputs.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** in binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. And another AIP signal start_port_valid is triggered whenever the skencode_enable is high.
In order to simplify understanding, the names of the assertions are a combination of states from the DUT, following the scheme: **main_state___write_state**

- reset_a: Checks that all the registers are resetted and the state and read/write requests are idle.

- CONSUME_LAST___STALL_to_DONE___GET_LAST_a: Checks if the transition from CONSUME_LAST to DONE is made, the second to last output is written and no data is read anymore.

- CONSUME___WRITE_to_CONSUME_LAST___STALL_a: Checks if the transition from CONSUME to CONSUME_LAST is made, the third to last output is written and no data is read anymore.

- DONE___GET_LAST_to_IDLE_a: Checks if the transition from DONE to IDLE is made and the last output is written.

- IDLE_to_READ_and_ENC_a: Checks if the transition from IDLE to READ_and_ENC is made and first data is read.

- READ_ENC_and_CONSUME___IDLE_to_READ_ENC_and_CONSUME___WAIT_BUFFER_a: Checks if the first transition of write states is made, from IDLE to WAIT_BUFFER, setting the first (incomplete) output and perform third reading.

- *READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___WAIT_BUFFER_a: Checks the potential situation, where the design stays in wait_buffer state and doesn't proceed to write. This assertion fails, as it is impossible.*

- READ_ENC_and_CONSUME___WAIT_BUFFER_to_READ_ENC_and_CONSUME___looped_a: Checks the loop entry, when in state READ_ENC_and_CONSUME and transition from WAIT_BUFFER to WRITE. Fourth reading is performed.

- READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_a: Checks the exit condition for the loop, when the consumer_selector is less than 2 and num_api_operands reaches 358.

- *impossible_READ_ENC_and_CONSUME___looped_to_CONSUME___WRITE_1_a: Checks the impossible exit condition for the loop, when consumer_selector == 2 and num_api_operands == 358.*

- READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_a: Checks the transitions between write states (WRITE to WRITE & WRITE to STALL) during READ_ENC_and_CONSUME, where the output is set to write mode.

- READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_1_a: Checks the transitions between write states (STALL to WAIT_BUFFER) during READ_ENC_and_CONSUME, where the output is set to idle mode.

- READ_ENC_and_CONSUME___looped_to_READ_ENC_and_CONSUME___looped_2_a: Checks the transitions between write states (WAIT_BUFFER to WRITE) during READ_ENC_and_CONSUME, where the output is set to write mode.

- READ_and_ENC_to_READ_ENC_and_CONSUME___IDLE_a: Checks the transition from the first read to second read request. No output is set.

- IDLE_wait_a: Checks if there isn't skencode_enable signal triggered in IDLE state then the state stays in IDLE and holds the past values.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
