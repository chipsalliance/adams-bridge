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

# sigdecode_h
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_sigdecode_h**

- **fv_sigdecode_h_states_m.sv**: Main assertion IP for sigdecode_h block
- **fv_sigdecode_h_states_pkg.sv**: Assertion IP package
- **fv_sigdecode_h_functions.sv**: Helper functions for the AIP
- **fv_sigdecode_h_states_binding.sv**: AIP binding file
- **fv_sigdecode_h_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model
  - `model/sigdecode_h.h`: High-level abstracted model
  - `model/sigdecode_h_states.luref`: LUBIS coverage and liveness reference


## DUT Overview

The DUT sigdecode_h has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                         |
| ---- | ---------------------      | --------- | ----------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                            |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                |
| 4    | encoded_h_i[7:0][82:0]     | input     | The 83 byte data input                                                              |
| 5    | sigdecode_h_enable         | input     | The module is enabled by the top hierarchy with this signal                         |
| 6    | dest_base_addr[13:0]       | input     | The base address of writing output to the memory                                    |
| 7    | mem_wr_req                 | output    | The memory write data request for decoded hints, consists of r/w mode and addr      |
| 8    | mem_wr_data[95:0]          | output    | The decoded hints, output data to be saved into memory                              |
| 9    | sigdecode_h_done           | output    | The output bit indicating sigdecode_h operation is done                             |
| 10   | sigdecode_h_error          | output    | The output bit indicating that an error occured during the operation                |

When the enable signal arrives, the input data arrives as well. The last 8 bytes of the input data are hintsums, so one hintsum per polynomial is processed each time. For the given polynomial, 4 bytes each time are read from the register API (the input data) and processed. The same throughput is kept for the data output, 4 coefficients per cycle. Each coefficient is 24 bits. The entire operation is done when all 8 polynomials are processed and the data is written to the memory, which takes at least 512 cycles - 64 writes per 8 polynomials.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** is binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. And another AIP signal start_port and start_write_fsm are triggered whenever the **sigdecode_h_enable** is high.

- read_reset_a: Checks that the registers are properly resetted and the read FSM is in idle state.

- read_rIDLE_to_rIDLE_a: If no enable signal arrives, the read FSM stays in idle state.

- read_rIDLE_to_rINIT_a: Once an enable arrives, the read FSM transitions to init state.

- read_rINIT_to_rIDLE_a: If an error is detected in the init state, it goes back idle state. The bitmap is updated based on rst_bitmap signal, that depends on write FSM.

- read_rINIT_to_rHINTSUM_a: If there's no error and write FSM is also in init state, the read FSM transitions to hintsum state, and the hintsum of current polynomial is read from the input data.

- read_rINIT_to_rINIT_a: If there's no error, but write FSM is not in init state, the read FSM stays in init.

- read_rHINTSUM_to_rEXEC_a: The read fsm always transitions from hintsum to exec state. curr_poly_map is reset to 0 and the rem_hintsum is updated.

- read_rEXEC_to_rIDLE_a: If an error is detected in the exec state or if reads for the last polynomial are done, the read FSM transitions to idle. curr_poly_map is set based on the rem_hintsum's value. The bitmap is updated based on rst_bitmap signal, that depends on write FSM. hint is reset to 0. Other register values are updated accordingly.

- read_rEXEC_to_rINIT_a: If there's no error and reads for the current, not the last, polynomial are done in the exec state, the FSM transitions to init state. curr_poly_map is set based on the rem_hintsum's value. hint is reset to 0. Other register values are updated accordingly.

- read_rEXEC_to_rEXEC_a: If there's no error and reading is not done in the exec state, it stays in exec state. curr_poly_map is set based on the rem_hintsum's value. Other register values are updated accordingly.


- write_reset_a: Checks that the registers are properly resetted, the write FSM state and write request are idle, error and write data ports are set to 0.

- write_wIDLE_to_wIDLE_a: If no enable signal arrives, the write FSM stays in idle state. For the done port, it should get read_state's current value, not past, as for the done signal to be asserted, both FSM must be in idle states. OR_remaining_encoded_h_i and hintsum_max_error_i are also updated based on current values, not past. Write request address is set to 0 and mode to idle. The write data is updated based on bitmap's values. Error port remains stable. 

- write_wIDLE_to_wINIT_a: Once an enable arrives, the write FSM transitions to init state. Done and error ports are set to 0. Write request is still idle and the address is 0. The write data is set based on bitmap's values.

- write_wINIT_to_wIDLE_a: If an error is detected in the init state, it goes back to idle state. Done port is set based on read FSM's state. Write data and error ports are updated accordingly. Memory write address remains stable and the request mode is set to idle.

- write_wINIT_to_wINIT_a: If there's no error, hint_rd_en_f is not set, and reads are not done or read FSM is not in exec state, the write FSM stays in init state. Done port is set to 0. Write data and error ports are updated accordingly. Memory write address remains stable and the request mode is set to idle.

- write_wINIT_to_wMEM_a: If there's no error, but either hint_rd_en_f is set or in exec state the reads are done, the write FSM transitions to mem state. Done port is set to 0. Write data and error ports are updated accordingly. Memory write address remains stable and the request mode is set to idle.

- write_wMEM_to_wIDLE_a: If an error is detected in the mem state or memory writes for the last polynomial are done, the write FSM transitions to idle state. Done port is set based on read FSM's state. Write data and error ports are updated accordingly. Memory write address is incremented and the request mode is set to write. 
Expected to fail, because of the case when the dest_base_addr is a big number and mem_wr_addr, which gets incremented 511 times, overflows. This case is not taken into account in the design, specifically in last_poly_last_addr_wr, so this signal does not get set, which results in mem_wr_addr being incremented on the transition to wIDLE state, instead of resetting to 0. But, this does not affect the primary output, as the enable signal will be set to idle with this wrong address.

- write_wMEM_to_wINIT_a: If there's no error and memory writes for the current, not the last, polynomial are done, the write FSM transitions to init state. Done port is set to 0. Write data and error ports are updated accordingly. Memory write address is incremented and the request mode is set to write.

- write_wMEM_to_wMEM_a: If there's no error and memory writes for current polynomial are not done, the write FSM stays in mem state. Done port is set to 0. Write data and error ports are updated accordingly. Memory write address is incremented and the request mode is set to write.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
