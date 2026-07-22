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

# power2round_top
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_power2round**

- **fv_power2round_top_m.sv**: Assertion IP (AIP) for the power2round block
- **fv_power2round_top_pkg.sv**: Assertion IP package
- **fv_power2round_top_functions.sv**: Helper functions for the AIP
- **fv_power2round_top_binding.sv**: AIP binding file
- **fv_power2round_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model and reference files
  - `model/power2round_top_pk.h`: High level abstracted model
  - `model/power2round_top.luref`: LUBIS reference documentation


## DUT Overview

The DUT power2round_top has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                              |
| 4    | enable                     | input     | The module is enabled by the top hierarchy with this signal                       |
| 5    | src_base_addr[13:0]        | input     | The base address of reading the coefficient data from the memory                  |
| 6    | dest_base_addr[13:0]       | input     | The base address of writing output (r0) to the memory                             |
| 7    | mem_a_rd_req               | output    | The memory read data request, consists of r/w mode and addr                       |
| 8    | mem_b_rd_req               | output    | Another memory read data request, consists of r/w mode and addr                   |
| 9    | mem_rd_data_a[95:0]        | input     | The four 24-bit coefficients data input                                           |
| 10   | mem_rd_data_b[95:0]        | input     | Another four 24-bit coefficients data input                                       |
| 11   | skmem_a_wr_req             | output    | The memory write data request for r0, consists of r/w mode and addr               |
| 12   | skmem_b_wr_req             | output    | Another memory write data request for r0, consists of r/w mode and addr           |
| 13   | skmem_wr_data_a[31:0]      | output    | The encoded output data r0 to be saved into memory                                |
| 14   | skmem_wr_data_b[31:0]      | output    | Another encoded output data r0 to be saved into memory                            |
| 15   | pk_t1_wren                 | output    | The enable signal of the output data r1                                           |
| 16   | pk_t1_wrdata[7:0][9:0]     | output    | The output data r1 to be saved into memory                                        |
| 17   | pk_t1_wr_addr[7:0]         | output    | The address to store the output data r1                                           |
| 18   | done                       | output    | The output bit indicating power2round operation is done/idle                      |

When the enable signal arrives, the design starts reading two 96 bit inputs at once and splits this data into two parts: r0 and r1. The value of r0 is processed using skEncode, then goes through the abr_sample_buffer, and then placed in the API register. The buffer takes 104 bits at once and returns 64 bits, which are the primary outputs of the module (skmem_wr_data_a/b). Meanwhile, r1 is be processed with power2round_core.

<!-- ![alt text](power2round.png) -->

After this, the output of skEncode goes through the buffer.


## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** in binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. And another AIP signal start_port_valid is triggered whenever the skencode_enable is high.
In order to simplify understanding, the names of the assertions are a combination of states from the DUT, following the scheme: **main_state___write_state**

- reset_a: Checks that all the registers are resetted and the state and read/write requests are idle.

- IDLE_wait_a: Checks if there isn't **enable** signal triggered in IDLE state then the state stays in IDLE and holds the past values. The consequent part was manually changed to fix the r0_packed_reg part, and add checks for the requests.

- IDLE_to_REQ_1ST_DATA_a: If state is in idle and **enable** signal is asserted, it sends the first read request to the memory. The memory request outputs are updated accordingly.

- REQ_1ST_DATA_to_REQ_2ND_DATA_a: After the first read request is sent, the second read request is sent in the following clock cycle. The memory request outputs are updated accordingly. 

- REQ_2ND_DATA_to_REQ_3RD_DATA_a: After the second read request is sent, the third read request is sent in the following clock cycle. The memory request outputs are updated accordingly. 

- REQ_3RD_DATA_to_LOOP_a: After the third read request is sent, it enters the LOOP state where both data read and data write occur. The memory request outputs are updated accordingly. pk data is computed and ready, so the **pk_t1_wren**, **pk_t1_wrdata**, and **pk_t1_wr_addr** are set accordingly.

- LOOP_to_LOOP_a: The LOOP iterates to read input and write outputs until the second to last read request is sent. The memory request outputs are updated accordingly. It loops based on the condition if buffer contains 12-16 (including) valid entries of data, which means the buffer will become full in the next iteration of r/w. All the data outputs will have the computed value of the subsequent data reads.

- LOOP_to_LOOP_1_a: Same as above, but the condition is if buffer contains 17 or more valid entries of data, which means the buffer is currently full.

- LOOP_to_LOOP_2_a: Same as above, but the condition is if buffer contains 0-11 (including) valid entries of data, which means the buffer is currently not full.

- LOOP_to_LAST_READ_a: Not a valid assertion as it presents unrealistics condition in the assumption part. It is automatically generated by the LUBIS app builder.

- LOOP_to_LAST_READ_1_a: The last read request is sent. Write requests and data are set and computed accordingly.

- LOOP_to_LAST_READ_2_a: Not a valid assertion as it presents unrealistics condition in the assumption part. It is automatically generated by the LUBIS app builder.

- LAST_READ_to_ONLY_WRITE1_a: Read request is idle now. Write requests and data are set and computed accordingly.

- ONLY_WRITE1_to_ONLY_WRITE2_a: Read request is idle. Write requests and data are set and computed accordingly. The last pk data is computed, but the buffer is full, so the enable signal is not set.

- ONLY_WRITE2_to_ONLY_WRITE3_a: Read request is still idle and address is reset to the source address. Write requests and data are set and computed accordingly. The last pk data is sent.

- ONLY_WRITE3_to_ONLY_WRITE4_a: Read request is idle. Write requests and data are set and computed accordingly. pk write enable is not set.

- ONLY_WRITE4_to_ONLY_WRITE5_a: Read request is idle. Write requests and data are set and computed accordingly. pk write enable is not set. The last sk write request is sent.

- ONLY_WRITE5_to_ONLY_WRITE6_a: Read request is idle. Write requests and data are set and computed accordingly. pk write request is reset. sk write request is idle.

- ONLY_WRITE6_to_DONE_a: **done** is set true as both read & write operations are done/idle.

- DONE_to_IDLE_a: The state transitions back to idle. 



## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
