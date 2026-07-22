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

# pkdecode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_pkdecode**

- **fv_pkdecode_m.sv**: Assertion IP (AIP) for the pkdecode block
- **fv_pkdecode_pkg.sv**: Assertion IP package
- **fv_pkdecode_functions.sv**: Helper functions for the AIP
- **fv_pkdecode_aip.sv**: Additional in-place assertions
- **fv_pkdecode_binding.sv**: AIP binding file
- **fv_pkdecode_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model (pkdecode.h)


## DUT Overview

The DUT pkdecode has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                         |
| ---- | ---------------------      | --------- | ----------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                            |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                                |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered.                                |
| 4    | pkdecode_enable            | input     | The module is enabled by the top hierarchy with this signal                         |
| 5    | src_base_addr[15:0]        | input     | The base address of reading the coefficient data from the memory                    |
| 6    | dest_base_addr[13:0]       | input     | The base address of writing output to the memory                                    |
| 7    | API_rd_address[15:0]       | output    | The memory read data request address                                                |
| 8    | API_rd_data[79:0]          | input     | The 80-bit coefficient data input                                                   |
| 9    | mem_a_wr_req               | output    | The memory write data request for encoded coeffs, consists of r/w mode and addr     |
| 10   | mem_b_wr_req               | output    | Another memory write data request for encoded coeffs, consists of r/w mode and addr |
| 11   | mem_a_wr_data[3:0][23:0]   | output    | The encoded coefficients, output data to be saved into memory                       |
| 12   | mem_b_wr_data[3:0][23:0]   | output    | Another encoded coefficients, output data to be saved into memory                   |
| 13   | pkdecode_done              | output    | The output bit indicating pkdecode operation is done                                |

When the enable signal arrives, the design starts requesting and then reading 80 bits of coefficient. The 80 bits are split into 8 10-bit data and each of them are concatinated 0 bit at MSB and are shifted by 13 bits, resulting in 8 24-bit encoded coefficients. These are then set to two outputs and write requests are sent correspondingly. When the THE_LAST_ADDR is reached, the last data is read, and when all the outputs are finished, the pkdecode_done signal is asserted.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst** is binded with the DUT (reset_n && !zeroize), which ensures the reset functionality. And another AIP signal start_port_valid is triggered whenever the **pkdecode_enable** is high.

- run_reset_a: Checks that all the registers are resetted, the state and write request are idle, read address and write data port are 0.

- run_IDLE_wait_a: Checks if there isn't **pkdecode_enable** signal triggered in IDLE state then the state stays in IDLE and read/write requests as well as opearand values stay stable, and **pkdecode_done** is 0.

- run_IDLE_to_READ_a: If state is in idle and **pkdecode_enable** signal is asserted, it sends the first read request to the memory.

- run_READ_to_READ_EXEC_a: After the first read request is sent, the second read request is sent in the following clock cycle. The api_operand is incremented.

- run_READ_EXEC_to_READ_WRITE_a: After the second read request is sent, the third read request is sent in the following clock cycle. The api_operand is incremented.

- run_READ_WRITE_to_READ_WRITE_a: After the third read request is sent, it enters the LOOP state where both data read and data write occur. The memory request outputs and operands are updated accordingly. The coefficient is encoded and set to output.

- run_READ_WRITE_to_WRITE_a: The LOOP iterates to read input and write outputs until **api_operand** reaches 256. Then it goes to Write state, operands and memory requests are updated accordingly. The last read request is sent.

- run_WRITE_to_DONE_a: The read request address and api_operand are set to 0. The write data is computed and write request is sent. mem_operand is updated.

- run_DONE_to_IDLE_a: the **pkdecode_done** is asserted and state transitions back to Idle. The read request address and operands are reset to 0. Write request is reset to idle.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
