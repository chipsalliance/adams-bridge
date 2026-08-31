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

# Makehint
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following subdirectories and files are part of the main directory **formal/fv_makehint**. Sequential and combinational blocks in the design are verified in separate files.

- **fv_makehint.sv**: Constraint top file
- **fv_makehint_constraints.sv**: Constraints for formal verification
- **fv_makehint_scoreboard.sv**: Scoreboard for data integrity and ordering checks

- model: This folder contains the high level model and AIP source files
  - **model/fv_makehint_m.sv**: Assertion IP (AIP) for the sequential part
  - **model/fv_makehint_pkg.sv**: Assertion IP package
  - **model/fv_makehint_binding.sv**: AIP binding file
  - **model/fv_makehint_functions.sv**: AIP functions file
  - **model/fv_makehint_cb_m.sv**: Assertion IP (AIP) for the combinational part
  - **model/fv_makehint_cb_binding.sv**: AIP binding file for combinational part
  - **model/makehint.h**: High level abstracted model
  - **model/makehint.dot**: FSM state diagram


## DUT Overview

The DUT makehint has the primary inputs and primary outputs as shown below.

| S.No | Port                       | Direction | Description                                                                       |
| ---- | ---------------------      | --------- | --------------------------------------------------------------------------------- |
| 1    | clk                        | input     | The positive edge of the clk is used for all the signals                          |
| 2    | reset_n                    | input     | The reset signal is active low and resets the module                              |
| 3    | zeroize                    | input     | The module is reseted when this signal is triggered                               |
| 4    | makehint_enable            | input     | The module is enabled by the top hierarchy with this signal                       |
| 5    | r[(4*REG_SIZE) - 1:0]      | input     | The r value that is obtained from the memory                                      |
| 6    | z[3:0]                     | input     | The z value that is obtained from the memory                                      |
| 7    | mem_base_addr[MLDSA_MEM_ADDR_WIDTH - 1 :0]       | input     | The base address of reading the coefficient data from the memory                             |
| 8    | dest_base_addr[MLDSA_MEM_ADDR_WIDTH - 1 :0]   | input     | The base address of writing output (reg_wrdata) to the memory              |
| 9    | invalid_h                  | output    | The 'h' component is invalid, so the data                                         |
| 10   | mem_rd_req                 | output    | The memory read data request, consists of r/w mode and addr                       |
| 11   | z_rd_req                   | output    | The memory read data request for z, consists of r/w mode and addr                 |
| 12   | makehint_done              | output    | The computation is done                                                           |
| 13   | reg_wren                   | output    | The output data enable signal                                                     |
| 14   | reg_wrdata[3:0][7:0]       | output    | The output data to be saved into the memory                                       |
| 15   | reg_wr_addr[MLDSA_MEM_ADDR_WIDTH-1:0]  | output    | The output address for the data to be stored                          |

The makehint process iterates through 8 polynomials, each polynomial needs 64 memory accesses, which are in total 256 index counts. In each cycle 4 hints are generated and they are valid signal for the buffer, while indexes are sent as data. When hint is 1, corresponding index is written into the buffer. When there are 4 data elements inside the buffer, **reg_wren** signal will be asserted and data will be sent to the memory. 

![alt text](image.png)

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the **rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality. Below properties for sequential and combinational parts are explained together.

- run_reset_a: Checks that all the registers are resetted and the state is idle.

- run_MH_IDLE_to_MH_RD_MEM_a: If state is in idle and **makehint_enable** signal is asserted, it sends the first read request to the memory. The memory request outputs are updated accordingly. **makehint_done** bit will be deasserted as it is no longer in idle state.

- run_MH_RD_MEM_to_MH_RD_MEM_x_a: After the first read request is sent, the second read request is sent in the following clock cycle. The memory request outputs are updated accordingly. The **hintgen_enable_reg** is asserted which starts hint computation and hintsum is updated. Buffer valid signal can be asserted or deasserted depending on the number of data elements.

- run_MH_RD_MEM_to_MH_WAIT1_x_a: After 64 memory accesses for a polynomial is done, it will go to the **MH_WAIT1** state. Buffer valid signal can be asserted or deasserted depending on the number of data elements.

- run_MH_WAIT1_to_MH_WAIT2_x_a: Makes transition to the **MH_WAIT2** state which selects the next polynomial and updates registers.

- run_MH_WAIT2_to_MH_RD_MEM_x_a: If it is not the last polynomial, 64 memory accesses start for the next polynomial and steps are repeated from **MH_MEM** to **MH_WAIT2**.

- run_MH_WAIT2_to_MH_FLUSH_SBUF_x_a: All polynomial calculations are done and **max_index_buffer** value is updated.

- run_MH_FLUSH_SBUF_to_MH_RD_IBUF_LOW_a: **reg_wr_addr** is updated and  with the property **run_flush_buf_a** from the **model/fv_makehint_cb_m.sv** file it is verified whether buffer is flushed.

- run_MH_RD_IBUF_LOW_to_MH_RD_IBUF_MID_a: **reg_wr_addr** is updated to **destination address + OMEGA/4**. With the property **run_max_index_buffer_data_1_a** from the **model/fv_makehint_cb_m.sv** file **max_index_buffer** lower index part sent to **reg_wrdata** is verified.

- run_MH_RD_IBUF_MID_to_MH_RD_IBUF_HIGH_a: **reg_wr_addr** is updated and with the property **run_max_index_buffer_data_2_a** from the **model/fv_makehint_cb_m.sv** file **max_index_buffer** mid index part sent to **reg_wrdata** is verified.

- run_MH_RD_IBUF_HIGH_to_MH_IDLE_a: **reg_wr_addr** is updated and with the property **run_max_index_buffer_data_3_a** from the **model/fv_makehint_cb_m.sv** file **max_index_buffer** higher index part sent to **reg_wrdata** is verified.

Remarks on the current constraints:
- assume_base_address_constraint: base addresses are set to a certain fixed number as per the design.

- assume_makehint_enable_constraint: Eventually makehint_enable is asserted, so that the **MH_IDLE** is left.

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100 0.000000e+00xcluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
