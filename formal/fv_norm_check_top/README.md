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

# norm_check_top - Formal Verification

Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure

The following files are part of the main directory **formal/fv_norm_check_top**

- `fv_norm_check_top_m.sv`: Main assertion IP with FSM state transition and control flow assertions
- `fv_norm_check_top_pkg.sv`: Package definitions for types, parameters, and constants
- `fv_norm_check_top_functions.sv`: Helper functions for norm validation and memory request generation
- `fv_norm_check_top_binding.sv`: Binding of assertions to DUT signals
- `fv_norm_check_top_constraints.sv`: Constraints for formal verification
- model: Contains the high level abstracted model (`norm_check_top.h`)

## DUT Overview

The DUT `Norm_Check_Top` is a cryptographic norm checking module used in the MLDSA (Module-Lattice-Based Digital Signature Algorithm) signature verification process. It reads vector data from memory, checks if elements are valid according to the norm check mode, and signals completion status.

| S.No | Port                      | Direction | Description                                                                  |
| ---- | ------------------------- | --------- | ---------------------------------------------------------------------------- |
| 1    | clk                       | input     | Clock signal for synchronous operation                                      |
| 2    | rst                       | input     | Reset signal                                                                 |
| 3    | mem_base_addr_port_vld    | input     | Valid signal indicating mem_base_addr_port contains valid address            |
| 4    | mem_base_addr_port_rdy    | output    | Ready signal indicating module can accept new base address                  |
| 5    | mem_base_addr_port        | input     | Base memory address for norm check data                                     |
| 6    | norm_check_mode_port      | input     | Norm check mode select (2-bit mode signal)                                  |
| 7    | shuffling_enable_port     | input     | Enable signal for shuffling during idle state                               |
| 8    | randomness_port           | input     | Randomness value (5-bit) for shuffling                                      |
| 9    | randomness_lsb_port       | input     | LSB of randomness value (1-bit)                                             |
| 10   | mem_rd_data_port          | input     | Memory read data (array of 4 x 24-bit values)                               |
| 11   | norm_check_done_port      | output    | Signal indicating norm check operation is complete                          |
| 12   | invalid_port              | output    | Signal indicating invalid elements detected during norm check                |
| 13   | mem_rd_req_port           | output    | Memory read request with address and read/write enable                      |

## FSM States

The Norm_Check_Top module implements a 4-state FSM:

- **IDLE**: Waiting for mem_base_addr_port_vld signal to start operation
  - Increments internal counters
  - Applies randomness during shuffling
  - Awaits valid base address

- **READ_MEM**: Initial memory read state
  - Issues first memory read request
  - Transitions to WAIT after receiving data
  - Transitions to DONE if 64 elements already processed

- **WAIT**: Waiting for memory data and issuing subsequent reads
  - Receives memory read data
  - Checks validity of data elements
  - Increments element counter (neutral_cnt)
  - Issues next memory read request
  - Transitions back to READ_MEM or to DONE when neutral_cnt reaches 64

- **DONE**: Operation complete state
  - Asserts norm_check_done_port
  - Transitions back to IDLE on next clock cycle
  - Disables memory read requests

## Assertion IP Overview

The Assertion IP consists of reset, FSM state transition, invalid signal handling, and liveness properties.

### Reset Assertions

- **run_reset_a**: On reset assertion followed by deassertion, FSM enters IDLE state with all control signals and registers cleared

### IDLE State Transition Assertions

- **run_IDLE_to_READ_MEM_a**: When mem_base_addr_port_vld is asserted and shuffling_enable_port is set, transitions to READ_MEM with shuffling randomness applied
- **run_IDLE_to_READ_MEM_1_a**: When mem_base_addr_port_vld is asserted and shuffling_enable_port is not set, transitions to READ_MEM without randomness
- **run_IDLE_wait_a**: When mem_base_addr_port_vld is not asserted, remains in IDLE with counters incremented and state stable

### READ_MEM State Transition Assertions

- **run_READ_MEM_to_DONE_a**: When neutral_cnt reaches 63 (meaning 64 elements processed), transitions to DONE state
- **run_READ_MEM_to_WAIT_a**: When neutral_cnt is less than 63, transitions to WAIT state with neutral_cnt incremented and next memory request issued

### WAIT State Transition Assertions

- **run_WAIT_to_READMEM_a**: When neutral_cnt is less than 63, transitions back to READ_MEM with neutral_cnt incremented and control signals stable
- **run_WAIT_to_DONE_a**: When neutral_cnt reaches 63, transitions to DONE state with memory requests disabled

### DONE State Transition Assertions

- **run_DONE_to_IDLE_a**: From DONE state, transitions back to IDLE with norm_check_done_port asserted and memory read requests disabled

### Invalid Signal Assertions

- **run_IDLE_disable_invalid_a**: When in IDLE state and norm_check_done_port is asserted, invalid_port is cleared in next cycle
- **run_IDLE_STABLE_INVALID_a**: When in IDLE state and norm_check_done_port is not asserted, invalid_port remains zero
- **run_INVALID_COMPUTATION_a**: During READ_MEM, WAIT, or DONE states, invalid_port is updated based on validity checks of received memory data or maintains previous value

### Liveness Assertions

- **run_IDLE_eventually_left_a**: When mem_base_addr_port_vld is asserted in IDLE state, eventually leaves IDLE
- **run_READ_MEM_eventually_left_a**: Eventually leaves READ_MEM state
- **run_WAIT_eventually_left_a**: Eventually leaves WAIT state
- **run_DONE_eventually_left_a**: Eventually leaves DONE state

### FSM Consistency Assertion

- **run_consistency_onehot0_state**: Ensures only one FSM state is active at any given time

## Assertion Functions

The verification module uses helper functions imported from `norm_check_top_functions`:

- `return_invalid()`: Checks if a data element is invalid based on norm_check_mode
- `return_idle_mem_rd_req()`: Generates memory read address during IDLE state with optional randomness
- `return_read_mem_mem_rd_req()`: Generates memory read address during READ_MEM state
- `return_wait_mem_mem_rd_req()`: Generates memory read address during WAIT state with counter increment

## Operation Flow

1. **Initialization**: FSM starts in IDLE, awaiting mem_base_addr_port_vld signal
2. **Base Address Reception**: When valid base address arrives, FSM transitions to READ_MEM
3. **Element Validation Loop**: 
   - READ_MEM issues memory request and transitions to WAIT
   - WAIT receives data, checks validity, increments counter
   - Loop continues until 64 elements processed
4. **Completion**: When neutral_cnt reaches 64, transitions to DONE
5. **Status Assertion**: norm_check_done_port is asserted in DONE state
6. **Return to Idle**: Transitions back to IDLE for next operation

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
