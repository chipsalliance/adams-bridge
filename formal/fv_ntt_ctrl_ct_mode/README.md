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

# ntt_ctrl - ct_mode
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectories are part of the main directory **formal/fv_ntt_ctrl_ct_mode**

- `fv_ntt_ctrl_ct_mode_m.sv`: Assertion IP (AIP) for CT mode
- `fv_ntt_ctrl_ct_mode_pkg.sv`: Package definitions for CT mode types and parameters
- `fv_ntt_ctrl_ct_mode_binding.sv`: Binding of assertions to DUT signals
- `fv_ntt_ctrl_ct_mode_aip.sv`: Additional in-place assertions for CT mode
- `fv_ntt_ctrl_ct_mode_additional_property.sv`: Additional properties for CT mode
- `fv_ntt_ctrl_ct_mode_constraints.sv`: Constraints for formal verification
- model: Contains the high level abstracted model
  - `model/ntt_ctrl_ct_mode.h`: High level abstracted model
  - `model/ntt_ctrl_ct_mode.luref`: LUBIS reference documentation

## DUT oveview

The DUT NTT_CTRL has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                                  |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals.                                    |
| 2    | reset_n           | input     | The reset signal is active low and reset all register and primary output to initial value.   |
| 3    | zeroize           | input     | When this signal is triggered all register and primary output to value.                      |
| 4    | ntt_mode          | input     | This signal is to selelct mode out of five mode (ct,gs,pwm,pwo,pws).                         |
| 5    | ntt_enable        | input     | This is input signal when this is asserted it will start NTT                                 | 
| 6    | butterfly_ready   | input     | This signal will start butterfly computauion                                                 |
| 7    | buf0_valid        | input     | When this signal is recived buffer count will start count till 3 to valid all 4 buffer are valid | 
| 8    | sampler_valid     | input     | Sampler valid is not used in this mode so it's open                                          |
| 9    | accumulate        | input     | Accumulate is not used in this mode so it's open                                             |
| 10   | ntt_mem_base_addr | input     | This input is for base singal we have three source destination and interim signals           |
| 11   | shuffle_en        | input     | Depnds on hat some signal some output will chnage                                            |
| 12   | random            | input     | Random value will be assigned to chunk_count and chunk rand offset                           |
| 13   | bf_enable         | output    | Indicate bf_enable flag depnding upon states                                                 | 
| 14   | opcode            | output    | Depends on ntt mode output will be assinges for ct mode always equal to ct mode              |
| 15   | masking_en_ctrl   | output    | Always zero for ct mode                                                                      |
| 17   | buf_wren          | output    | Depending on state it will assert                                                            |
| 18   | buf_rden          | output    | Depending on state it will assert                                                            |
| 19   | buf_wrptr         | output    | Output signals increase accoding to buf_wren                                                 |
| 20   | buf_rdptr         | output    | Output signals for module                                                                    |
| 21   | twiddle_addr      | output    | output of module will work as input for twiddle ROM                                          |     
| 22   | mem_rd_addr       | output    | Output memomry read signal after ntt operation it will provide shuffled addder usign butterfly operation|
| 23   | mem_wr_addr       | output    | Output memomry read signal after ntt operation it will provide shuffled addder usign butterfly operation| 
| 24   | mem_rd_en         | output    | Output indicate the mem_rd_en signal is high                                                 |
| 25   | mem_wr_en         | output    | Output indicate the mem_wr_en signal is high                                                 |
| 26   | buf_wr_rst_count  | output    | buf_wr_rst_count it will be asserted accodiding to STATES                                    |
| 27   | buf_rd_rst_count  | output    | buf_rd_rst_count it will be asserted accodiding to STATES                                    |
| 28   | pw_rden           | output    | Set to be zero for ct mode pw_rden                                                           |
| 29   | pw_wren           | output    | Set to be zero for ct mode pw_wren                                                           | 
| 30   | busy              | output    | It will indicate that ntt operation is ongoing                                               |
| 31   | done              | output    | It will assert when the ntt opeartion is done                                                |

The design take base address as the input signals and the perform the bf2X2 for ct mode and perform the shuffle opeartion to the address and provide shuffled output address

## Assertion IP overview

The Assertion IP signals are bound to the respective signals in the DUT, where rst is bound to (!ntt_ctrl.reset_n || ntt_ctrl.zeroize), ensuring the reset functionality.

The design primarily consists of two FSMs: one for Read Address (Read FSM) and another for Write Address (Write FSM). The state transitions depend on signals such as ntt_enable, buf0_valid, rd_valid_count, and wr_valid_count. Based on these signals and register conditions, specific transitions occur in the design.

- read_reset_a: All the register's and primary output related to read fsm are zero for reset.
  
- read_read_idle_to_read_idle_a: All register and primary output gets thier initial values.
  
- read_read_idle_to_read_stage_a: This assertion ensures that whenever ntt_enable is asserted, the read_idle state transitions to read_stage and    
                                  starts the NTT computation. Additionally, all registers are assigned their respective values according to the transition.

- read_read_stage_to_read_buf_a: When we are in the read_stage and ntt_done is low, the read_stage will jump to the read_buf state because the NTT computation is not yet complete. It    
                                 will move to a future state and wait for the NTT operation to finish before proceeding.

- read_read_stage_to_read_idle_a: When the NTT operation is complete, ntt_done goes high, and we return to the idle state.
  
- read_read_stage_to_read_stage_a: We stay in the read_stage when we are not transitioning to another state, meaning if ntt_done is neither low nor high.
  
- read_read_buf_to_read_buf_a: This assertion ensures that we are in the buf state. If we do not receive buf0_valid, it means valid data is not available.
- read_read_buf_to_read_exec_a: This assertion ensures that we are in the buf state, and upon receiving the buf0_valid signal, we transition to the read_exec state.
- read_read_exec_to_read_exec_wait_a: This assertion ensures that whenever buf_count == 3 and rd_valid_count == 60, a transition occurs from read_exec to read_exec_wait.
- read_read_exec_to_read_buf_a:This property is not expected to hold, as the design is behaving in a way that should transition from read_exec to read_buf instead.
- read_read_exec_to_read_exec_a: If we are not transitioning from read_exec to either read_buf or read_exec_wait, then we remain in the read_exec state until all conditions are met. 
                                 This means buf_count and rd_valid_count have not yet reached the required values.
- read_read_exec_wait_to_read_stage_a: When rd_valid_count == 64 and buf_count == 3, we transition from the read_exec_wait state to the read_stage state.
- read_read_exec_wait_to_read_exec_wait_a: When rd_valid_count != 64 and buf_count != 3, we remain in the read_exec_wait state.
  

- write_reset_a: All registers and primary outputs related to the read FSM are set to zero during reset.
- write_write_idle_to_write_stage_a: When we are in the idle state and ntt_enable is asserted, we transition from idle to write_stage.
- write_write_idle_to_write_idle_a: When we are in the idle state and ntt_enable is not asserted, we remain in the idle state.
- write_write_stage_to_write_idle_a: When all NTT operations are complete, we receive ntt_done. Depending on the value of ntt_done, we transition from write_stage to idle state.
- write_write_stage_to_write_mem_a: When we are in the write_stage and ntt_done is low, we transition from write_stage to write_mem.
- write_write_mem_to_write_mem_a: This transition depends on the wr_valid_count. If wr_valid_count != 63, we stay in the current state until it reaches 63.
- write_write_mem_to_write_stage_a:This transition depends on the wr_valid_count. When it reaches 63 (wr_valid_count == 63), we transition from write_mem to write_stage.

This assertion make sure That we left all state eventually -
- read_read_idle_eventually_left_a
- read_read_stage_eventually_left_a
- read_read_buf_eventually_left_a
- read_read_exec_eventually_left_a
- read_read_exec_wait_eventually_left_a
- write_write_idle_eventually_left_a
- write_write_stage_eventually_left_a
- read_consistency_onehot0_state
- write_consistency_onehot0_state
  

## additional_property
The following assertion are to prove combinational logic of desgin.

- assert_buf_enable_a
- assert_buf_wr_en_a
- assert_buf_wr_ptr_check_a
- assert_twiddle_addr_a
- assert_buf_rd_en_a
- assert_buf_wr_rst_count_a
- assert_buf_rd_rst_count_a
- assert_buf_rdptr_a
- assert_mem_rd_en_exec_a
- assert_busy_a
- mem_rd_en_a
- assert_mem_wr_en_a
- not_same_address_a
- ntt_done_a
- latch_index_rand_offset_a
- assert_latch_chunk_rand_offset_a

## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
