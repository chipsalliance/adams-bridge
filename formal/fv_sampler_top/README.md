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

# mldsa_sampler_top
Date: 26.03.2025
Author: LUBIS EDA GmbH

## Folder Structure
The following files and subdirectory are part of the main directory **formal/fv_sampler_top**

- **fv_mldsa_sampler_top_m.sv**: Main assertion IP containing the FSM properties
- **fv_mldsa_sampler_top_pkg.sv**: Package definitions and shared types
- **fv_mldsa_sampler_top_functions.sv**: Helper functions for the AIP
- **fv_mldsa_sampler_top_binding.sv**: AIP binding file
- **fv_mldsa_sampler_top_aip.sv**: Additional in-place assertions
- **fv_mldsa_sampler_top_constraints.sv**: Constraints for formal verification
- model: Contains the high level abstracted model
  - `model/mldsa_sampler_top.h`: High-level abstracted model
  - `model/mldsa_sampler_top.luref`: LUBIS coverage and liveness reference
  - `model/mldsa_sampler_top.dot`: FSM diagram


## DUT Overview

The DUT mldsa_sampler_top has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                                  |
| 2    | rst_b             | input     | The reset signal is active low and resets the core                                        |
| 3    | zeroize           | input     | The core is reseted when this signal is triggered.                                        |
| 4    | sampler_mode_i    | input     | Defines, which of the samplers should be operated.                                        |
| 5    | sha3_start_i      | input     | Sets the start signal for the sha3 instance to start its operation.                       | 
| 6    | msg_start_i       | input     | Follows the sha3 start signal with a pulse.                                               |
| 7    | msg_valid_i       | input     | Is asserted, when valid msg data is available.                                            |
| 8    | msg_rdy_o         | output    | Signal that comes from the sha3 instance to indicate ready messages.                      |
| 9    | msg_strobe_i      | input     | Strobe signal as input for the sha3 instance.                                             |
| 10    | msg_data_i       | input     | Input data for the sha3 instance and following samplers.                                  |
| 11    | sampler_start_i     | input     | Indicates the start of the sampling procedure and when samplers are started            |
| 12    | dest_base_addr_i    | input     | Provides the base destination address to store the results.                            |
| 13    | sib_mem_rd_req_i    | input     | Read request signal for the sib_mem instance.                                          |
| 14    | sib_mem_rd_data_o   | output    | Output data from the sib_mem instance.                                                 |
| 15    | sampler_busy_o      | output    | Busy signal, indicating that one of the samplers is in operation.                      |
| 16    | sampler_ntt_dv_o    | output    | NTT data valid signal.                                                                 |
| 17    | sampler_ntt_data_o  | output    | NTT data output signal.                                                                |
| 18    | sampler_mem_dv_o    | output    | Data valid signal assigned with individual sampler data valid signals.                 |
| 19    | sampler_mem_data_o  | output    | Data output signal assigned with individual sampler data output signals.               |
| 20    | sampler_mem_addr_o  | output    | Destination address for the sampler operation.                                         |
| 21    | sampler_state_dv_o  | output    | Data valid signal assigned with individual sha3 data valid signals.                    |
| 22    | sampler_state_data_o| output    | Data output signal assigned with individual sha3 data output signals.                  |


The design serves as a ctrl unit for the samplers REJ_BOUNDED, EXP_MASK, REJ_SAMPLER and SAMPLER_IN_BALL. It coordinates the operation of the Keccak sha3 instance and the following sampler operations. Intermediate results are stored in a PISO buffer.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut. There are assertions for the FSM inside the design, that triggers the sha3_run, sha3_done and sha3_process signals (mldsa_sampler_top.sv). In addition, inside the mldsa_sampler_top_aip.sv there are properties that ensure the correctness of the remaining signals, that are either asserted combinationally or are connections between instances.

### mldsa_sampler_top.sv

- run_reset_a: Checks that all the signals are set correctly and the sampler_fsm transitions to IDLE.

- run_DONE_to_DONE_a: Checks that in case of a squeezing signal being set during MLDSA_SAMPLER_DONE, the design stays in the MLDSA_SAMPLER_DONE state. The done signal will be set according to sha3_fsm signal.

- run_DONE_to_IDLE_a: Checks that in case of no squeezing signal during MLDSA_SAMPLER_DONE, the design transitions to the MLDSA_SAMPLER_IDLE state and the signals are set accordingly.

- run_IDLE_to_IDLE_a: Checks that in case no sampler_start_i is asserted, the design stays in the MLDSA_SAMPLER_IDLE state.

- run_IDLE_to_PROC_a: Checks if the design leaves the MLDSA_SAMPLER_IDLE state, when the sampler_start_i signal is asserted. Here, the sha3_process signal has to be asserted.

- run_PROC_to_WAIT_a: Checks if the design leaves the MLDSA_SAMPLER_PROC state. This should happen without any trigger condition.

- run_RUN_to_DONE_a: Checks if the design transitions from MLDSA_SAMPLER_RUN to MLDSA_SAMPLER_DONE, if the sampler_done signal is asserted during the MLDSA_SAMPLER_RUN state. Accordingly, within the MLDSA_SAMPLER_DONE sha3_done has to be set to true or false.

- run_RUN_to_WAIT_a: Checks if the design goes back from MLDSA_SAMPLER_RUN to MLDSA_SAMPLER_WAIT, if no sampler_done signal is asserted.

- run_WAIT_to_DONE_a: Checks if the design transitions from MLDSA_SAMPLER_WAIT to MLDSA_SAMPLER_DONE, if the sampler_done signal is asserted during the MLDSA_SAMPLER_WAIT state. Accordingly, within the MLDSA_SAMPLER_DONE sha3_done has to be set to true or false.

- run_WAIT_to_RUN_a: Checks if the design transition from MLDSA_SAMPLER_WAIT to MLDSA_SAMPLER_RUN, when sha3_state_dv & ~sha3_state_hold are asserted. In addition, sha3_run signal has to be asserted in case no sampler_done signal is asserted.

- run_WAIT_to_WAIT_a: Checks if the design can reside in MLDSA_SAMPLER_WAIT state.

- run_XXX_eventually_left_a: These assertions check, that each MLDSA_SAMPLER state leaves at one point.

### fv_mldsa_sampler_top_aip.sv

- mode_mux_NONE_a: Checks the case, when no mode has been selected and the signals are reset accordingly
- mode_mux_SHAKE256_a: Checks the case, when SHAKE256 mode has been selected and the signals are set according to the mode
- mode_mux_SHAKE128_a: Checks the case, when SHAKE128 mode has been selected and the signals are set according to the mode
- mode_mux_REJ_SAMPLER_a: Checks the case, when REJ_SAMPLER mode has been selected and the signals are set according to the mode
- mode_mux_EXP_MASK_a: Checks the case, when EXP_MASK mode has been selected and the signals are set according to the mode
- mode_mux_REJ_BOUNDED_a: Checks the case, when REJ_BOUNDED mode has been selected and the signals are set according to the mode
- mode_mux_SAMPLER_IN_BALL_a: Checks the case, when SAMPLER_IN_BALL mode has been selected and the signals are set according to the mode

- register_REJ_BOUNDED_vld_hld_a: Checks if in case of a data_hold signal from REJ_BOUNDED and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- register_REJ_SAMPLER_vld_hld_a: Checks if in case of a data_hold signal from REJ_SAMPLER and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- register_SAMPLE_IN_BALL_vld_hld_a: Checks if in case of a data_hold signal from SAMPLER_IN_BALL and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- register_SAMPLE_IN_BALL_CTRL_vld_stable_a: Checks that the piso_dv signal is asserted and stays asserted until the sampler is done.
- register_PISO_BITS_REJS_a: Checks if there is no data incoming, the design can expect valid data in the future.

- signal_PISO_HOLD_a: Checks if the piso hold signal is asserted correctly.

- signal_REJS_PISO_DV_a: Checks if REJ_SAMPLER data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- signal_REJB_PISO_DV_a: Checks if REJ_BOUNDED data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- signal_EXP_PISO_DV_a: Checks if EXP_MASK data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- signal_SIB_PISO_DV_a: Checks if SAMPLE_IN_BALL data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- signal_EXP_PISO_DATA_a: hecks if EXP_MASK input data is extracted correctly from piso output data

- signal_SAMPLER_BUSY_a: Checks that the sampler_busy_o signal is asserted either through sampler_start_i or the sampler_fsm states.
- liveness_SAMPLER_BUSY_a: Checks if the sampler_busy_o signal is also deasserted at one point.

- signal_SAMPLER_NTT_DV_a: Checks that sampler_ntt_dv_o represents the data valid signal from REJ_SAMPLER.

- signal_SAMPLER_NTT_DATA_a: Checks that sampler_ntt_data_o represents the output data from REJ_SAMPLER.

- signal_SIB_MEM_CS_MUX_a: Checks that sib_mem_cs_mux is assigned correclty.

- signal_SIB_MEM_ADDR_MUX_a: Checks that sib_mem_addr_mux is assigned correclty.

- signal_SIB_MEM_RD_DATA_a: Checks that sib_mem_rd_data is assigned correclty.

- signal_REJS_DATA_a: Checks that rejs_data is delayed by one clock cycle.

- signal_COEFF_CNT_sampler_start_a: Checks, if there is either a sampler_start_i or a sampler_done, the coeff_cnt is set to 0.
- signal_COEFF_CNT_vld_cycle_a: Checks, if there is no a sampler_start_i nor a sampler_done, but a vld_cycle, the coeff_cnt increments.
- signal_COEFF_CNT_no_vld_cycle_a: Checks, if there is no a sampler_start_i, no sampler_done and no vld_cycle, the coeff_cnt stays stable.

- signal_DEST_ADDR_sampler_done_a: Checks, if there is either a sampler_done, the dest_addr is set to 0.
- signal_DEST_ADDR_sampler_start_a: Checks, if there is no sampler_done, but a sampler_start_i, the dest_addr is set to dest_base_addr_i
- signal_DEST_ADDR_vld_cycle_a: Checks, if there is no sampler_done, no sampler_start_i, but a vld_cycle, the dest_addr increments
- signal_DEST_ADDR_no_vld_cycle_a: Checks, if there is no sampler_done, no sampler_start_i and no vld_cycle, the dest_addr stays stable

- signal_ABR_SHA3_DATA_a: Checks that sha3 output is 0, whenever there is no data valid signal asserted.

- signal_reset_a: Checks that all sequential signals are resetted accordingly.

- signal_sampler_fsm_a: Checks that the sampler_fsm signal is updated accordingly.

- signal_sampler_fsm_in_range_a: Checks that the sampler_fsm signal stays in its specified value range.


## Reproduce Results

The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf) and formal coverage is at 100% excluding valid unreachable and deadcode. 

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
