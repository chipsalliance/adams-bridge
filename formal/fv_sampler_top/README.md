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

# abr_sampler_top

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_sampler_top** for . Under each of this directoris for each module there is a **model** directory that contains the high level model **abr_sampler_top.h**. 

The **formal/fv_sampler_top** also  contains the top level verification assertion IP(AIP) named as **fv_sampler_top.sv**, the properties are written  in the file **fv_sampler_top_whitebox.sv** and the constraints are written in **fv_sampler_top_constraints.sv**. We also have **fv_sampler_top_pkg.sv** for some global declarations, and **fv_sampler_top_m.sv** contains the property generated from the model **abr_sampler_top.h**. 


## DUT Overview

The DUT abr_sampler_top has the primary inputs and primary outputs as shown below.

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

The Assertion IP signals are bound with the respective signals in the dut. There are assertions for the FSM inside the design, that triggers the sha3_run and sha3_process signals (abr_sampler_top.sv). In addition, inside the **fv_sampler_top_whitebox.sv** there are properties that ensure the correctness of the remaining signals, that are either asserted combinationally or are connections between instances.

### fv_sampler_top_m.sv

- a_run_reset: Checks that all the signals are set correctly and the sampler_fsm transitions to IDLE.

- a_run_done_to_done: Checks that in case of a squeezing signal being set during MLDSA_SAMPLER_DONE, the design stays in the MLDSA_SAMPLER_DONE state. The done signal will be set according to sha3_fsm signal.

- a_run_done_to_idle: Checks that in case of no squeezing signal during MLDSA_SAMPLER_DONE, the design transitions to the MLDSA_SAMPLER_IDLE state and the signals are set accordingly.

- a_run_idle_to_idle: Checks that in case no sampler_start_i is asserted, the design stays in the MLDSA_SAMPLER_IDLE state.

- a_run_idle_to_proc: Checks if the design leaves the MLDSA_SAMPLER_IDLE state, when the sampler_start_i signal is asserted. Here, the sha3_process signal has to be asserted.

- a_run_proc_to_wait: Checks if the design leaves the MLDSA_SAMPLER_PROC state. This should happen without any trigger condition.

- a_run_run_to_done: Checks if the design transitions from MLDSA_SAMPLER_RUN to MLDSA_SAMPLER_DONE, if the sampler_done signal is asserted during the MLDSA_SAMPLER_RUN state. Accordingly, within the MLDSA_SAMPLER_DONE sha3_done has to be set to true or false.

- a_run_run_to_wait: Checks if the design goes back from MLDSA_SAMPLER_RUN to MLDSA_SAMPLER_WAIT, if no sampler_done signal is asserted.

- a_run_wait_to_done: Checks if the design transitions from MLDSA_SAMPLER_WAIT to MLDSA_SAMPLER_DONE, if the sampler_done signal is asserted during the MLDSA_SAMPLER_WAIT state. Accordingly, within the MLDSA_SAMPLER_DONE sha3_done has to be set to true or false.

- a_run_wait_to_run: Checks if the design transition from MLDSA_SAMPLER_WAIT to MLDSA_SAMPLER_RUN, when sha3_state_dv & ~sha3_state_hold are asserted. In addition, sha3_run signal has to be asserted in case no sampler_done signal is asserted.

- a_run_wait_to_wait: Checks if the design can reside in MLDSA_SAMPLER_WAIT state.

- a_run_xxx_eventually_left: These assertions check, that each MLDSA_SAMPLER state leaves at one point.

### fv_sampler_top_whitebox.sv

- a_mode_mux_none: Checks the case, when no mode has been selected and the signals are reset accordingly
- a_mode_mux_shake256: Checks the case, when SHAKE256 mode has been selected and the signals are set according to the mode
- a_mode_mux_shake128: Checks the case, when SHAKE128 mode has been selected and the signals are set according to the mode
- a_mode_mux_sha512: Checks the case, when SHA512 mode has been selected and the signals are set according to the mode
- a_mode_mux_sha256: Checks the case, when SHA256 mode has been selected and the signals are set according to the mode
- a_mode_mux_rej_sampler_mldsa: Checks the case, when REJ_SAMPLER mode MLDSA has been selected and the signals are set according to the mode
- a_mode_mux_rej_sampler_mlkem: Checks the case, when REJ_SAMPLER mode MLKEM has been selected and the signals are set according to the mode
- a_mode_mux_exp_mask: Checks the case, when EXP_MASK mode has been selected and the signals are set according to the mode
- a_mode_mux_rej_bounded: Checks the case, when REJ_BOUNDED mode has been selected and the signals are set according to the mode
- a_mode_mux_sample_in_ball: Checks the case, when SAMPLER_IN_BALL mode has been selected and the signals are set according to the mode
- a_mode_mux_abr_cbd_sampler: Checks the case, when CBD_SAMPLER mode has been selected and the signals are set according to the mode

- a_register_rej_bounded_vld_hld: Checks if in case of a data_hold signal from REJ_BOUNDED and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- a_register_rej_sampler_vld_hld: Checks if in case of a data_hold signal from REJ_SAMPLER and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- a_register_sample_in_ball_ctrl_vld_hld: Checks if in case of a data_hold signal from SAMPLER_IN_BALL and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
- a_register_sample_in_ball_ctrl_vld_stable: Checks that the piso_dv signal is asserted and stays asserted until the sampler is done.
- a_register_piso_bits: Checks if there is no data incoming, the design can expect valid data in the future.

- a_signal_piso_hold: Checks if the piso hold signal is asserted correctly.

- a_signal_rejs_piso_dv: Checks if REJ_SAMPLER data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- a_signal_rejb_piso_dv: Checks if REJ_BOUNDED data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- a_signal_exp_piso_dv: Checks if EXP_MASK data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- a_signal_sib_piso_dv: Checks if SAMPLE_IN_BALL data valid signals are asserted correctly, based on the mode and the piso data valid signal.
- a_signal_exp_piso_data: hecks if EXP_MASK input data is extracted correctly from piso output data

- a_signal_sampler_busy: Checks that the sampler_busy_o signal is asserted either through sampler_start_i or the sampler_fsm states.
- a_liveness_sampler_busy: Checks if the sampler_busy_o signal is also deasserted at one point.

- a_signal_sampler_ntt_dv: Checks that sampler_ntt_dv_o represents the data valid signal from REJ_SAMPLER.

- a_signal_sampler_ntt_data_mlkem: Checks that sampler_ntt_data_o represents the output data from REJ_SAMPLER_MLKEM.
- a_signal_sampler_ntt_data_mldsa: Checks that sampler_ntt_data_o represents the output data from REJ_SAMPLER_MLDSA.

- a_signal_sib_mem_cs_mux: Checks that sib_mem_cs_mux is assigned correclty.

- a_signal_sib_mem_addr_mux: Checks that sib_mem_addr_mux is assigned correclty.

- a_signal_sib_mem_rd_data: Checks that sib_mem_rd_data is assigned correclty.


- a_signal_coeff_cnt_sampler_start: Checks, if there is either a sampler_start_i or a sampler_done, the coeff_cnt is set to 0.
- a_signal_coeff_cnt_vld_cycle: Checks, if there is no a sampler_start_i nor a sampler_done, but a vld_cycle, the coeff_cnt increments.
- a_signal_coeff_cnt_no_vld_cycle: Checks, if there is no a sampler_start_i, no sampler_done and no vld_cycle, the coeff_cnt stays stable.

- a_signal_dest_addr_sampler_done: Checks, if there is either a sampler_done, the dest_addr is set to 0.
- a_signal_dest_addr_sampler_start: Checks, if there is no sampler_done, but a sampler_start_i, the dest_addr is set to dest_base_addr_i
- a_signal_dest_addr_vld_cycle: Checks, if there is no sampler_done, no sampler_start_i, but a vld_cycle, the dest_addr increments
- a_signal_dest_addr_no_vld_cycle: Checks, if there is no sampler_done, no sampler_start_i and no vld_cycle, the dest_addr stays stable

- a_signal_abr_sha3_data: Checks that sha3 output is 0, whenever there is no data valid signal asserted.

- a_signal_reset: Checks that all sequential signals are resetted accordingly.

- a_signal_sampler_fsm: Checks that the sampler_fsm signal is updated accordingly.

- a_signal_sampler_fsm_in_range: Checks that the sampler_fsm signal stays in its specified value range.

## Formal Setup
This AIP instantiates the LUBIS library module `lubis_scoreboard`, which is not part of this repository.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
