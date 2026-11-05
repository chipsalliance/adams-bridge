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

# fv_abr_sha3pad

## Folder Structure
The following files are part of the main directory **formal/fv_abr_sha3/fv_abr_sha3pad**

- **properties/fv_abr_sha3pad.sv** contains the assertion IP (AIP) for the abr_sha3pad block, together with the functional padding model and the bind statement that links the AIP to the DUT

- **properties/fv_abr_sha3pad_constraints.sv** contains the assumptions/constraints on the abr_sha3pad inputs (mode, strength, start/process protocol, message strobe, keccak_round handshake)

- **properties/fv_abr_sha3pad_incr_counter_m.sv** contains a generic counter (with reset, soft reset, set and increment) used to count the received message words and message bits

- **properties/fv_abr_sha3pad_scoreboard.sv** contains the scoreboard wrapper used to check that padded blocks are sent to keccak_round in the correct order and with the correct data

- **properties/fv_abr_sha3pad_scoreboard_tracking.sv** contains the symbolic data tracking logic, invariants and liveness check of the scoreboard

- **properties/fv_abr_sha3pad_scoreboard_properties.sv** contains the data ordering and integrity assertion of the scoreboard

- **waiver_list.tcl** contains the coverage waivers for unreachable code (unused strengths, unreachable FSM branches and counter error branches)


## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                        | Direction | Description                                                                                                    |
| ---- | --------------------------- | --------- | -------------------------------------------------------------------------------------------------------------- |
| 1    | clk_i                       | input     | The positive edge of the clk is used for all the signals                                                       |
| 2    | rst_b                       | input     | The reset signal is active low and resets the module                                                           |
| 3    | zeroize                     | input     | The module is reset when this signal is triggered                                                              |
| 4    | msg_valid_i                 | input     | Valid signal of the incoming message word from the message FIFO                                                |
| 5    | msg_data_i[Share][63:0]     | input     | Incoming 64-bit message word (one per share)                                                                   |
| 6    | msg_strb_i[7:0]             | input     | Byte strobe of the incoming message word, common for all shares (partial word if not all ones)                 |
| 7    | msg_ready_o                 | output    | Ready signal to the message FIFO, indicating that the message word is accepted                                 |
| 8    | keccak_data_o[Share][1599:0]| output    | Padded message block (keccak state) sent to keccak_round                                                       |
| 9    | keccak_ready_i              | input     | Input from keccak_round indicating it is ready to accept a new run                                             |
| 10   | keccak_run_o                | output    | Output to keccak_round to start processing a full keccak_f on keccak_data_o                                    |
| 11   | keccak_complete_i           | input     | Input from keccak_round indicating that the current keccak_f is completed                                      |
| 12   | mode_i                      | input     | SHA3 mode selection (Sha3, Shake)                                                                              |
| 13   | strength_i                  | input     | Keccak strength selection (L128 -> rate 1344 bits / 21 words, L256 -> rate 1088 bits / 17 words)               |
| 14   | start_i                     | input     | Pulse to start the padding logic and accept incoming messages                                                  |
| 15   | masked_i                    | input     | Input indicating that the operation is masked                                                                  |
| 16   | process_i                   | input     | Pulse to stop receiving messages and pad the trailing bits of the last block                                   |
| 17   | absorbed_o                  | output    | MuBi4 output indicating that the keccak sponge absorbing is complete                                           |
| 18   | sparse_fsm_error_o          | output    | Output indicating a fault in the sparse FSM encoding                                                           |
| 19   | msg_count_error_o           | output    | Output indicating a fault in the message counter                                                               |


The abr_sha3pad is the padding module of the SHA3 core. After start_i, it collects 64-bit message words from the message FIFO into a block of rate size (21 words for L128, 17 words for L256). When a block is full, it issues keccak_run_o to keccak_round with the block on keccak_data_o. When process_i is received, it appends the SHAKE domain separator and the 10*1 padding to the last block; if the last block has no space left for the padding, an extra padding-only block is sent. Once the last block has been processed by keccak_round, absorbed_o is pulsed.

The AIP contains a functional model of the padding behavior (fv_padded_msg), which rebuilds the expected padded block from the received message words, strobes, strength and process_i. For the masked configuration (EN_MASKING = 1), the message and the keccak data are reconstructed by XOR-ing both shares before comparison. In the following list are given the AIPs for abr_sha3pad:

## Assertion IP Overview

The AIP signals are bound to the respective signals in the DUT, where the reset of the checks is (!rst_b || zeroize), which ensures the reset and zeroize functionality.

- assert_data_ordering_and_integrity: Checks that the padded block sent on keccak_data_o at every keccak_run_o matches the expected padded block from the model, and that blocks are sent in the correct order (scoreboard with symbolic bit index).

- assert_data_ordering_and_integrity_liveness: Liveness assertion to check that an expected padded block is eventually sent out to keccak_round.

- assert_l0_only_pop_after_push: Scoreboard invariant, checks that a block is only sent out after it was expected by the model.

- assert_l1_depth_is_sufficient: Scoreboard invariant, checks that the scoreboard depth is never exceeded.

- assert_l2_data_not_in_then_never_at_output: Scoreboard invariant, checks that the tracked symbolic block is never seen at the output before it was pushed.

- assert_l3_tracking_counter_not_zero_if_data_in: Scoreboard invariant, checks that the tracking counter is non-zero while the tracked block is pending.

- assert_msg_ready_o_high: Checks the msg_ready_o output whenever msg_valid_i is high. msg_ready_o is high when a partial word is received before process_i, or when the block is not yet full (or its keccak run is issued in the same cycle), otherwise low.

- assert_absorbed_o_high: Liveness assertion to check that after start_i, absorbed_o is eventually set to MuBi4True.

- assert_absorbed_o_low: Checks that absorbed_o is MuBi4False during start_i and while the message is still being absorbed.

- assert_absorbed_o_pulse: Checks that absorbed_o is a single-cycle pulse.

- assert_absorbed_o_reset: Checks that absorbed_o is MuBi4False after reset or zeroize.

- assert_sparse_fsm_error_o: Checks that sparse_fsm_error_o is never raised.

- assert_msg_count_error_o: Checks that msg_count_error_o is never raised.

- cover_sampled_in / cover_sampled_out: Covers that the tracked symbolic block is pushed into and popped out of the scoreboard.

## Constraints Overview

- assume_mode_i: Mode is restricted to SHAKE.

- assume_strength_i: Strength is restricted to L128 or L256.

- assume_stable_strength_i: Strength is stable after start_i.

- assume_no_msg_at_start: No valid message word in the same cycle as start_i.

- assume_no_several_starts: No new start_i until absorbed_o is set.

- assume_process_i / assume_process_i_pulse: process_i is a pulse and only comes after at least one message word.

- assume_process_fairness: After start_i, process_i eventually comes.

- assume_msg_valid_after_process_i: No valid message words after process_i until the next start_i.

- assume_no_msgs_after_partial: No valid message words after a partial word until the next start_i.

- assume_no_bubbles: msg_strb_i is contiguous from the LSB (no bubbles).

- assume_complete_after_run: keccak_complete_i is a pulse 12*Share cycles after keccak_run_o.

- assume_no_complete_without_run: keccak_complete_i only after a keccak_run_o.

- assume_keccak_ready / assume_keccak_ready_fairness: keccak_ready_i is low while keccak_round is busy and is eventually high.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
