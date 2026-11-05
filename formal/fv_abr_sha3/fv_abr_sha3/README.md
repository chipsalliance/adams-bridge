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

# abr_sha3

## Folder Structure
The following files are part of the main directory **formal/fv_abr_sha3/fv_abr_sha3**. They
verify the top-level control of the **abr_sha3** core. Its two sub-blocks have their own benches:
**formal/fv_abr_sha3/fv_abr_sha3pad** (u_pad) and **formal/fv_abr_sha3/fv_abr_keccak_round**
(u_keccak).

- **model/abr_sha3.h** is the SystemC model of the abr_sha3 FSM (IDLE, ABSORB, SQUEEZE, RUN)
  that the operational properties in fv_abr_sha3_m.sv were generated from.

- **properties/fv_abr_sha3_m.sv** contains the FSM assertions (module fv_abr_sha3_m): reset,
  every state transition with its outputs, liveness of each state, and a one-hot check of the
  state conditions.

- **properties/fv_abr_sha3_binding.sv** is the wrapper (fv_abr_sha3_ref_wrapper_m) that maps
  the DUT signals and the sparse FSM states onto fv_abr_sha3_m and is bound to `abr_sha3`.

- **properties/fv_abr_sha3_whitebox.sv** contains the white-box assertions for the connections
  between the top FSM and the u_pad / u_keccak sub-blocks, the digest output guard and the
  error_o / error output wiring. It is bound to `abr_sha3`.

- **properties/fv_abr_sha3_constraints.sv** contains the assumptions/constraints. It is bound to
  `abr_sha3`.

- **properties/fv_abr_sha3_pkg.sv** contains the `eState` type (fv_idle_type, fv_absorb_type,
  fv_squeeze_type, fv_run_type) used by the FSM assertions.

- **properties/fv_abr_sha3_incr_counter_m.sv** is a local copy of the incrementing counter helper
  (module fv_abr_sha3_incr_counter_m). It is not instantiated by the constraints: the message counter in
  the constraints instantiates the LUBIS library module `lubis_incr_counter_m`, which is not part
  of this repository; contact contact@lubis-eda.com to obtain it.

- **properties/fv_abr_sha3_cov_waivers.tcl** waives the u_pad and u_keccak sub-blocks from the
  top coverage (see [Coverage](#coverage)).

- **properties/waiver_list_done_i_disabled.tcl** is a JasperGold GUI-exported waiver list from an
  earlier RTL version (see [Coverage](#coverage)).

## DUT Overview

The DUT has the primary inputs and primary outputs as shown below. `Share` is 2 with
`EnMasking = 1` and 1 otherwise; `MsgWidth = 64`, `MsgStrbW = 8` and `StateW = 1600`
(abr_sha3_pkg).

| S.No | Port                              | Direction | Description                                         |
| ---- | --------------------------------- | --------- | --------------------------------------------------- |
| 1    | clk_i                             | input     | Positive edge samples all signals.                  |
| 2    | rst_b                             | input     | Active-low reset; resets the module.                |
| 3    | zeroize                           | input     | Clears the module and returns the FSM to idle.      |
| 4    | msg_start_i                       | input     | Start of a message, to the pad block.               |
| 5    | msg_valid_i                       | input     | Message beat valid.                                 |
| 6    | msg_data_i[Share][MsgWidth-1:0]   | input     | Message data, one word per share.                   |
| 7    | msg_strb_i[MsgStrbW-1:0]          | input     | Byte strobe of the message beat (shared).           |
| 8    | msg_ready_o                       | output    | Message beat accepted.                              |
| 9    | rand_valid_i                      | input     | Entropy valid (masked Keccak).                      |
| 10   | rand_early_i                      | input     | Entropy early valid (masked Keccak).                |
| 11   | rand_data_i[StateW/2-1:0]         | input     | Entropy data (masked Keccak).                       |
| 12   | rand_aux_i                        | input     | Auxiliary entropy bit (masked Keccak).              |
| 13   | rand_update_o                     | output    | Requests new entropy.                               |
| 14   | rand_consumed_o                   | output    | Entropy consumed.                                   |
| 15   | mode_i (sha3_mode_e)              | input     | Hash mode: Sha3 or Shake.                           |
| 16   | strength_i (keccak_strength_e)    | input     | Security strength (L128 ... L512).                  |
| 17   | start_i                           | input     | Starts a hash operation (pulse).                    |
| 18   | masked_i                          | input     | Enables the masked Keccak datapath.                 |
| 19   | process_i                         | input     | Ends the message; starts the final absorb (pulse).  |
| 20   | run_i                             | input     | SW-triggered extra Keccak run during squeeze.       |
| 21   | absorbed_o (mubi4_t)              | output    | Absorbing is done (registered).                     |
| 22   | squeezing_o                       | output    | FSM is in the squeeze or manual-run state.          |
| 23   | block_processed_o                 | output    | One Keccak block processed (keccak_complete).       |
| 24   | sha3_fsm_o (sha3_st_e)            | output    | Decoded FSM state.                                  |
| 25   | state_valid_o                     | output    | Digest state is valid.                              |
| 26   | state_valid_hold_i                | input     | Holds state_valid_o while asserted.                 |
| 27   | state_o[Share][StateW-1:0]        | output    | Digest state; zero while not valid.                 |
| 28   | error_o (err_t)                   | output    | SW control error (ErrSha3SwControl).                |
| 29   | sparse_fsm_error_o                | output    | Sparse FSM error of the top, pad or Keccak FSM.     |
| 30   | count_error_o                     | output    | Round or message counter error.                     |
| 31   | keccak_storage_rst_error_o        | output    | Unexpected Keccak storage reset.                    |

abr_sha3 module is responsible for the following tasks:
1. Runs the top FSM StIdle -> StAbsorb -> StSqueeze <-> StManualRun, with zeroize returning it
   to StIdle and illegal sparse encodings trapped in StTerminalError
2. Passes the message to u_pad (abr_sha3pad), which pads it and feeds blocks to u_keccak
   (abr_keccak_round)
3. Filters the SW controls by state: start_i in StIdle, the first process_i in StAbsorb and run_i
   in StSqueeze
4. Raises state_valid_o on entry to StSqueeze, holds it with state_valid_hold_i, and guards
   state_o to zero while it is not valid
5. Reports illegal SW control signals on error_o and aggregates the sub-block FSM and counter
   errors on sparse_fsm_error_o, count_error_o and keccak_storage_rst_error_o

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the DUT. In
fv_abr_sha3_binding.sv, **rst** of fv_abr_sha3_m is bound to (!rst_b || zeroize), and the FSM
assertions are disabled with **disable iff (rst)**. The white-box assertions use
**disable iff (!pi_rst_b || pi_zeroize)**, where **pi_rst_b** is bound to `rst_b` and
**pi_zeroize** to `zeroize`. assert_sha3_process_reset and assert_state_flush are not disabled,
as they check the reset/zeroize behavior itself. JasperGold declares only `~rst_b` as reset.

### fv_abr_sha3_m.sv

The state conditions IDLE, ABSORB, SQUEEZE and RUN are bound to the sparse FSM register
`st` (StIdle_sparse, StAbsorb_sparse, StSqueeze_sparse, StManualRun_sparse). The `_1` variants
of a transition cover the case with state_valid_hold_i high, where state_valid_o must stay
stable.

Reset

- assert_sha3_process_reset: After reset/zeroize, the FSM is in IDLE and absorbed_o,
  squeezing_o and state_valid_o are low, with sha3_fsm_o reporting idle

State transitions

- assert_sha3_process_idle_to_idle / assert_sha3_process_idle_to_idle_1: Without start_i, the
  FSM stays in IDLE

- assert_sha3_process_idle_to_absorb / assert_sha3_process_idle_to_absorb_1: start_i moves the
  FSM from IDLE to ABSORB

- assert_sha3_process_absorb_to_absorb / assert_sha3_process_absorb_to_absorb_1: The FSM stays
  in ABSORB until the pad block reports absorbed

- assert_sha3_process_absorb_to_squeeze: Once absorbed, the FSM moves to SQUEEZE with
  absorbed_o, squeezing_o and state_valid_o high

- assert_sha3_process_squeeze_to_squeeze / assert_sha3_process_squeeze_to_squeeze_1: Without
  run_i, the FSM stays in SQUEEZE with squeezing_o high

- assert_sha3_process_squeeze_to_run / assert_sha3_process_squeeze_to_run_1: run_i moves the
  FSM from SQUEEZE to RUN

- assert_sha3_process_run_wait: The FSM stays in RUN with stable outputs until keccak_complete

- assert_sha3_process_run_to_squeeze: keccak_complete moves the FSM from RUN back to SQUEEZE with
  state_valid_o high

Liveness

- assert_sha3_process_idle_eventually_left / assert_sha3_process_squeeze_eventually_left: IDLE
  is left after start_i and SQUEEZE is left after run_i

- assert_sha3_process_absorb_eventually_left / assert_sha3_process_run_eventually_left: ABSORB
  and RUN are eventually left (s_eventually)

Consistency

- assert_sha3_process_consistency_onehot0_state: At most one of the IDLE, ABSORB, SQUEEZE, RUN
  conditions holds at a time

### fv_abr_sha3_whitebox.sv

Digest output

- assert_state_o: state_o is zero while state_valid_o is low or the FSM is in StIdle

- assert_state_flush: state_o is zero one cycle after reset or zeroize

Sub-block connections

- assert_padding_keccak_ready_i: u_pad.keccak_ready_i is high when u_keccak is ready and the FSM
  is not squeezing

- assert_keccak_process: keccak_process to u_pad is high only for the first process_i in
  StAbsorb

- assert_keccak_run: u_keccak.run_i is the pad's keccak_run_o or run_i in StSqueeze

- assert_block_processed_o: block_processed_o equals keccak_complete

SW control error (error_o)

- assert_sha3_sw_ctrl_err_***: error_o reports ErrSha3SwControl, with {run_i, process_i,
  start_i} as info, for the illegal controls of each state, where `***` is `idle`
  (process_i or run_i), `absorb` (start_i, run_i or a repeated process_i), `squeeze` (start_i or
  process_i) or `run` (any of them)

- assert_sha3_no_sw_ctrl_err: Outside these combinations, error_o is {valid 0, ErrNone, 0}

Error outputs

- assert_sha3_count_error_o: count_error_o is the OR of the round and message counter errors

- assert_sha3_sparse_fsm_error_o: sparse_fsm_error_o is high when the top FSM decodes to StError
  or the Keccak round or pad FSM reports a sparse FSM error

- assert_sha3_keccak_storage_rst_error_o: keccak_storage_rst_error_o equals the Keccak storage
  reset error

The bench has no explicit cover properties. JasperGold creates the related precondition and
witness covers at elaboration (`-create_related_covers`).

## Key Constraints

- assume_mode_i: mode_i is Shake

- assume_strength_i: strength_i is L128 or L256

- assume_masked_requires_masking_hw: With EN_MASKING = 0, masked_i stays low, as the masked
  Keccak path is not built for one share

- assume_rand_progress: rand_early_i or rand_valid_i is eventually asserted (free-running entropy
  source), so the masked Keccak FSM can make progress

- assume_process_i / assume_process_i_low / assume_process_i_pulse: process_i is a pulse, only in
  StAbsorb and only after at least one accepted message beat (counted by lubis_incr_counter_m,
  21 beats for L128 and 17 for L256)

- assume_process_fairness: After msg_start_i, process_i is eventually asserted

- assume_msg_valid_after_process_i: After process_i, no message is valid until the next
  msg_start_i

- assume_no_msgs_after_partial: After an accepted partial beat, no message is valid until the
  next start_i

- assume_no_bubbles: msg_strb_i is contiguous from bit 0

- assume_start_i_pulse / assume_msg_start_i_pulse / assume_msg_start_i_after_start_i: start_i
  and msg_start_i are pulses, and msg_start_i follows start_i by one cycle

- assume_no_msg_at_start / assume_no_several_starts: No message is valid with msg_start_i, and no
  new msg_start_i until absorbed_o

- assume_stable_strength_i: strength_i is stable except at msg_start_i

- assume_run_i_during_hold: No run_i while state_valid_o and state_valid_hold_i are high

## Coverage

- **fv_abr_sha3_cov_waivers.tcl**: The coverage of this bench is signed off for the top module
  only. The file waives the u_pad and u_keccak instances, which are covered by their own
  benches. Source it after elaboration in both masking setups. The proofs still run on the full
  design; the waivers only affect `check_cov`.

- **waiver_list_done_i_disabled.tcl**: A JasperGold GUI-exported waiver list for an earlier RTL
  version. Besides u_pad and u_keccak, it waives abr_prim_mubi_pkg, abr_sha3_pkg, u_state_regs
  and line-based branch/statement items, using absolute source paths and line numbers of that
  version. It is not needed for the current RTL.

- **Masking coverage merge**: `EnMasking` is an elaboration parameter, so the EN_MASKING = 0 and
  1 netlists are measured in separate sessions. The coverage databases of both sessions are
  exported and merged into one report. Check the merged item counts against the two
  per-configuration reports, since the cross-netlist merge is not fully verified.

## Formal Setup
Use top `abr_sha3`, clock `clk_i`, reset `~rst_b` and define `DISABLE_DONE_SIGNAL`. Use one setup per
masking configuration (`EnMasking = 0` and `EnMasking = 1`).

This AIP instantiates the LUBIS library module `lubis_incr_counter_m`, which is not part of this
repository.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
