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

# ntt_top

## Folder Structure
The following files are part of the main directory **formal/fv_ntt_top**


- **fv_ntt_top_mlkem.sv** contains the assertions for ntt_top module

- **fv_ntt_top_mlkem_internal.sv** contains the assertions for internal submodules of ntt_top
  such ass hybrid_bfu_2x2, ntt_ctrl, etc.

- **fv_ntt_top_mlkem_constraints.sv** contains the assumptions/constraints for ntt_top 

- **fv_ntt_top_mlkem_top.sv** is the wrapper file.

## DUT Overview

The DUT has the primary inputs and primary outputs as shown below.

| S.No | Port                         | Direction | Description                                  |
| ---- | ---------------------------- | --------- | -------------------------------------------- |
| 1    | clk                          | input     | Positive edge samples all signals.           |
| 2    | reset_n                      | input     | Active-low reset; resets the module.         |
| 3    | zeroize                      | input     | Resets the module when asserted.             |
| 4    | mode                         | input     | NTT mode select (ct/gs/pwm/pwa/pws/pairwm).  |
| 5    | ntt_enable                   | input     | Enables the NTT operation.                   |
| 6    | sampler_valid                | input     | Sampler valid from abr_ctrl (pwo mode only). |
| 7    | accumulate                   | input     | Selects the accumulate case.                 |
| 8    | ntt_mem_base_addr[2:0][13:0] | input     | NTT src/dest/interim base addrs, 14b each.   |
| 9    | pwo_mem_base_addr[2:0][13:0] | input     | PWO base addrs a/b/c, 14b each.              |
| 10   | shuffle_en                   | input     | Enables the shuffling operation.             |
| 11   | random[5:0]                  | input     | Randomizes chunk/index selection.            |
| 12   | mlkem                        | input     | Enables MLKEM operation.                     |
| 13   | mem_rd_data[95:0]            | input     | Memory read data (NTT).                      |
| 14   | mem_rd_data_valid            | input     | Read ack, SRAM_LATENCY cycles after request. |
| 15   | pwm_a_rd_data[95:0]          | input     | Memory read data a (PWO).                    |
| 16   | pwm_b_rd_data[95:0]          | input     | Memory read data b (PWO).                    |
| 17   | mem_wr_req                   | output    | Memory write request enable/address (NTT).   |
| 18   | mem_rd_req                   | output    | Memory read request enable/address (NTT).    |
| 19   | pwm_a_rd_req                 | output    | Memory read request enable/address (PWM a).  |
| 20   | pwm_b_rd_req                 | output    | Memory read request enable/address (PWM b).  |
| 21   | mem_wr_data[95:0]            | output    | Memory write data.                           |
| 22   | ntt_busy                     | output    | Busy indicator.                              |
| 23   | ntt_done                     | output    | Done indicator.                              |


ntt_top module is responsible for the following tasks:
1. Keeps track of stages of bf2x2 operation
2. Reads appropriate addr of ROM and passes w input to bf2x2
3. Orchestrates memory writes and reads and passes u and v inputs to bf2x2
4. Controls direct PWM inputs to bf2x2 in pwm mode
5. Maintains mode input to bf2x2 and related input/output muxes
6. Aligns data and control delays associated with bf2x2 module

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut, where for the
**rst_n** is bound with the DUT (reset_n && !zeroize), which ensures the reset functionality.

- assert_check_po_pwm_a_rd_req: Property to check request outputs for pwo modes
  (masking-independent since masking support was removed)

- assert_check_po_pwm_a_rd_req_no_pwo: Property to check that when not in pwo mode,
  po_pwm_a_rd_req has no read request and its address is zero

- assert_check_po_pwm_a_rd_req_no_ongoing: Property to check if nothing is ongoing then no read
  request.

- assert_check_po_pwm_b_rd_req_no_shuffle: Property to check req b when the shuffle is disabled

- assert_po_pwm_b_rd_req_shuffle: Property to check req b when the shuffling is enabled

- assert_no_p_mode_no_req: Property to check if the mode is not pwo then no read request.

- assert_mem_wr_req_ct_no_shuffle: Property to check write req and addr for ct mode when shuffle
  is disabled

- assert_mem_wr_req_ct_shuffle: Property to check write req and addr for ct mode when shuffle is
  enabled

- assert_mem_wr_req_gs : Property to check write req and addr for gs mode

- assert_mem_wr_req_pwo: Property to check write req and addr for pwo mode

- assert_mem_wr_data_ct: Property to check for wr_data output during ct_mode and wr_req is write

- assert_mem_wr_data_gs: Property to check for wr_data output during gs_mode and wr_req is write

- assert_mem_wr_data_pwm_pwa_pws: Property to check for wr_data output during pwo mode
  (pwm/pairwm/pwa/pws)

- assert_check_pwm_b_rd_data_reg_reset: Property to check pwm_b_rd_data_reg is zero during reset

- assert_check_mem_rd_req_ct_gs: Property to check read enable and addr for ct or gs mode

- assert_check_mem_rd_req_pwm_dest_mem: Property to check read enable and addr for pwm/pairwm
  mode, based on ntt_ctrl_inst0.pw_rden_dest_mem

- assert_mem_rd_req_other: Property to check read enable and addr are idle/zero for other modes
  when not in ct, gs or pwm/pairwm mode

- assert_num_rd_always_64: Property to check that mem_rd_en is always asserted 64-cycle long

- assert_num_wr_always_64: Property to check that mem_wr_en is always asserted 64-cycle long

- assert_num_pwrd_always_64: Property to check that pw_rden is always asserted 64-cycle long
  until done signal is asserted

- assert_num_pwwr_always_64: Property to check that pw_wren is always asserted 64-cycle long
  until done signal is asserted

- assert_busy_eventually_not_busy: Property to check liveness condition of ntt_busy output signal

- assert_cmd_ctrl_done_to_output: Connection check for cmd_ctrl done to ntt_done

- assert_cmd_ctrl_busy_to_output: Connection check for cmd_ctrl busy to ntt_busy

- assert_correct_cmd_ctrl_input_***: Assertions to check connectivity of command control inputs,
  including mem_rd_data_valid

- assert_correct_butterfly_input_opcode / shuffle_en / mlkem / accumulate / ntt_passthrough /
  intt_passthrough / enable_ct / enable_non_ct: Assertions to check connectivity of butterfly
  inputs

- assert_correct_butterfly_input_enable_bf: Aux-signal-based equivalent of
  enable_ct/enable_non_ct - checks hybrid_bf2x2.enable against an fv_bf_enable shadow register
  (same-cycle bf_enable in ct mode, 1-cycle delayed otherwise)

- assert_pi_mode_ct_assignment: Assertion to check uvw_i w input assignments on ct_mode

- assert_pi_mode_gs_pwm_intt_shuffle: Assertion to check uvw_i w input assignments on gs_mode &
  shuffling enabled

- assert_pi_mode_gs_pwm_intt_no_shuffle: Assertion to check uvw_i w input assignments on gs_mode
  & shuffling disabled

- assert_pi_mode_default_assignment: Assertion to check uvw_i w input assignments on other modes

- assert_mlkem_pairwm_zeta: Assertion to check mlkem_pairwm_zeta13_i inputs assignments in
  pairwm mode (masking terms removed)

- assert_no_mlkem_pairwm_zeta: Assertion to check mlkem_pairwm_zeta13_i inputs assignments are
  zero when not in pairwm mode

- assert_check_uvw_assignment_ct: Assertion to check uvw_i u & v & pw_uvw_i input assignments
  for ct mode

- assert_check_uvw_assignment_gs: Assertion to check uvw_i u & v & pw_uvw_i input assignments
  for gs mode

- assert_check_pw_uvw_assignment_pwm: Assertion to check uvw_i & pw_uvw_i input assignments
  during pwm mode / pairwm mode

- assert_check_pw_uvw_assignment_pwa_pws: Assertion to check uvw_i & pw_uvw_i input assignments
  for pwa or pws mode

- assert_check_zero_uvw_default: Assertions for Default Case (Zeroing Out) of uvw_i

- assert_check_zero_pw_uvw_default: Assertions for Default Case (Zeroing Out) of pw_uvw_i

- assert_check_pwo_regs_reset: Property to check pw_rden_reg, pw_mem_rd_addr_a_reg,
  pw_mem_rd_addr_b_reg, w10_reg and w11_reg are zero during reset/zeroize

- assert_correct_buffer_input_***: Shuffle Buffer connectivity checks

- assert_correct_twiddle_rom_input_addr / mode / mlkem: Connectivity checks for the twiddle
  ROM's own read address, mode, and mlkem inputs

- assert_check_ct_mode_reg / gs_mode_reg / pwm_mode_reg / pwa_mode_reg / pws_mode_reg /
  pairwm_mode_reg / pwo_mode_reg : Register-connectivity checks for the one-cycle-delayed mode
  flags, including the reset/zeroize override

- assert_check_uv_o_reg (CT-001 refinement): Register-connectivity check for the uv_o ->
  uv_o_reg one-cycle link

- assert_check_buf_array_write / assert_check_buf_array_read : End-to-end transit-correctness
  checks through ntt_shuffle_buffer's internal buffer array, proving a coefficient written at
  (lo_hi, wrptr) matches what data_o produces when read at the matching rdptr

## Key Constraints

- assume_stable_mode: keeps pi_mode, pi_shuffle_en, pi_mlkem, pi_accumulate and the base
  addresses stable while an operation is ongoing (the pi_masking_en stability clause was removed
  - the signal is no longer driven)

- assume_mem_rd_data_valid_latency: models the memory's fixed read latency by asserting
  pi_mem_rd_data_valid exactly SRAM_LATENCY cycles after a read request on po_mem_rd_req,
  matching abr_top.sv's ntt_mem_rd_data_valid generation

- assume_ntt_enable_not_while_ongoing: prevents re-enabling ntt while an operation is already
  ongoing unless done is asserted

- assume_valid_base_address: constrains the source/destination/interim base addresses to be
  aligned and sufficiently spaced apart

- assume_sampler_valid / assume_sampler_valid_duration: force sampler_valid to eventually assert
  and hold for 64 cycles once raised

- assume_busy_not_busy: ensures the busy signal is eventually deasserted once an operation is
  ongoing

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
