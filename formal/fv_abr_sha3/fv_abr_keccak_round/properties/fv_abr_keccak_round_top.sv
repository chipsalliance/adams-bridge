// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+


import fv_abr_keccak_round_pkg::*;
import fv_abr_keccak_round_functions::*;


module fv_abr_keccak_round_top #(
  // Must match the DUT's EnMasking parameter. Gates elaboration of the
  // masked-FSM (Phase1/Phase2CycleN) assertions/liveness/covers below: with
  // EN_MASKING=0 those states are unreachable (see
  // fv_abr_keccak_round_constraints.sv:gen_no_masking_hw), so the
  // implication-form asserts would only ever report vacuous passes and their
  // paired covers would report uncovered/fail -- neither is a real check in
  // that build, so skip generating them instead of reporting noise.
  parameter bit EN_MASKING = 1'b1
)(
  input logic rst,
  input logic clk,

  // Ports
  input logic data_in_vld,
  input logic data_in_rdy,
  input logic unsigned [1599:0] data_in,
  input logic unsigned [1599:0] data_in_1,

  input logic clear_in,

  input logic masked_in,
  input logic squeezing_in,

  input logic unsigned [1599:0] state_out,
  input logic unsigned [1599:0] state_out_1,

  input logic complete_out,

  input logic rand_valid_in,
  input logic rand_early_in,
  input logic rand_aux_in,
  input logic rand_update_out,
  input logic rand_consumed_out,

  input logic sparse_fsm_error_out,

  input logic round_count_error_out,

  input logic rst_storage_error_out,

  // Registers
  input logic signed [31:0] round_idx,
  input logic unsigned [1599:0] storage,
  input logic unsigned [1599:0] storage_1,

  // States
  input logic waiting_for_input,
  input logic round_state,
  input logic phase1_state,
  input logic phase2cycle1_state,
  input logic phase2cycle2_state,
  input logic phase2cycle3_state
);


default clocking default_clk @(posedge clk); endclocking


///////////////////////////////////////////////
// Unmasked reference model (2 rounds/cycle) //
///////////////////////////////////////////////

fv_a_a_unsigned_64_5_5_type fv_string_to_state_0_i;
assign fv_string_to_state_0_i = string_to_state(storage);

fv_a_a_unsigned_64_5_5_type fv_theta_0_i;
assign fv_theta_0_i = theta(fv_string_to_state_0_i);

fv_a_a_unsigned_64_5_5_type fv_rho_0_i;
assign fv_rho_0_i = rho(fv_theta_0_i);

fv_a_a_unsigned_64_5_5_type fv_pi_0_i;
assign fv_pi_0_i = pi(fv_rho_0_i);

fv_a_a_unsigned_64_5_5_type fv_chi_0_i;
assign fv_chi_0_i = chi(fv_pi_0_i);

fv_a_a_unsigned_64_5_5_type fv_iota_0_i;
assign fv_iota_0_i = iota(fv_chi_0_i, (round_idx + 0));

fv_a_a_unsigned_64_5_5_type fv_theta_1_i;
assign fv_theta_1_i = theta(fv_iota_0_i);

fv_a_a_unsigned_64_5_5_type fv_rho_1_i;
assign fv_rho_1_i = rho(fv_theta_1_i);

fv_a_a_unsigned_64_5_5_type fv_pi_1_i;
assign fv_pi_1_i = pi(fv_rho_1_i);

fv_a_a_unsigned_64_5_5_type fv_chi_1_i;
assign fv_chi_1_i = chi(fv_pi_1_i);

fv_a_a_unsigned_64_5_5_type fv_iota_1_i;
assign fv_iota_1_i = iota(fv_chi_1_i, (round_idx + 1));

logic unsigned [1599:0] fv_state_to_string_0_i;
assign fv_state_to_string_0_i = state_to_string(fv_iota_1_i);


/////////////////////////////////////////////////////////////////////
// Masked reference model (1 round/4 cycles, shares XOR-recombined) //
/////////////////////////////////////////////////////////////////////
// Theta/Rho/Pi are linear over GF(2) and Chi/Iota are applied to the
// XOR-recombination of the two shares, so a single application of the
// existing unmasked step functions to the recombined state is the correct
// per-round reference for the masked datapath too.

function automatic logic unsigned [1599:0] combine_shares(
  logic unsigned [1599:0] share0,
  logic unsigned [1599:0] share1
);
  return share0 ^ share1;
endfunction

logic unsigned [1599:0] fv_storage_combined;
assign fv_storage_combined = combine_shares(storage, storage_1);

logic unsigned [1599:0] fv_state_out_combined;
assign fv_state_out_combined = combine_shares(state_out, state_out_1);

logic unsigned [1599:0] fv_data_in_combined;
assign fv_data_in_combined = combine_shares(data_in, data_in_1);

fv_a_a_unsigned_64_5_5_type fv_m_string_to_state_i;
assign fv_m_string_to_state_i = string_to_state(fv_storage_combined);

fv_a_a_unsigned_64_5_5_type fv_m_theta_i;
assign fv_m_theta_i = theta(fv_m_string_to_state_i);

fv_a_a_unsigned_64_5_5_type fv_m_rho_i;
assign fv_m_rho_i = rho(fv_m_theta_i);

fv_a_a_unsigned_64_5_5_type fv_m_pi_i;
assign fv_m_pi_i = pi(fv_m_rho_i);

fv_a_a_unsigned_64_5_5_type fv_m_chi_i;
assign fv_m_chi_i = chi(fv_m_pi_i);

fv_a_a_unsigned_64_5_5_type fv_m_iota_i;
assign fv_m_iota_i = iota(fv_m_chi_i, round_idx);

logic unsigned [1599:0] fv_m_state_to_string_i;
assign fv_m_state_to_string_i = state_to_string(fv_m_iota_i);


////////////////////
// Reset behavior //
////////////////////

// After reset (rst was high last cycle), the FSM lands in the idle state
// with all status outputs, error flags, and storage/state registers cleared,
// and the module ready to accept new input.
property fsm_reset_p;
  $past(rst)
|->
  waiting_for_input &&
  complete_out == 0 &&
  rand_consumed_out == 0 &&
  rand_update_out == 0 &&
  round_count_error_out == 0 &&
  round_idx == 0 &&
  rst_storage_error_out == 0 &&
  sparse_fsm_error_out == 0 &&
  state_out == 1600'd0 &&
  state_out_1 == 1600'd0 &&
  storage == 1600'd0 &&
  storage_1 == 1600'd0 &&
  data_in_rdy == 1;
endproperty
assert_keccak_round_fsm_reset: assert property (fsm_reset_p);


///////////////////////////////
// Unmasked round processing //
///////////////////////////////

// Mid-operation (more than 2 rounds remain): each round_state cycle applies
// one two-round step of the unmasked reference model (theta/rho/pi/chi/iota
// applied twice) to storage, advances round_idx by 2, and holds all status
// outputs stable with data_in_rdy low.
property fsm_round_state_to_round_state_p;
  round_state &&
  ((2 + round_idx) < 24)
|->
  ##1 ($stable(complete_out)) and
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  round_idx == (2 + $past(round_idx, 1)) &&
  state_out == $past(fv_state_to_string_0_i, 1) &&
  storage == $past(fv_state_to_string_0_i, 1);
endproperty
assert_keccak_round_round_state_to_round_state: assert property (disable iff(rst) fsm_round_state_to_round_state_p);


// Terminating case (round_idx + 2 >= 24): the same two-round step is
// applied, but the FSM then returns to waiting_for_input, reports
// complete_out, resets round_idx to 0, and re-opens data_in_rdy.
property fsm_round_state_to_waiting_for_input_p;
  round_state &&
  ((2 + round_idx) >= 24)
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1
  waiting_for_input &&
  complete_out == 1 &&
  round_idx == 0 &&
  state_out == $past(fv_state_to_string_0_i, 1) &&
  storage == $past(fv_state_to_string_0_i, 1) &&
  data_in_rdy == 1;
endproperty
assert_keccak_round_round_state_to_waiting_for_input: assert property (disable iff(rst) fsm_round_state_to_waiting_for_input_p);


// Absorbing new (unmasked, non-squeezing) input XORs it into storage/
// state_out and moves the FSM into round_state to begin processing.
property fsm_waiting_for_input_to_round_state_p;
  waiting_for_input &&
  !masked_in &&
  !clear_in &&
  data_in_vld &&
  !squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  state_out == ($past(storage, 1) ^ $past(data_in, 1)) &&
  storage == ($past(storage, 1) ^ $past(data_in, 1));
endproperty
assert_keccak_round_waiting_for_input_to_round_state: assert property (disable iff(rst) fsm_waiting_for_input_to_round_state_p);


// During squeezing, new input is accepted but not absorbed (storage/
// state_out stay stable) -- the FSM still advances to round_state to
// produce the next output block.
property fsm_waiting_for_input_to_round_state_1_p;
  waiting_for_input &&
  !masked_in &&
  !clear_in &&
  data_in_vld &&
  squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 ($stable(state_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  round_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  $stable(storage);
endproperty
assert_keccak_round_waiting_for_input_to_round_state_1: assert property (disable iff(rst) fsm_waiting_for_input_to_round_state_1_p);


/////////////////////////////
// Masked round processing //
/////////////////////////////
// Gated on EN_MASKING: with EN_MASKING=0 phase1_state/phase2cycleN_state are
// unreachable (masked_i is forced 0, see gen_no_masking_hw in
// fv_abr_keccak_round_constraints.sv), so these implication-form properties
// would only ever report a vacuous pass in that build.

if (EN_MASKING) begin : gen_masked_fsm_checks

// Masked-path equivalent of assert_keccak_round_waiting_for_input_to_round_state:
// absorbing (non-squeezing) input XORs it into the combined
// (XOR-recombined) storage/state_out and moves the FSM into phase1_state.
property fsm_waiting_for_input_to_phase1_p;
  waiting_for_input &&
  masked_in &&
  !clear_in &&
  data_in_vld &&
  !squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 (data_in_rdy == 0) and
  ##1
  phase1_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  fv_state_out_combined == ($past(fv_storage_combined, 1) ^ $past(fv_data_in_combined, 1)) &&
  fv_storage_combined == ($past(fv_storage_combined, 1) ^ $past(fv_data_in_combined, 1));
endproperty
assert_keccak_round_waiting_for_input_to_phase1: assert property (disable iff(rst) fsm_waiting_for_input_to_phase1_p);


// Masked-path equivalent of assert_keccak_round_waiting_for_input_to_round_state_1:
// during squeezing, input is accepted without being absorbed into the
// combined storage, and the FSM advances to phase1_state.
property fsm_waiting_for_input_to_phase1_1_p;
  waiting_for_input &&
  masked_in &&
  !clear_in &&
  data_in_vld &&
  squeezing_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 ($stable(fv_state_out_combined)) and
  ##1 (data_in_rdy == 0) and
  ##1
  phase1_state &&
  complete_out == 0 &&
  round_idx == 0 &&
  $stable(fv_storage_combined);
endproperty
assert_keccak_round_waiting_for_input_to_phase1_1: assert property (disable iff(rst) fsm_waiting_for_input_to_phase1_1_p);


// Phase1 holds until the DOM multipliers are guaranteed fresh randomness for
// Phase2 (rand_early_in signals it will be available next cycle, rand_valid_in
// signals it already is).
property fsm_phase1_stall_p;
  phase1_state &&
  !(rand_early_in || rand_valid_in)
|->
  ##1
  phase1_state &&
  $stable(fv_storage_combined) &&
  $stable(round_idx) &&
  data_in_rdy == 0;
endproperty
assert_keccak_round_phase1_stall: assert property (disable iff(rst) fsm_phase1_stall_p);


// Phase1 -> Phase2Cycle1 -> Phase2Cycle2 -> Phase2Cycle3 always advances in
// lock-step, one state per cycle, once Phase1 is left. After the full 4-cycle
// sequence, the XOR-recombination of the two shares equals one Keccak round
// (theta/rho/pi/chi/iota) applied to the recombination sampled when Phase1
// was left, matching FIPS 202 Rnd(A, i_r) for the masked datapath.
property fsm_phase1_to_next_round_p;
  phase1_state &&
  (rand_early_in || rand_valid_in)
|->
  ##1 (phase2cycle1_state && data_in_rdy == 0)
  ##1 (phase2cycle2_state && data_in_rdy == 0)
  ##1 (phase2cycle3_state && data_in_rdy == 0)
  ##1 (
    fv_storage_combined == $past(fv_m_state_to_string_i, 4) &&
    fv_state_out_combined == $past(fv_m_state_to_string_i, 4) &&
    round_idx == (($past(round_idx, 4) == 23) ? 0 : ($past(round_idx, 4) + 1)) &&
    complete_out == ($past(round_idx, 4) == 23) &&
    (($past(round_idx, 4) == 23) ? waiting_for_input : phase1_state) &&
    data_in_rdy == (($past(round_idx, 4) == 23) ? 1 : 0)
  );
endproperty
assert_keccak_round_phase1_to_next_round: assert property (disable iff(rst) fsm_phase1_to_next_round_p);

end : gen_masked_fsm_checks


// rand_update_out/rand_consumed_out are pure functions of the masked FSM
// state (see abr_keccak_round.sv: keccak_rand_update/keccak_rand_consumed).
property rand_update_correct_p;
  rand_update_out ==
    (phase2cycle1_state || phase2cycle2_state ||
     (phase1_state && (rand_early_in || rand_valid_in)));
endproperty
assert_keccak_round_rand_update_correct: assert property (disable iff(rst) rand_update_correct_p);

property rand_consumed_correct_p;
  rand_consumed_out == phase2cycle2_state;
endproperty
assert_keccak_round_rand_consumed_correct: assert property (disable iff(rst) rand_consumed_correct_p);


//////////////////////////////////////
// Shared idle / liveness behavior //
//////////////////////////////////////

// clear_in returns the FSM to a fully-zeroed idle state without consuming
// any input, regardless of data_in_vld.
property fsm_waiting_for_input_to_waiting_for_input_p;
  waiting_for_input &&
  clear_in
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1
  waiting_for_input &&
  complete_out == 0 &&
  $stable(round_idx) &&
  state_out == 1600'd0 &&
  state_out_1 == 1600'd0 &&
  storage == 1600'd0 &&
  storage_1 == 1600'd0 &&
  data_in_rdy == 1;
endproperty
assert_keccak_round_waiting_for_input_to_waiting_for_input: assert property (disable iff(rst) fsm_waiting_for_input_to_waiting_for_input_p);


// With no clear_in and no data_in_vld, the FSM simply idles: round_idx,
// storage/state_out, and all error flags hold stable, and data_in_rdy
// stays asserted.
property fsm_waiting_for_input_to_waiting_for_input_1_p;
  waiting_for_input &&
  !clear_in &&
  !data_in_vld
|->
  ##1 ($stable(rand_consumed_out)) and
  ##1 ($stable(round_count_error_out)) and
  ##1 ($stable(rst_storage_error_out)) and
  ##1 ($stable(sparse_fsm_error_out)) and
  ##1 ($stable(state_out)) and
  ##1 ($stable(state_out_1)) and
  ##1
  waiting_for_input &&
  complete_out == 0 &&
  $stable(round_idx) &&
  $stable(storage) &&
  $stable(storage_1) &&
  data_in_rdy == 1;
endproperty
assert_keccak_round_waiting_for_input_to_waiting_for_input_1: assert property (disable iff(rst) fsm_waiting_for_input_to_waiting_for_input_1_p);


// Liveness: the FSM does not get stuck waiting for input forever --
// guaranteed by assume_run_i (fv_abr_keccak_round_constraints.sv), which
// promises the environment eventually drives run_i with a genuine clear.
property fsm_waiting_for_input_eventually_left_p;
  waiting_for_input
|->
  s_eventually(!waiting_for_input);
endproperty
assert_keccak_round_waiting_for_input_eventually_left: assert property (disable iff(rst) fsm_waiting_for_input_eventually_left_p);


// Liveness: round_state is always eventually left -- the round pipeline
// can't stall indefinitely (assert_keccak_round_round_state_to_round_state/
// assert_keccak_round_round_state_to_waiting_for_input together cover every exit).
property fsm_round_state_eventually_left_p;
  round_state
|->
  s_eventually(!round_state);
endproperty
assert_keccak_round_round_state_eventually_left: assert property (disable iff(rst) fsm_round_state_eventually_left_p);


// Gated on EN_MASKING: with EN_MASKING=0 these states never hold, so the
// liveness implications below would only ever report a vacuous pass.
if (EN_MASKING) begin : gen_masked_liveness_checks

// Liveness: Phase1 is always eventually left -- guaranteed by
// assume_rand_progress (fv_abr_keccak_round_constraints.sv), which promises
// rand_early_in/rand_valid_in eventually assert (see assert_keccak_round_phase1_stall/
// assert_keccak_round_phase1_to_next_round for the corresponding transitions).
property fsm_phase1_eventually_left_p;
  phase1_state
|->
  s_eventually(!phase1_state);
endproperty
assert_keccak_round_phase1_eventually_left: assert property (disable iff(rst) fsm_phase1_eventually_left_p);


// Liveness: once entered, Phase2Cycle1 is always eventually left -- it's an
// unconditional one-cycle step to Phase2Cycle2 (assert_keccak_round_phase1_to_next_round).
property fsm_phase2cycle1_eventually_left_p;
  phase2cycle1_state
|->
  s_eventually(!phase2cycle1_state);
endproperty
assert_keccak_round_phase2cycle1_eventually_left: assert property (disable iff(rst) fsm_phase2cycle1_eventually_left_p);


// Liveness: same guarantee, one step later -- Phase2Cycle2 is always
// eventually left, advancing unconditionally to Phase2Cycle3.
property fsm_phase2cycle2_eventually_left_p;
  phase2cycle2_state
|->
  s_eventually(!phase2cycle2_state);
endproperty
assert_keccak_round_phase2cycle2_eventually_left: assert property (disable iff(rst) fsm_phase2cycle2_eventually_left_p);


// Liveness: same guarantee for the final cycle -- Phase2Cycle3 is always
// eventually left, landing back in Phase1 (next round) or waiting_for_input
// (operation complete).
property fsm_phase2cycle3_eventually_left_p;
  phase2cycle3_state
|->
  s_eventually(!phase2cycle3_state);
endproperty
assert_keccak_round_phase2cycle3_eventually_left: assert property (disable iff(rst) fsm_phase2cycle3_eventually_left_p);

end : gen_masked_liveness_checks


localparam CONSISTENCY = 1;
if (CONSISTENCY) begin : gen_consistency_check
  // Check that no more than 1 state condition is met at the same time
  assert_keccak_round_consistency_onehot0_state: assert property($onehot0({
    round_state,
    waiting_for_input,
    phase1_state,
    phase2cycle1_state,
    phase2cycle2_state,
    phase2cycle3_state
  }));
end : gen_consistency_check


///////////////////////////////////////////////////////////////
// Coverage: is the randomness handshake actually exercised?  //
///////////////////////////////////////////////////////////////
// assert_keccak_round_phase1_eventually_left's liveness depends entirely on
// rand_early_in/rand_valid_in asserting while phase1_state holds. These covers
// confirm the proof environment can actually reach that condition, rather
// than the liveness result being vacuous because rand_early_in/rand_valid_in
// (or the Phase1 state itself) are never reachable in the first place.
//
// Gated on EN_MASKING: with EN_MASKING=0 phase1_state is unreachable, so
// these would report uncovered/fail rather than a meaningful coverage result.
if (EN_MASKING) begin : gen_masked_coverage

// rand_early_in alone can be seen during Phase1.
cover_phase1_rand_early_in_c: cover property (
  disable iff(rst) phase1_state && rand_early_in
);

// rand_valid_in alone can be seen during Phase1.
cover_phase1_rand_valid_in_c: cover property (
  disable iff(rst) phase1_state && rand_valid_in
);

// The actual transition-enabling condition (either signal high) is reached.
cover_phase1_rand_progress_c: cover property (
  disable iff(rst) phase1_state && (rand_early_in || rand_valid_in)
);

// Phase1 is left specifically via the randomness condition, landing in
// Phase2Cycle1 the following cycle -- i.e. the transition itself fires, not
// just its enabling condition.
cover_phase1_leaves_via_rand_c: cover property (
  disable iff(rst) phase1_state && (rand_early_in || rand_valid_in) ##1 phase2cycle1_state
);

// Phase1 can also stall for more than one cycle (rand not yet available) --
// confirms the stall path is reachable, not just the immediate-grant path.
// If this is unreachable, rand_early_in/rand_valid_in are effectively forced
// high on entry in every reachable trace, which would make the liveness
// property trivial rather than a real check of the fairness assumption.
cover_phase1_stalls_multi_cycle_c: cover property (
  disable iff(rst) phase1_state ##1 phase1_state ##1 phase1_state
);

end : gen_masked_coverage


endmodule
