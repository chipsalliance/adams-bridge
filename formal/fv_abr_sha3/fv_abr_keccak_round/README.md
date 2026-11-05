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

# abr_keccak_round

## Folder Structure
The following files are part of the main directory **formal/fv_abr_sha3/fv_abr_keccak_round**

- **model/abr_sha3_round.h** is the C++/SystemC untimed reference model of the unmasked Keccak
  round (Keccak-f[1600], 24 rounds, `ROUNDS_PER_CLOCK` = 2) from which the properties were
  derived: string/state conversion, theta/rho/pi/chi/iota and the idle/round FSM.

- **properties/fv_abr_keccak_round_pkg.sv** contains the shared lane/state array typedefs
  (`fv_a_a_unsigned_64_5_5_type` etc.).

- **properties/fv_abr_keccak_round_functions.sv** contains the reference step functions
  (`string_to_state`, `state_to_string`, `theta`, `rho`, `pi`, `chi`, `iota`, `rotate_left`)
  used as the round oracle.

- **properties/fv_abr_keccak_round_top.sv** contains the assertions and covers for the
  abr_keccak_round module (unmasked and masked datapath).

- **properties/fv_abr_keccak_round_constraints.sv** contains the assumptions/constraints and the
  covers checking that the randomness fairness assumption is exercised.

- **properties/fv_abr_keccak_round_binding.sv** is the wrapper file. It binds the
  `fv_abr_keccak_round_share_bridge` helper (extracts share 1 of `data_i`/`state_o`/`storage`
  when `EnMasking=1`, ties it to 0 otherwise) and `fv_abr_keccak_round_top` into
  `abr_keccak_round`.

## DUT Overview

The DUT is elaborated with `Width=1600`, `RoundsPerClock=2` and `EnMasking=1` (so
`Share=2`). It has the primary inputs and primary outputs as shown below.

| S.No | Port                   | Direction | Description                                            |
| ---- | ---------------------- | --------- | ------------------------------------------------------ |
| 1    | clk_i                  | input     | Positive edge samples all signals.                     |
| 2    | rst_b                  | input     | Active-low reset; resets the module.                   |
| 3    | zeroize                | input     | Resets the module when asserted.                       |
| 4    | data_i[Share][1599:0]  | input     | Message block (per share) XORed into the state.        |
| 5    | ready_o                | output    | Idle, ready to accept a new run.                       |
| 6    | run_i                  | input     | Pulse that starts a full 24-round permutation.         |
| 7    | masked_i               | input     | Selects the masked (DOM two-share) datapath.           |
| 8    | squeezing_i            | input     | Squeezing run: permute without absorbing data_i.       |
| 9    | rand_valid_i           | input     | External randomness is valid.                          |
| 10   | rand_early_i           | input     | External randomness will be valid next cycle.          |
| 11   | rand_data_i[799:0]     | input     | External randomness for the DOM multipliers.           |
| 12   | rand_aux_i             | input     | Aux random bit: which lane halves are processed first. |
| 13   | rand_update_o          | output    | Requests a randomness update from the PRNG.            |
| 14   | rand_consumed_o        | output    | Randomness has been consumed.                          |
| 15   | complete_o             | output    | Full permutation (all rounds) is done.                 |
| 16   | state_o[Share][1599:0] | output    | Keccak state (per share), usable as digest.            |
| 17   | sparse_fsm_error_o     | output    | FSM state is not a valid sparse encoding.              |
| 18   | round_count_error_o    | output    | Round counter (abr_prim_count) consistency error.      |
| 19   | rst_storage_error_o    | output    | Storage reset asserted outside the permitted window.   |
| 20   | clear_i                | input     | mubi4 clear; MuBi4True clears the internal state to 0. |

abr_keccak_round module is responsible for the following tasks:
1. Absorbs `data_i` into the internal state on `run_i` (skipped when `squeezing_i` is set) and
   clears the state on `clear_i`
2. Unmasked datapath (`masked_i=0`): computes `RoundsPerClock`=2 full Keccak rounds
   (theta/rho/pi/chi/iota) per cycle in `KeccakStActive`
3. Masked datapath (`masked_i=1`): computes one round per 4 cycles on two shares,
   `KeccakStPhase1 -> KeccakStPhase2Cycle1 -> KeccakStPhase2Cycle2 -> KeccakStPhase2Cycle3`,
   with domain-oriented masking (DOM) for chi (see the KMAC theory of operation,
   https://opentitan.org/book/hw/ip/kmac/doc/theory_of_operation.html)
4. Stalls Phase1 until randomness is available and drives the `rand_update_o`/`rand_consumed_o`
   handshake with the PRNG
5. Signals `complete_o` and returns to idle (`ready_o`) after the last round
6. Reports sparse FSM, round counter and storage reset errors

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the DUT, where **rst** is
bound with (!rst_b || zeroize), which ensures the reset functionality. All transition, handshake
and liveness assertions use `disable iff(rst)`; the reset assertion checks the state the cycle
after `rst`. In JasperGold, `~rst_b` and `zeroize` are declared as resets. `clear_in` is bound
to `clear_i == MuBi4True` (4'h6), and the FSM state flags (`waiting_for_input`, `round_state`,
`phase1_state`, `phase2cycle*_state`) are decoded from `keccak_st`.

The masked-path checks are compared against the XOR-recombination of the two shares
(`storage ^ storage_1` etc.). Theta/rho/pi are linear over GF(2) and distribute over the share
XOR, and chi/iota act on the recombined value, so the unmasked reference functions in
`fv_abr_keccak_round_functions.sv` applied once per round to the recombined state are reused as
the masked-round oracle.

### Reset

- assert_keccak_round_fsm_reset: Property to check that after reset the FSM is idle, ready_o is
  high, round index, storage/state of both shares and all status/error outputs are zero

### Unmasked round processing

- assert_keccak_round_waiting_for_input_to_round_state: Property to check that an unmasked,
  non-squeezing run XORs data_in into storage/state_out and enters round_state

- assert_keccak_round_waiting_for_input_to_round_state_1: Property to check that an unmasked
  squeezing run keeps storage/state_out stable and enters round_state

- assert_keccak_round_round_state_to_round_state: Property to check that each round_state cycle
  applies two reference rounds to storage, advances the round index by 2 and keeps ready_o low

- assert_keccak_round_round_state_to_waiting_for_input: Property to check that the last
  round_state cycle applies the final two rounds, raises complete_o, resets the round index and
  returns to idle

### Masked round processing (generated only when EN_MASKING=1)

- assert_keccak_round_waiting_for_input_to_phase1: Property to check that a masked,
  non-squeezing run XORs the recombined data_in into the recombined storage and enters Phase1

- assert_keccak_round_waiting_for_input_to_phase1_1: Property to check that a masked squeezing
  run keeps the recombined storage/state stable and enters Phase1

- assert_keccak_round_phase1_stall: Property to check that Phase1 holds (storage and round index
  stable, ready_o low) while neither rand_early_i nor rand_valid_i is set

- assert_keccak_round_phase1_to_next_round: Property to check the Phase1 -> Phase2Cycle1 ->
  Phase2Cycle2 -> Phase2Cycle3 sequence and that afterwards the recombined storage/state equals
  one reference round of the recombined state; the round index advances by 1 and after round 23
  the FSM completes and returns to idle

### Randomness handshake

- assert_keccak_round_rand_update_correct: Property to check that rand_update_o is high exactly
  in Phase2Cycle1, Phase2Cycle2, and in Phase1 when randomness is available

- assert_keccak_round_rand_consumed_correct: Property to check that rand_consumed_o is high
  exactly in Phase2Cycle2

### Idle behavior

- assert_keccak_round_waiting_for_input_to_waiting_for_input: Property to check that clear_i in
  idle zeroes storage/state of both shares and stays idle

- assert_keccak_round_waiting_for_input_to_waiting_for_input_1: Property to check that without
  clear_i and run_i the FSM idles with storage, state and round index stable

### Liveness and consistency

- assert_keccak_round_waiting_for_input_eventually_left / round_state_eventually_left: Liveness
  properties to check that idle and round_state are always eventually left

- assert_keccak_round_phase1_eventually_left / phase2cycle***_eventually_left: Liveness
  properties to check that each masked FSM state is always eventually left (generated only when
  EN_MASKING=1)

- assert_keccak_round_consistency_onehot0_state: Property to check that at most one of the six
  FSM state flags is set at any time

### Covers

- cover_phase1_rand_early_in_c / cover_phase1_rand_valid_in_c / cover_phase1_rand_progress_c:
  Covers to check that rand_early_i, rand_valid_i and either of them are reachable in Phase1

- cover_phase1_leaves_via_rand_c: Cover to check that Phase1 is left via the randomness
  condition into Phase2Cycle1

- cover_phase1_stalls_multi_cycle_c: Cover to check that Phase1 can stall for multiple cycles

- cover_rand_early_i_c / cover_rand_valid_i_c / cover_rand_progress_c /
  cover_rand_progress_after_gap_c (constraints file): Covers to check that the
  assume_rand_progress fairness assumption is exercised non-vacuously, including progress after a
  multi-cycle gap

The masked-datapath assertions, liveness properties and covers in `fv_abr_keccak_round_top.sv`
(`gen_masked_fsm_checks`/`gen_masked_liveness_checks`/`gen_masked_coverage`) are generated only
when `EN_MASKING=1` (bound to the DUT's `EnMasking`). With `EnMasking=0` the Phase1/Phase2CycleN
states do not exist, so these checks are skipped rather than reported as vacuous passes or
uncovered covers.

### Explicitly out of scope
This AIP checks **functional correctness** of the masked datapath (recombined output is
bit-exact to the unmasked reference) and its **control/protocol behavior**. It does **not**
check the SCA/non-interference (masking-soundness) property that individual shares or
intermediate signals leak no information about the secret; that requires dedicated
leakage/probing-security tooling, not classical model checking. The DOM AND primitive
(`abr_prim_dom_and_2share.sv`) carries its own embedded functional assertion
(`UnmaskedAndMatched_A`); this AIP composes on top of it at the `abr_keccak_round` boundary
rather than re-deriving the per-cycle DOM multiplier bit math.

## Key Constraints

- assume_run_i: while ready_o is high, the environment eventually drives run_i with clear_i
  deasserted (4'h9, MuBi4False), so idle liveness is not proved vacuously

- assume_masked_i_stable: masked_i is stable while a run is in flight (!ready_o). This models
  masked_i being a per-instruction opcode field (`abr_ctrl.sv`) held for an operation; required
  because the round termination logic reads masked_i combinationally every cycle

- assume_rand_progress: rand_early_i or rand_valid_i is eventually asserted (recurring fairness),
  matching the free-running LFSR randomness source in the integrated design; needed for the
  masked FSM liveness without over-constraining to "always asserted"

- assume_masked_requires_masking_hw: masked_i is held low; only generated when EN_MASKING=0
  (not active in the default EnMasking=1 run)

## Formal Setup
The AIP has been run with JasperGold only. OneSpin's bind-only `read_sva` flow rejects the
`fv_abr_keccak_round_share_bridge` module's output ports, and VCS rejects a net/variable port-type
mismatch inside the DUT RTL (`abr_keccak_2share.sv` s_i/s_o vs. `abr_keccak_round.sv` storage_datapath).

Load the design (abr_prim, abr_prim_generic, abr_sha3 incl. `abr_keccak_2share.sv`) and the five
property files and elaborate with:

| Setting    | Value                                                             |
| ---------- | ----------------------------------------------------------------- |
| top        | abr_keccak_round                                                  |
| parameters | RoundsPerClock 2, EnMasking 1                                     |
| clock      | clk_i                                                             |
| reset      | ~rst_b, zeroize                                                   |
| elaborate  | -create_related_covers {precondition witness}, -disable_auto_bbox |

With `EnMasking=1` both the unmasked and masked datapaths are present and checked in the same
run, matching the `SHA3_MASKING_EN=1` configuration of the integrated `abr_top` design.

## Reproduce Results
The AIP has been tested and proven with atleast one of these formals tools (Onespin ,Jasper , vcf).

To reproduce the results:
Load the AIP with all the necessary constraints together in your formal tool.

Feel free to reach out to contact@lubis-eda.com to request the loadscripts or the lubis modules.
