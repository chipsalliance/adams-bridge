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

module fv_abr_keccak_round_constraints
  import abr_prim_mubi_pkg::*;
#(
  parameter bit EN_MASKING = 1'b0
)(
  input clk_i,
  input ready_o,
  input run_i,
  input masked_i,
  input rand_early_i,
  input rand_valid_i,
  input abr_prim_mubi_pkg::mubi4_t clear_i
);

default clocking default_clk @(posedge clk_i); endclocking


// Fairness: while idle (ready_o), the environment eventually drives a genuine
// clear (4'h9=MuBi4True) with run_i -- needed so waiting-for-input liveness
// in fv_abr_keccak_round_top.sv isn't proved vacuously.
property assume_run_i_p;
  ready_o
|->
  s_eventually(clear_i == 4'h9 && run_i)
endproperty
assume_run_i: assume property (assume_run_i_p);


// masked_i is a per-instruction opcode field (abr_ctrl.sv) held stable for
// an entire operation; round-termination logic (rnd_eq_end) reads it
// combinationally and assumes it can't change mid-round.
property assume_masked_i_stable_p;
  !ready_o
|->
  $stable(masked_i)
endproperty
assume_masked_i_stable: assume property (assume_masked_i_stable_p);


// Masked datapath only exists in RTL when EnMasking=1; gated via generate
// (not masked_i|->EN_MASKING, which is a vacuous tautology when EN_MASKING=1).
if (!EN_MASKING) begin : gen_no_masking_hw
  assume_masked_requires_masking_hw: assume property(!masked_i);
end


// In integration, rand_early_i/rand_valid_i come from a free-running LFSR
// (always asserted); model as recurring fairness so masked-FSM liveness
// proves at unit level. Uses s_eventually, not ##[1:$], since only that form
// is reliably consumed by JasperGold's liveness engine as a fairness constraint.
assume_rand_progress: assume property(
  s_eventually (rand_early_i || rand_valid_i)
);


///////////////////////////////////////////////////////////////
// Coverage: is the rand_progress fairness assumption exercised //
// non-vacuously, in both directions?                           //
///////////////////////////////////////////////////////////////

// rand_early_i alone is reachable.
cover_rand_early_i_c: cover property (
  rand_early_i
);

// rand_valid_i alone is reachable.
cover_rand_valid_i_c: cover property (
  rand_valid_i
);

// The combined enabling condition used by assume_rand_progress is reachable.
cover_rand_progress_c: cover property (
  rand_early_i || rand_valid_i
);

// Confirms the "eventually" isn't vacuously immediate -- a multi-cycle gap
// before progress is also reachable, not just being forced high every cycle.
cover_rand_progress_after_gap_c: cover property (
  !(rand_early_i || rand_valid_i) ##1 !(rand_early_i || rand_valid_i) ##1 (rand_early_i || rand_valid_i)
);


endmodule


bind abr_keccak_round fv_abr_keccak_round_constraints #(.EN_MASKING(EnMasking)) constraints_inst (
  .clk_i(clk_i),
  .ready_o(ready_o),
  .run_i(run_i),
  .masked_i(masked_i),
  .rand_early_i(rand_early_i),
  .rand_valid_i(rand_valid_i),
  .clear_i(clear_i)
);
