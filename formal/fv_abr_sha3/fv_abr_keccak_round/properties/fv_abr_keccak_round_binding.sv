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


import fv_abr_keccak_round_functions::*;


// abr_keccak_round.data_i/state_o/storage are unpacked arrays sized by the
// localparam Share (EnMasking ? 2 : 1). Index [1] only exists when
// EnMasking=1. This bridge resolves that at elaboration time via a
// generate-if keyed on SHARE, so the suite also elaborates with
// EnMasking=0 (share-1 signals tie to '0; every property that consumes them
// is masked-path only and gated on masked_in, which RTL holds low when
// EnMasking=0, so the tie-off value never affects a live check).
module fv_abr_keccak_round_share_bridge #(
  parameter int SHARE = 1
)(
  input  logic unsigned [1599:0] data_i  [SHARE],
  input  logic unsigned [1599:0] state_o [SHARE],
  input  logic unsigned [1599:0] storage [SHARE],
  output logic unsigned [1599:0] data_in_1,
  output logic unsigned [1599:0] state_out_1,
  output logic unsigned [1599:0] storage_1
);
  if (SHARE > 1) begin : gen_masked_share
    assign data_in_1   = data_i[1];
    assign state_out_1 = state_o[1];
    assign storage_1   = storage[1];
  end else begin : gen_no_share
    assign data_in_1   = '0;
    assign state_out_1 = '0;
    assign storage_1   = '0;
  end
endmodule


bind abr_keccak_round fv_abr_keccak_round_share_bridge #(.SHARE(Share)) fv_abr_keccak_round_share_bridge_i(
  .data_i(data_i),
  .state_o(state_o),
  .storage(storage),
  .data_in_1(),
  .state_out_1(),
  .storage_1()
);


bind abr_keccak_round fv_abr_keccak_round_top #(.EN_MASKING(EnMasking)) fv_abr_keccak_round_top_i(
  .rst((!abr_keccak_round.rst_b || abr_keccak_round.zeroize)),
  .clk(abr_keccak_round.clk_i),

  // Ports
  .clear_in(abr_keccak_round.clear_i == 4'h6),

  .data_in_vld(abr_keccak_round.run_i),
  .data_in_rdy(abr_keccak_round.ready_o),
  .data_in(abr_keccak_round.data_i[0]),
  .data_in_1(abr_keccak_round.fv_abr_keccak_round_share_bridge_i.data_in_1),

  .masked_in(abr_keccak_round.masked_i),
  .squeezing_in(abr_keccak_round.squeezing_i),

  .complete_out(abr_keccak_round.complete_o),

  .rand_valid_in(abr_keccak_round.rand_valid_i),
  .rand_early_in(abr_keccak_round.rand_early_i),
  .rand_aux_in(abr_keccak_round.rand_aux_i),
  .rand_update_out(abr_keccak_round.rand_update_o),
  .rand_consumed_out(abr_keccak_round.rand_consumed_o),

  .round_count_error_out(abr_keccak_round.round_count_error_o),

  .rst_storage_error_out(abr_keccak_round.rst_storage_error_o),

  .sparse_fsm_error_out(abr_keccak_round.sparse_fsm_error_o),

  .state_out(abr_keccak_round.state_o[0]),
  .state_out_1(abr_keccak_round.fv_abr_keccak_round_share_bridge_i.state_out_1),

  // Registers
  .round_idx(abr_keccak_round.round),
  .storage(abr_keccak_round.storage[0]),
  .storage_1(abr_keccak_round.fv_abr_keccak_round_share_bridge_i.storage_1),

  // States
  .round_state(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStActive),
  .waiting_for_input(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStIdle),
  .phase1_state(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStPhase1),
  .phase2cycle1_state(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStPhase2Cycle1),
  .phase2cycle2_state(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStPhase2Cycle2),
  .phase2cycle3_state(abr_keccak_round.keccak_st == abr_sha3_pkg::KeccakStPhase2Cycle3)
);
