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
// | Created on 11.03.2025 at 13:08                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_abr_keccak_round_functions::*;


bind abr_keccak_round fv_abr_keccak_round_top fv_abr_keccak_round_top_i(
  .rst((!abr_keccak_round.rst_b || abr_keccak_round.zeroize)),
  .clk(abr_keccak_round.clk_i),

  // Ports
  .clear_in(abr_keccak_round.clear_i == 4'h6),

  .data_in_vld(abr_keccak_round.run_i),
  .data_in_rdy(abr_keccak_round.ready_o),
  .data_in(abr_keccak_round.data_i[0]),

  .squeezing_in(abr_keccak_round.squeezing_i),

  .complete_out(abr_keccak_round.complete_o),

  .rand_consumed_out(abr_keccak_round.rand_consumed_o),

  .round_count_error_out(abr_keccak_round.round_count_error_o),

  .rst_storage_error_out(abr_keccak_round.rst_storage_error_o),

  .sparse_fsm_error_out(abr_keccak_round.sparse_fsm_error_o),

  .state_out(abr_keccak_round.state_o[0]),

  // Registers
  .round_idx(abr_keccak_round.round),
  .storage(abr_keccak_round.storage[0]),

  // States
  .round_state(abr_keccak_round.keccak_st == StActive),
  .waiting_for_input(abr_keccak_round.keccak_st == StIdle)
);
