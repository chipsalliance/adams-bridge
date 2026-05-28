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
// | Created on 06.02.2025 at 10:55                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


bind mldsa_sampler_top fv_mldsa_sampler_top_m fv_mldsa_sampler_top(
  .rst_n(mldsa_sampler_top.rst_b && !mldsa_sampler_top.zeroize),
  .clk(mldsa_sampler_top.clk),

  // Ports
  .sampler_done(mldsa_sampler_top.sampler_done),

  .sampler_start_i(mldsa_sampler_top.sampler_start_i),

  .sha3_squeezing(mldsa_sampler_top.sha3_squeezing),

  .sha3_state_dv(mldsa_sampler_top.sha3_state_dv),

  .sha3_state_hold(mldsa_sampler_top.sha3_state_hold),

  .sha3_done_vld(1'b1),
  .sha3_done(mldsa_sampler_top.sha3_done),

  .sha3_process_vld(1'b1),
  .sha3_process(mldsa_sampler_top.sha3_process),

  .sha3_run_vld(1'b1),
  .sha3_run(mldsa_sampler_top.sha3_run),

  // Registers
  .cur_st(mldsa_sampler_top.sampler_fsm_ps),
  .sampler_done_temp(mldsa_sampler_top.sampler_done),
  .sampler_start_i_temp(mldsa_sampler_top.sampler_start_i),
  .sha3_squeezing_temp(mldsa_sampler_top.sha3_squeezing),
  .sha3_state_dv_temp(mldsa_sampler_top.sha3_state_dv),
  .sha3_state_hold_temp(mldsa_sampler_top.sha3_state_hold),
  .sha3_fsm_temp(mldsa_sampler_top.sha3_fsm),

  // States
  .DONE(mldsa_sampler_top.sampler_fsm_ps ==  MLDSA_SAMPLER_DONE),
  .IDLE(mldsa_sampler_top.sampler_fsm_ps ==  MLDSA_SAMPLER_IDLE),
  .PROC(mldsa_sampler_top.sampler_fsm_ps == MLDSA_SAMPLER_PROC),
  .RUN(mldsa_sampler_top.sampler_fsm_ps == MLDSA_SAMPLER_RUN),
  .WAIT(mldsa_sampler_top.sampler_fsm_ps == MLDSA_SAMPLER_WAIT)
);
