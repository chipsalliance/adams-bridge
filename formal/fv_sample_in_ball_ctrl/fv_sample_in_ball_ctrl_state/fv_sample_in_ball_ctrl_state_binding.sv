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
// | Created on 20.02.2025 at 18:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_sample_in_ball_ctrl_pkg::*;
import fv_sample_in_ball_ctrl_state_functions::*;


bind sample_in_ball_ctrl fv_sample_in_ball_ctrl_state_m fv_sample_in_ball_ctrl_state(
  .rst_n(sample_in_ball_ctrl.rst_b && !sample_in_ball_ctrl.zeroize),
  .clk(sample_in_ball_ctrl.clk),

  // Ports
  .data_i_port_vld(sample_in_ball_ctrl.data_valid_i),
  .data_i_port_rdy(1'b1),
  .data_i_port(sample_in_ball_ctrl.data_i),

  .data_valid_i(sample_in_ball_ctrl.data_valid_i),

  .index_found(sample_in_ball_ctrl.index_found),

  .read_valid_in(sample_in_ball_ctrl.sib_shuffler_i.read_valid),

  .rej_value_en(sample_in_ball_ctrl.rej_value_en),

  .rej_value_in(sample_in_ball_ctrl.rej_value),

  .sign_buffer_in(sample_in_ball_ctrl.sign_buffer),

  .read_valid(sample_in_ball_ctrl.sib_shuffler_i.read_valid),

  .rej_value(sample_in_ball_ctrl.rej_value),

  .sign_buffer(sample_in_ball_ctrl.sign_buffer),

  // States
  .ACTIVE(sample_in_ball_ctrl.sib_fsm_ps == SIB_ACTIVE),
  .DONE(sample_in_ball_ctrl.sib_fsm_ps == SIB_DONE),
  .IDLE(sample_in_ball_ctrl.sib_fsm_ps == SIB_IDLE),
  .SIGN_BUFFER(sample_in_ball_ctrl.sib_fsm_ps == SIB_SIGN_BUFFER)
);
