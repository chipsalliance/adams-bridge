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
// | Created on 25.02.2025 at 12:33                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_sample_in_ball_ctrl_pkg::*;


bind sample_in_ball_ctrl fv_sample_in_ball_ctrl_m fv_sample_in_ball_ctrl(
  .rst_n(rst_b && !zeroize),
  .clk(clk),

  // Ports
  .data_valid_port(sample_in_ball_ctrl.data_valid_i),

  .rddata0_port(sample_in_ball_ctrl.rddata_i[0]),

  .rddata1_port(sample_in_ball_ctrl.rddata_i[1]),

  .read_valid_port(sample_in_ball_ctrl.sib_shuffler_i.read_valid),

  .rej_value_port(sample_in_ball_ctrl.rej_value),

  .sampler_data_valid_port(sample_in_ball_ctrl.sampler_valid),

  .sampler_mask(sample_in_ball_ctrl.sampler_mask),

  .sampler_valid_port(sample_in_ball_ctrl.valid_sample),

  .shared_sib_data_in_port(sample_in_ball_ctrl.data_i),

  .sib_data_in_port_vld(sample_in_ball_ctrl.data_valid_i),
  .sib_data_in_port_rdy(1'b1),
  .sib_data_in_port(sample_in_ball_ctrl.data_i),

  .sign_buffer0_port(sample_in_ball_ctrl.sign_buffer[0]),

  .addr_o(sample_in_ball_ctrl.addr_o),

  .cs_o(sample_in_ball_ctrl.cs_o),

  .data_hold_o(sample_in_ball_ctrl.data_hold_o),

  .index_found(sample_in_ball_ctrl.index_found),

  .rej_value_en_out(sample_in_ball_ctrl.rej_value_en),

  .sampler_mask_d(sample_in_ball_ctrl.sampler_mask_d),

  .sampler_mask_en(sample_in_ball_ctrl.sampler_mask_en),

  .sib_done_o(sample_in_ball_ctrl.sib_done_o),

  .valid_sample(sample_in_ball_ctrl.valid_sample),

  .we_o(sample_in_ball_ctrl.we_o),

  .wrdata0_o(sample_in_ball_ctrl.wrdata_o[0]),

  .wrdata1_o(sample_in_ball_ctrl.wrdata_o[1]),

  // States
  .ACTIVE(sample_in_ball_ctrl.sib_fsm_ps == SIB_ACTIVE),
  .DONE(sample_in_ball_ctrl.sib_fsm_ps == SIB_DONE),
  .IDLE(sample_in_ball_ctrl.sib_fsm_ps == SIB_IDLE),
  .SIGN_BUFFER(sample_in_ball_ctrl.sib_fsm_ps == SIB_SIGN_BUFFER)
);
