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
// | Created on 19.12.2024 at 19:42                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_rej_bounded_ctrl_functions::*;


bind rej_bounded_ctrl fv_rej_bounded_ctrl_m fv_rej_bounded_ctrl(
  .rst_n(rst_b && !rej_bounded_ctrl.zeroize),
  .clk(rej_bounded_ctrl.clk),

  // Ports
  .data_i(rej_bounded_ctrl.data_i),

  .data_valid_i(rej_bounded_ctrl.data_valid_i),

  .fifo_data_o(rej_bounded_ctrl.rej_buffer),

  .data_hold_o_vld(1'b1),
  .data_hold_o(rej_bounded_ctrl.data_hold_o),

  .data_o(rej_bounded_ctrl.data_o),

  .data_valid_o_vld(1'b1),
  .data_valid_o(rej_bounded_ctrl.data_valid_o),

  .fifo_data_i(rej_bounded_ctrl.buffer_data),

  .fifo_valid_i(rej_bounded_ctrl.sample_valid),

  // States
  .buffer_full_state(rej_bounded_ctrl.buffer_full && rej_bounded_ctrl.rej_buffer_valid),
  .no_valid_data_state(!rej_bounded_ctrl.rej_buffer_valid && !rej_bounded_ctrl.buffer_full),
  .regular_state(rej_bounded_ctrl.rej_buffer_valid && !rej_bounded_ctrl.buffer_full)
);
