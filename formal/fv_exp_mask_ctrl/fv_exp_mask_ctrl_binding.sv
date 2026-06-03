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
// | Created on 03.12.2024 at 15:33                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_exp_mask_ctrl_pkg::*;


bind exp_mask_ctrl fv_exp_mask_ctrl_m fv_exp_mask_ctrl(
  .rst_n(rst_b),
  .zeroize(zeroize),
  .clk(clk),

  // Ports
  .input_data_port(exp_mask_ctrl.data_i),

  .input_data_valid_port(exp_mask_ctrl.data_valid_i),

  .output_data_port(exp_mask_ctrl.data_o),

  .output_data_hold_o(exp_mask_ctrl.data_hold_o),

  .output_data_valid_port(exp_mask_ctrl.data_valid_o)

);
