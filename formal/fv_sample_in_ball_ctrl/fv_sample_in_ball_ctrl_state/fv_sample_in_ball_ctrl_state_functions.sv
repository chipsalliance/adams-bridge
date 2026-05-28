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
// | Created on 17.02.2025 at 16:38                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sample_in_ball_ctrl_state_functions;


function logic unsigned [0:0] c_index_found(logic data_valid, logic unsigned [3:0][0:0] mask, logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej);
  logic unsigned [0:0] temp; // @ sample_in_ball_ctrl_state.h:20:5
  logic signed [31:0] i;     // @ sample_in_ball_ctrl_state.h:21:9

  temp = 1'd0;

  for (i = 32'd3; i > (-32'd1); i = i - 32'd1) begin
    if ((data_valid && (mask[unsigned'(i)] == 2'd1)) && (data[unsigned'(i)] < rej)) begin
      temp = 32'd1;
      break;
    end else begin
      temp = 32'd0;
    end
  end

  return temp;
endfunction


endpackage
