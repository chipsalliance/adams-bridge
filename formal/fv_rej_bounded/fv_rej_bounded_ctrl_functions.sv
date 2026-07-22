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
// | Created on 19.12.2024 at 18:34                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_rej_bounded_ctrl_functions;


function logic unsigned [7:0][2:0] rejBoundedData(logic unsigned [7:0][3:0] data_in_pi);
  logic unsigned [7:0][2:0] valid_samples; // @ rej_bounded_ctrl.h:48:17
  logic signed [31:0] i;                   // @ rej_bounded_ctrl.h:50:21

  valid_samples = '{ 0: 3'd0, 1: 3'd0, 2: 3'd0, 3: 3'd0, 4: 3'd0, 5: 3'd0, 6: 3'd0, 7: 3'd0 };

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    if (data_in_pi[unsigned'(i)] == 4'd15) begin
      valid_samples[unsigned'(i)] = 3'd0;
    end else begin
      valid_samples[unsigned'(i)] = 3'(data_in_pi[unsigned'(i)] % 4'd5);
    end
  end

  return valid_samples;
endfunction


function logic unsigned [7:0] rejBoundedValid(logic unsigned [7:0][3:0] data_in_pi, logic valid_input);
  logic unsigned [7:0] valid_data; // @ rej_bounded_ctrl.h:62:17
  logic signed [31:0] i;           // @ rej_bounded_ctrl.h:64:21

  valid_data = 8'd0;

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    if ((data_in_pi[unsigned'(i)] == 4'd15) || (!valid_input)) begin
      valid_data[i] = 0;
    end else begin
      valid_data[i] = 1;
    end
  end

  return valid_data;
endfunction


function logic unsigned [3:0][23:0] modMux(logic unsigned [3:0][2:0] fifo_output_data);
  logic unsigned [3:0][23:0] muxed_data; // @ rej_bounded_ctrl.h:76:17
  logic signed [31:0] i;                 // @ rej_bounded_ctrl.h:78:21

  muxed_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    muxed_data[unsigned'(i)] = ((24'd2 + 64'd8380417) - fifo_output_data[unsigned'(i)]) % 64'd8380417;
  end

  return muxed_data;
endfunction


endpackage
