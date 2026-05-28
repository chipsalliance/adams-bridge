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
// | Created on 29.03.2025 at 21:28                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_skdecode_top_functions;


function logic unsigned [3:0][23:0] decode_s1s2_a(logic unsigned [7:0][2:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] decoded_data; // @ skdecode_top.h:67:13
  logic signed [31:0] i;                   // @ skdecode_top.h:69:17

  decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if ((data_to_be_decoded[unsigned'(i)] >= 64'd0) && (data_to_be_decoded[unsigned'(i)] < 64'd5)) begin
      decoded_data[unsigned'(i)] = ((24'd2 - data_to_be_decoded[unsigned'(i)]) + 64'd8380417) % 64'd8380417;
    end else begin
      decoded_data[unsigned'(i)] = 32'd0;
    end
  end

  return decoded_data;
endfunction


function logic unsigned [3:0][23:0] decode_s1s2_b(logic unsigned [7:0][2:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] decoded_data; // @ skdecode_top.h:80:13
  logic signed [31:0] i;                   // @ skdecode_top.h:82:17

  decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };

  for (i = 32'd4; i < 32'd8; i = i + 32'd1) begin
    if ((data_to_be_decoded[unsigned'(i)] >= 64'd0) && (data_to_be_decoded[unsigned'(i)] < 64'd5)) begin
      decoded_data[unsigned'(i - 32'd4)] = ((24'd2 - data_to_be_decoded[unsigned'(i)]) + 64'd8380417) % 64'd8380417;
    end else begin
      decoded_data[unsigned'(i - 32'd4)] = 32'd0;
    end
  end

  return decoded_data;
endfunction


function logic unsigned [3:0][23:0] decode_t0(logic unsigned [3:0][12:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] decoded_data; // @ skdecode_top.h:93:13
  logic signed [31:0] i;                   // @ skdecode_top.h:95:17

  decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    decoded_data[unsigned'(i)] = ((24'd4096 - data_to_be_decoded[unsigned'(i)]) + 64'd8380417) % 64'd8380417;
  end

  return decoded_data;
endfunction


endpackage
