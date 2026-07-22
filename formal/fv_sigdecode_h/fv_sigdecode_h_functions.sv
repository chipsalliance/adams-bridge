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
// | Created on 07.03.2025 at 14:58                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sigdecode_h_functions;


function logic unsigned [7:0] upd_rem_hintsum(logic unsigned [7:0] prev_val);
  logic unsigned [7:0] result; // @ sigdecode_h_new.h:67:13

  result = 8'd0;

  if (prev_val >= 8'd4) begin
    result = 8'(prev_val - 8'd4);
  end

  return result;
endfunction


function logic unsigned [255:0] upd_bitmap(logic unsigned [3:0] curr_poly_map_val, logic unsigned [3:0][7:0] hint_val, logic unsigned [255:0] bitmap_val);
  logic unsigned [255:0] result; // @ sigdecode_h_new.h:75:13

  result = 256'd0;
  result = bitmap_val;

  if (curr_poly_map_val == 4'd15) begin
    result[unsigned'(hint_val[64'd0])] = 1;
    result[unsigned'(hint_val[64'd1])] = 1;
    result[unsigned'(hint_val[64'd2])] = 1;
    result[unsigned'(hint_val[64'd3])] = 1;
  end else if (curr_poly_map_val == 4'd1) begin
    result[unsigned'(hint_val[64'd0])] = 1;
  end else if (curr_poly_map_val == 4'd3) begin
    result[unsigned'(hint_val[64'd0])] = 1;
    result[unsigned'(hint_val[64'd1])] = 1;
  end else if (curr_poly_map_val == 4'd7) begin
    result[unsigned'(hint_val[64'd0])] = 1;
    result[unsigned'(hint_val[64'd1])] = 1;
    result[unsigned'(hint_val[64'd2])] = 1;
  end

  return result;
endfunction


function logic unsigned [95:0] upd_write_data(logic unsigned [255:0] bitmap_val, logic unsigned [7:0] bitmap_ptr_val);
  logic unsigned [95:0] result;    // @ sigdecode_h_new.h:96:13
  logic unsigned [3:0][95:0] temp; // @ sigdecode_h_new.h:97:13

  result = 96'd0;
  temp = '{ 0: 96'd0, 1: 96'd0, 2: 96'd0, 3: 96'd0 };
  temp[64'd0] = bitmap_val[unsigned'(8'(bitmap_ptr_val + 8'd3))] << 32'd72;
  temp[64'd1] = bitmap_val[unsigned'(8'(bitmap_ptr_val + 8'd2))] << 32'd48;
  temp[64'd2] = bitmap_val[unsigned'(8'(bitmap_ptr_val + 8'd1))] << 32'd24;
  temp[64'd3] = bitmap_val[unsigned'(8'(bitmap_ptr_val + 8'd0))];
  result = ((temp[64'd0] | temp[64'd1]) | temp[64'd2]) | temp[64'd3];
  return result;
endfunction


function logic upd_remaining_encoded_h_i(logic unsigned [82:0][7:0] read_data_val);
  logic result;          // @ sigdecode_h_new.h:107:13
  logic signed [31:0] i; // @ sigdecode_h_new.h:108:17
  logic ored_val;        // @ sigdecode_h_new.h:110:21
  logic signed [31:0] j; // @ sigdecode_h_new.h:111:25

  result = 0;

  for (i = 32'd0; i < 32'd75; i = i + 32'd1) begin
    if (unsigned'(i) >= read_data_val[64'd82]) begin
      ored_val = 0;

      for (j = 32'd0; j < 32'd8; j = j + 32'd1) begin
        ored_val = (ored_val | read_data_val[unsigned'(i)][j]) != 64'd0;
      end

      result = (result | ored_val) != 32'd0;
    end else begin
      result = 0;
    end
  end

  return result;
endfunction


function logic upd_hintsum_max_error_i(logic unsigned [82:0][7:0] read_data_val);
  logic result;          // @ sigdecode_h_new.h:123:13
  logic signed [31:0] i; // @ sigdecode_h_new.h:124:17

  result = 0;

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    if (read_data_val[unsigned'(32'd75 + i)] > 64'd75) begin
      result = 1;
    end
  end

  return result;
endfunction


function logic upd_hint_ok(logic unsigned [3:0] curr_poly_map_val, logic unsigned [3:0][7:0] hint_val, logic unsigned [7:0] prev_hint_val, logic first_hint_val);
  logic result; // @ sigdecode_h_new.h:133:13

  result = 0;
  result = ((((curr_poly_map_val[32'd0] != 64'd0) ? (first_hint_val ? (prev_hint_val <= hint_val[64'd0]) : (prev_hint_val < hint_val[64'd0])) : 1) && (((curr_poly_map_val[32'd0] & curr_poly_map_val[32'd1]) != 64'd0) ? (hint_val[64'd0] < hint_val[64'd1]) : 1)) && (((curr_poly_map_val[32'd1] & curr_poly_map_val[32'd2]) != 64'd0) ? (hint_val[64'd1] < hint_val[64'd2]) : 1)) && (((curr_poly_map_val[32'd2] & curr_poly_map_val[32'd3]) != 64'd0) ? (hint_val[64'd2] < hint_val[64'd3]) : 1);
  return result;
endfunction


endpackage
