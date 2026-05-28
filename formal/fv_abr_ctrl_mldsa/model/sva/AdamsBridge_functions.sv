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
// | Created on 13.12.2024 at 12:44                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package AdamsBridge_functions;


function logic unsigned [63:0] getChunk(logic unsigned [20735:0] whole_value, logic unsigned [15:0] chunk_idx);
  logic unsigned [15:0] current_chunk_idx; // @ AdamsBridge.h:149:8

  //for (current_chunk_idx = 16'd0; (current_chunk_idx < chunk_idx) && (current_chunk_idx < 64'd324); current_chunk_idx = current_chunk_idx + 16'd1) begin
    whole_value = whole_value >> (32'd64*chunk_idx);
  //end

  return whole_value[(32'd64 - 32'd1):32'd0];
endfunction



function logic unsigned [63:0] func_concat_seed(logic unsigned [7:0][31:0] whole_value, logic unsigned [2:0] chunk_idx);
  logic unsigned [63:0] temp; // @ AdamsBridge.h:168:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[chunk_idx << 32'd1];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[(chunk_idx << 32'd1) | 64'd1];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


function logic unsigned [63:0] func_concat_pk(logic unsigned [647:0][31:0] whole_value, logic unsigned [2:0] chunk_idx);
  logic unsigned [63:0] temp; // @ AdamsBridge.h:178:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[chunk_idx << 32'd1];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[(chunk_idx << 32'd1) | 64'd1];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


function logic unsigned [63:0] func_concat_sig_c(logic unsigned [15:0][31:0] whole_value, logic unsigned [2:0] chunk_idx);
  logic unsigned [63:0] temp; // @ AdamsBridge.h:189:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[4'(chunk_idx << 32'd1)];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[4'((chunk_idx << 32'd1) | 64'd1)];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


function logic unsigned [63:0] func_concat_msg_p(logic unsigned [16:0][31:0] whole_value, logic unsigned [3:0] chunk_idx);
  logic unsigned [63:0] temp; // @ AdamsBridge.h:199:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[5'(chunk_idx << 32'd1)];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[5'((chunk_idx << 32'd1) | 64'd1)];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


function logic unsigned [63:0] func_concat(logic unsigned [9:0][31:0] whole_value, logic unsigned [2:0] chunk_idx);
  logic unsigned [63:0] temp; // @ AdamsBridge.h:209:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[4'(chunk_idx << 32'd1)];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[4'((chunk_idx << 32'd1) | 64'd1)];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


endpackage
