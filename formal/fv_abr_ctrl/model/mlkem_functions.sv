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
// | Created on 11.09.2025 at 19:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package mlkem_functions;


function logic unsigned [63:0] getChunk(logic unsigned [20735:0] whole_value, logic unsigned [15:0] chunk_idx);
  whole_value = whole_value >> (64'd64 * chunk_idx);
  return whole_value[(32'd64 - 32'd1):32'd0];
endfunction


function logic unsigned [63:0] func_concat_seed(logic unsigned [7:0][31:0] whole_value, logic unsigned [2:0] chunk_idx);
  logic unsigned [63:0] temp; // @ mlkem.h:175:3

  temp = 64'd0;
  temp[((32'd64 / 32'd2) - 32'd1):32'd0] = whole_value[chunk_idx << 32'd1];
  temp[(32'd64 - 32'd1):(32'd64 / 32'd2)] = whole_value[(chunk_idx << 32'd1) | 64'd1];
  return temp[(32'd64 - 32'd1):32'd0];
endfunction


endpackage
