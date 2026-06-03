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
// | Created on 06.02.2025 at 13:51                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_ntt_masked_butterfly1x2_functions;


function logic unsigned [22:0] compute_u(logic unsigned [1:0][45:0] u, logic unsigned [1:0][45:0] v);
  logic unsigned [22:0] temp; // @ ntt_masked_butterfly1x2.h:15:5

  temp = 23'd0;
  temp = 23'(((((u[64'd0] + u[64'd1]) + v[64'd0]) + v[64'd1]) % 64'h400000000000) % 64'd8380417);
  return temp;
endfunction


function logic unsigned [22:0] compute_v(logic unsigned [1:0][45:0] u, logic unsigned [1:0][45:0] v, logic unsigned [1:0][45:0] w);
  logic unsigned [22:0] temp; // @ ntt_masked_butterfly1x2.h:23:5

  temp = 23'd0;

  if (46'(u[64'd0] + u[64'd1]) >= 46'(v[64'd0] + v[64'd1])) begin
    temp = 23'(((u[64'd0] + u[64'd1]) - v[64'd0]) - v[64'd1]);
  end else begin
    temp = 23'((((u[64'd0] + u[64'd1]) - v[64'd0]) - v[64'd1]) + 64'd8380417);
  end

  return 23'((temp * ((w[64'd0] + w[64'd1]) % 64'h400000000000)) % 64'd8380417);
endfunction


function logic unsigned [22:0] div2(logic unsigned [22:0] data);
  logic unsigned [22:0] result; // @ ntt_masked_butterfly1x2.h:38:5

  result = 23'd0;

  if (data[32'd0] != 64'd0) begin
    result = (data >> 32'd1) + unsigned'(23'((32'd8380417 + 32'd1) / 32'd2));
  end else begin
    result = data >> 32'd1;
  end

  return result;
endfunction

function logic unsigned [1:0][45:0] comp_packed(logic unsigned [45:0][1:0] temp);
  logic unsigned [1:0][45:0] result; // @ ntt_hybrid_butterfly_2x2.h:96:5
  logic signed [31:0] i;             // @ ntt_hybrid_butterfly_2x2.h:98:10

  result = '{ 0: 46'd0, 1: 46'd0 };

  for (i = 32'd0; i < 32'd46; i = i + 32'd1) begin
    result[64'd0][i] = temp[unsigned'(i)][32'd0];
    result[64'd1][i] = temp[unsigned'(i)][32'd1];
  end

  return result;
endfunction

function logic unsigned [45:0][1:0] unpacked(logic unsigned [1:0][45:0] temp);
  logic unsigned [45:0][1:0] result; // @ ntt_hybrid_butterfly_2x2.h:85:5
  logic signed [31:0] i;             // @ ntt_hybrid_butterfly_2x2.h:87:10

  result = '{ 0: 2'd0, 1: 2'd0, 2: 2'd0, 3: 2'd0, 4: 2'd0, 5: 2'd0, 6: 2'd0, 7: 2'd0, 8: 2'd0, 9: 2'd0, 10: 2'd0, 11: 2'd0, 12: 2'd0, 13: 2'd0, 14: 2'd0, 15: 2'd0, 16: 2'd0, 17: 2'd0, 18: 2'd0, 19: 2'd0, 20: 2'd0, 21: 2'd0, 22: 2'd0, 23: 2'd0, 24: 2'd0, 25: 2'd0, 26: 2'd0, 27: 2'd0, 28: 2'd0, 29: 2'd0, 30: 2'd0, 31: 2'd0, 32: 2'd0, 33: 2'd0, 34: 2'd0, 35: 2'd0, 36: 2'd0, 37: 2'd0, 38: 2'd0, 39: 2'd0, 40: 2'd0, 41: 2'd0, 42: 2'd0, 43: 2'd0, 44: 2'd0, 45: 2'd0 };

  for (i = 32'd0; i < 32'd46; i = i + 32'd1) begin
    result[unsigned'(i)][32'd0] = temp[64'd0][i];
    result[unsigned'(i)][32'd1] = temp[64'd1][i];
  end
  
  /*for (i = 32'd0; i < 32'd46; i = i + 32'd1) begin
    result[64'd0][i] = temp[unsigned'(i)][32'd0];
    result[64'd1][i] = temp[unsigned'(i)][32'd1];
  end*/

  return result;
endfunction


endpackage
