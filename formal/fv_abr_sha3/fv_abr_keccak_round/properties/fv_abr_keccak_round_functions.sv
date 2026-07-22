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
// | Created on 17.01.2025 at 13:57                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_abr_keccak_round_functions;


parameter logic signed [4:0][4:0][31:0] rho_offsets = '{ 0: '{ 0: 32'd0, 1: 32'd36, 2: 32'd3, 3: 32'd41, 4: 32'd18 }, 1: '{ 0: 32'd1, 1: 32'd44, 2: 32'd10, 3: 32'd45, 4: 32'd2 }, 2: '{ 0: 32'd62, 1: 32'd6, 2: 32'd43, 3: 32'd15, 4: 32'd61 }, 3: '{ 0: 32'd28, 1: 32'd55, 2: 32'd25, 3: 32'd21, 4: 32'd56 }, 4: '{ 0: 32'd27, 1: 32'd20, 2: 32'd39, 3: 32'd8, 4: 32'd14 } };
parameter logic unsigned [23:0][63:0] rc_values = '{ 0: 64'h1, 1: 64'h8082, 2: 64'h800000000000808A, 3: 64'h8000000080008000, 4: 64'h808B, 5: 64'h80000001, 6: 64'h8000000080008081, 7: 64'h8000000000008009, 8: 64'h8A, 9: 64'h88, 10: 64'h80008009, 11: 64'h8000000A, 12: 64'h8000808B, 13: 64'h800000000000008B, 14: 64'h8000000000008089, 15: 64'h8000000000008003, 16: 64'h8000000000008002, 17: 64'h8000000000000080, 18: 64'h800A, 19: 64'h800000008000000A, 20: 64'h8000000080008081, 21: 64'h8000000000008080, 22: 64'h80000001, 23: 64'h8000000080008008 };


function logic unsigned [63:0] rotateLeft(logic unsigned [63:0] lane, logic signed [31:0] positions);
  return (lane << positions) | (lane >> (32'd64 - positions));
endfunction


function logic unsigned [4:0][4:0][63:0] stringToState(logic unsigned [1599:0] str);
  logic unsigned [4:0][4:0][63:0] new_state; // @ abr_sha3.h:38:3
  logic signed [31:0] row_idx;               // @ abr_sha3.h:40:8
  logic signed [31:0] col_idx;               // @ abr_sha3.h:41:10

  new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (row_idx = 32'd0; row_idx < 32'd5; row_idx = row_idx + 32'd1) begin
    for (col_idx = 32'd0; col_idx < 32'd5; col_idx = col_idx + 32'd1) begin
      new_state[unsigned'(col_idx)][unsigned'(row_idx)] = 64'(str);
      str = str >> 32'd64;
    end
  end

  return new_state;
endfunction


function logic unsigned [1599:0] stateToString(logic unsigned [4:0][4:0][63:0] state);
  logic unsigned [1599:0] new_string; // @ abr_sha3.h:51:3
  logic signed [31:0] row_idx;        // @ abr_sha3.h:53:8
  logic signed [31:0] col_idx;        // @ abr_sha3.h:54:10

  new_string = 1600'd0;

  for (row_idx = 32'd4; row_idx >= 32'sd0; row_idx = row_idx - 32'd1) begin
    for (col_idx = 32'd4; col_idx >= 32'sd0; col_idx = col_idx - 32'd1) begin
      new_string = new_string << 32'd64;
      new_string = new_string | state[unsigned'(col_idx)][unsigned'(row_idx)];
    end
  end

  return new_string;
endfunction


function logic unsigned [4:0][4:0][63:0] theta(logic unsigned [4:0][4:0][63:0] original_state);
  logic unsigned [4:0][63:0] C;              // @ abr_sha3.h:64:3
  logic signed [31:0] col_idx_0;             // @ abr_sha3.h:65:8
  logic unsigned [4:0][63:0] D;              // @ abr_sha3.h:70:3
  logic signed [31:0] col_idx_1;             // @ abr_sha3.h:71:8
  logic unsigned [4:0][4:0][63:0] new_state; // @ abr_sha3.h:75:3
  logic signed [31:0] row_idx;               // @ abr_sha3.h:76:8
  logic signed [31:0] col_idx_2;             // @ abr_sha3.h:77:10

  C = '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 };

  for (col_idx_0 = 32'd0; col_idx_0 < 32'd5; col_idx_0 = col_idx_0 + 32'd1) begin
    C[unsigned'(col_idx_0)] = (((original_state[unsigned'(col_idx_0)][64'd0] ^ original_state[unsigned'(col_idx_0)][64'd1]) ^ original_state[unsigned'(col_idx_0)][64'd2]) ^ original_state[unsigned'(col_idx_0)][64'd3]) ^ original_state[unsigned'(col_idx_0)][64'd4];
  end

  D = '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 };

  for (col_idx_1 = 32'd0; col_idx_1 < 32'd5; col_idx_1 = col_idx_1 + 32'd1) begin
    D[unsigned'(col_idx_1)] = C[unsigned'((col_idx_1 + 32'd4) % 32'd5)] ^ rotateLeft(C[unsigned'((col_idx_1 + 32'd1) % 32'd5)], 32'd1);
  end

  new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (row_idx = 32'd0; row_idx < 32'd5; row_idx = row_idx + 32'd1) begin
    for (col_idx_2 = 32'd0; col_idx_2 < 32'd5; col_idx_2 = col_idx_2 + 32'd1) begin
      new_state[unsigned'(col_idx_2)][unsigned'(row_idx)] = original_state[unsigned'(col_idx_2)][unsigned'(row_idx)] ^ D[unsigned'(col_idx_2)];
    end
  end

  return new_state;
endfunction


function logic unsigned [4:0][4:0][63:0] rho(logic unsigned [4:0][4:0][63:0] original_state);
  logic unsigned [4:0][4:0][63:0] new_state; // @ abr_sha3.h:86:3
  logic signed [31:0] row_idx;               // @ abr_sha3.h:87:8
  logic signed [31:0] col_idx;               // @ abr_sha3.h:88:10

  new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (row_idx = 32'd0; row_idx < 32'd5; row_idx = row_idx + 32'd1) begin
    for (col_idx = 32'd0; col_idx < 32'd5; col_idx = col_idx + 32'd1) begin
      new_state[unsigned'(col_idx)][unsigned'(row_idx)] = rotateLeft(original_state[unsigned'(col_idx)][unsigned'(row_idx)], rho_offsets[unsigned'(col_idx)][unsigned'(row_idx)]);
    end
  end

  return new_state;
endfunction


function logic unsigned [4:0][4:0][63:0] pi(logic unsigned [4:0][4:0][63:0] original_state);
  logic unsigned [4:0][4:0][63:0] new_state; // @ abr_sha3.h:97:3
  logic signed [31:0] row_idx;               // @ abr_sha3.h:98:8
  logic signed [31:0] col_idx;               // @ abr_sha3.h:99:10

  new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (row_idx = 32'd0; row_idx < 32'd5; row_idx = row_idx + 32'd1) begin
    for (col_idx = 32'd0; col_idx < 32'd5; col_idx = col_idx + 32'd1) begin
      new_state[unsigned'(col_idx)][unsigned'(row_idx)] = original_state[unsigned'((col_idx + (32'd3 * row_idx)) % 32'd5)][unsigned'(col_idx)];
    end
  end

  return new_state;
endfunction


function logic unsigned [4:0][4:0][63:0] chi(logic unsigned [4:0][4:0][63:0] original_state);
  logic unsigned [4:0][4:0][63:0] new_state; // @ abr_sha3.h:108:3
  logic signed [31:0] row_idx;               // @ abr_sha3.h:109:8
  logic signed [31:0] col_idx;               // @ abr_sha3.h:110:10

  new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (row_idx = 32'd0; row_idx < 32'd5; row_idx = row_idx + 32'd1) begin
    for (col_idx = 32'd0; col_idx < 32'd5; col_idx = col_idx + 32'd1) begin
      new_state[unsigned'(col_idx)][unsigned'(row_idx)] = original_state[unsigned'(col_idx)][unsigned'(row_idx)] ^ ((~original_state[unsigned'((col_idx + 32'd1) % 32'd5)][unsigned'(row_idx)]) & original_state[unsigned'((col_idx + 32'd2) % 32'd5)][unsigned'(row_idx)]);
    end
  end

  return new_state;
endfunction


function logic unsigned [4:0][4:0][63:0] iota(logic unsigned [4:0][4:0][63:0] original_state, logic signed [31:0] round_idx);
  original_state[64'd0][64'd0] = original_state[64'd0][64'd0] ^ rc_values[unsigned'(round_idx)];
  return original_state;
endfunction


endpackage
