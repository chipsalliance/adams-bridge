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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+


package fv_abr_keccak_round_functions;


localparam logic signed [4:0][4:0][31:0] RHO_OFFSETS = '{ 0: '{ 0: 32'd0, 1: 32'd36, 2: 32'd3, 3: 32'd41, 4: 32'd18 }, 1: '{ 0: 32'd1, 1: 32'd44, 2: 32'd10, 3: 32'd45, 4: 32'd2 }, 2: '{ 0: 32'd62, 1: 32'd6, 2: 32'd43, 3: 32'd15, 4: 32'd61 }, 3: '{ 0: 32'd28, 1: 32'd55, 2: 32'd25, 3: 32'd21, 4: 32'd56 }, 4: '{ 0: 32'd27, 1: 32'd20, 2: 32'd39, 3: 32'd8, 4: 32'd14 } };
localparam logic unsigned [23:0][63:0] RC_VALUES = '{ 0: 64'h1, 1: 64'h8082, 2: 64'h800000000000808A, 3: 64'h8000000080008000, 4: 64'h808B, 5: 64'h80000001, 6: 64'h8000000080008081, 7: 64'h8000000000008009, 8: 64'h8A, 9: 64'h88, 10: 64'h80008009, 11: 64'h8000000A, 12: 64'h8000808B, 13: 64'h800000000000008B, 14: 64'h8000000000008089, 15: 64'h8000000000008003, 16: 64'h8000000000008002, 17: 64'h8000000000000080, 18: 64'h800A, 19: 64'h800000008000000A, 20: 64'h8000000080008081, 21: 64'h8000000000008080, 22: 64'h80000001, 23: 64'h8000000080008008 };


function automatic logic unsigned [63:0] rotate_left(logic unsigned [63:0] fv_lane, logic signed [31:0] fv_positions);
  return (fv_lane << fv_positions) | (fv_lane >> (32'd64 - fv_positions));
endfunction


function automatic logic unsigned [4:0][4:0][63:0] string_to_state(logic unsigned [1599:0] fv_str);
  logic unsigned [4:0][4:0][63:0] fv_new_state; // @ abr_sha3.h:38:3
  logic signed [31:0] fv_row_idx;               // @ abr_sha3.h:40:8
  logic signed [31:0] fv_col_idx;               // @ abr_sha3.h:41:10

  fv_new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (fv_row_idx = 32'd0; fv_row_idx < 32'd5; fv_row_idx = fv_row_idx + 32'd1) begin
    for (fv_col_idx = 32'd0; fv_col_idx < 32'd5; fv_col_idx = fv_col_idx + 32'd1) begin
      fv_new_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)] = 64'(fv_str);
      fv_str = fv_str >> 32'd64;
    end
  end

  return fv_new_state;
endfunction


function automatic logic unsigned [1599:0] state_to_string(logic unsigned [4:0][4:0][63:0] fv_state);
  logic unsigned [1599:0] fv_new_string; // @ abr_sha3.h:51:3
  logic signed [31:0] fv_row_idx;        // @ abr_sha3.h:53:8
  logic signed [31:0] fv_col_idx;        // @ abr_sha3.h:54:10

  fv_new_string = 1600'd0;

  for (fv_row_idx = 32'd4; fv_row_idx >= 32'sd0; fv_row_idx = fv_row_idx - 32'd1) begin
    for (fv_col_idx = 32'd4; fv_col_idx >= 32'sd0; fv_col_idx = fv_col_idx - 32'd1) begin
      fv_new_string = fv_new_string << 32'd64;
      fv_new_string = fv_new_string | fv_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)];
    end
  end

  return fv_new_string;
endfunction


function automatic logic unsigned [4:0][4:0][63:0] theta(logic unsigned [4:0][4:0][63:0] fv_original_state);
  logic unsigned [4:0][63:0] fv_c;              // @ abr_sha3.h:64:3
  logic signed [31:0] fv_col_idx_0;             // @ abr_sha3.h:65:8
  logic unsigned [4:0][63:0] fv_d;              // @ abr_sha3.h:70:3
  logic signed [31:0] fv_col_idx_1;             // @ abr_sha3.h:71:8
  logic unsigned [4:0][4:0][63:0] fv_new_state; // @ abr_sha3.h:75:3
  logic signed [31:0] fv_row_idx;               // @ abr_sha3.h:76:8
  logic signed [31:0] fv_col_idx_2;             // @ abr_sha3.h:77:10

  fv_c = '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 };

  for (fv_col_idx_0 = 32'd0; fv_col_idx_0 < 32'd5; fv_col_idx_0 = fv_col_idx_0 + 32'd1) begin
    fv_c[unsigned'(fv_col_idx_0)] = (((fv_original_state[unsigned'(fv_col_idx_0)][64'd0] ^ fv_original_state[unsigned'(fv_col_idx_0)][64'd1]) ^ fv_original_state[unsigned'(fv_col_idx_0)][64'd2]) ^ fv_original_state[unsigned'(fv_col_idx_0)][64'd3]) ^ fv_original_state[unsigned'(fv_col_idx_0)][64'd4];
  end

  fv_d = '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 };

  for (fv_col_idx_1 = 32'd0; fv_col_idx_1 < 32'd5; fv_col_idx_1 = fv_col_idx_1 + 32'd1) begin
    fv_d[unsigned'(fv_col_idx_1)] = fv_c[unsigned'((fv_col_idx_1 + 32'd4) % 32'd5)] ^ rotate_left(fv_c[unsigned'((fv_col_idx_1 + 32'd1) % 32'd5)], 32'd1);
  end

  fv_new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (fv_row_idx = 32'd0; fv_row_idx < 32'd5; fv_row_idx = fv_row_idx + 32'd1) begin
    for (fv_col_idx_2 = 32'd0; fv_col_idx_2 < 32'd5; fv_col_idx_2 = fv_col_idx_2 + 32'd1) begin
      fv_new_state[unsigned'(fv_col_idx_2)][unsigned'(fv_row_idx)] = fv_original_state[unsigned'(fv_col_idx_2)][unsigned'(fv_row_idx)] ^ fv_d[unsigned'(fv_col_idx_2)];
    end
  end

  return fv_new_state;
endfunction


function automatic logic unsigned [4:0][4:0][63:0] rho(logic unsigned [4:0][4:0][63:0] fv_original_state);
  logic unsigned [4:0][4:0][63:0] fv_new_state; // @ abr_sha3.h:86:3
  logic signed [31:0] fv_row_idx;               // @ abr_sha3.h:87:8
  logic signed [31:0] fv_col_idx;               // @ abr_sha3.h:88:10

  fv_new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (fv_row_idx = 32'd0; fv_row_idx < 32'd5; fv_row_idx = fv_row_idx + 32'd1) begin
    for (fv_col_idx = 32'd0; fv_col_idx < 32'd5; fv_col_idx = fv_col_idx + 32'd1) begin
      fv_new_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)] = rotate_left(fv_original_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)], RHO_OFFSETS[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)]);
    end
  end

  return fv_new_state;
endfunction


function automatic logic unsigned [4:0][4:0][63:0] pi(logic unsigned [4:0][4:0][63:0] fv_original_state);
  logic unsigned [4:0][4:0][63:0] fv_new_state; // @ abr_sha3.h:97:3
  logic signed [31:0] fv_row_idx;               // @ abr_sha3.h:98:8
  logic signed [31:0] fv_col_idx;               // @ abr_sha3.h:99:10

  fv_new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (fv_row_idx = 32'd0; fv_row_idx < 32'd5; fv_row_idx = fv_row_idx + 32'd1) begin
    for (fv_col_idx = 32'd0; fv_col_idx < 32'd5; fv_col_idx = fv_col_idx + 32'd1) begin
      fv_new_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)] = fv_original_state[unsigned'((fv_col_idx + (32'd3 * fv_row_idx)) % 32'd5)][unsigned'(fv_col_idx)];
    end
  end

  return fv_new_state;
endfunction


function automatic logic unsigned [4:0][4:0][63:0] chi(logic unsigned [4:0][4:0][63:0] fv_original_state);
  logic unsigned [4:0][4:0][63:0] fv_new_state; // @ abr_sha3.h:108:3
  logic signed [31:0] fv_row_idx;               // @ abr_sha3.h:109:8
  logic signed [31:0] fv_col_idx;               // @ abr_sha3.h:110:10

  fv_new_state = '{ 0: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 1: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 2: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 3: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 }, 4: '{ 0: 64'd0, 1: 64'd0, 2: 64'd0, 3: 64'd0, 4: 64'd0 } };

  for (fv_row_idx = 32'd0; fv_row_idx < 32'd5; fv_row_idx = fv_row_idx + 32'd1) begin
    for (fv_col_idx = 32'd0; fv_col_idx < 32'd5; fv_col_idx = fv_col_idx + 32'd1) begin
      fv_new_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)] = fv_original_state[unsigned'(fv_col_idx)][unsigned'(fv_row_idx)] ^ ((~fv_original_state[unsigned'((fv_col_idx + 32'd1) % 32'd5)][unsigned'(fv_row_idx)]) & fv_original_state[unsigned'((fv_col_idx + 32'd2) % 32'd5)][unsigned'(fv_row_idx)]);
    end
  end

  return fv_new_state;
endfunction


function automatic logic unsigned [4:0][4:0][63:0] iota(logic unsigned [4:0][4:0][63:0] fv_original_state, logic signed [31:0] fv_round_idx);
  fv_original_state[64'd0][64'd0] = fv_original_state[64'd0][64'd0] ^ RC_VALUES[unsigned'(fv_round_idx)];
  return fv_original_state;
endfunction


endpackage
