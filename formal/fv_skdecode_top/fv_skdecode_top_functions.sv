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


package fv_skdecode_top_functions;


function automatic logic unsigned [3:0][23:0] decode_s1s2_a(logic unsigned [7:0][2:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] fv_decoded_data; // @ skdecode_top.h:67:13
  logic signed [31:0] fv_i;                   // @ skdecode_top.h:69:17

  // Fixed: dropped ">= 64'd0" -- data_to_be_decoded is unsigned, so that half of
  // the condition was always true (dead code, unreachable false branch). Also
  // removed the fv_decoded_data initializer below -- the loop unconditionally
  // overwrites all 4 elements every call, so the initial value was never read.
  //   fv_decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };
  for (fv_i = 32'd0; fv_i < 32'd4; fv_i = fv_i + 32'd1) begin
    if (data_to_be_decoded[unsigned'(fv_i)] < 64'd5) begin
      fv_decoded_data[unsigned'(fv_i)] = ((24'd2 - data_to_be_decoded[unsigned'(fv_i)]) + 64'd8380417) % 64'd8380417;
    end else begin
      fv_decoded_data[unsigned'(fv_i)] = 32'd0;
    end
  end

  return fv_decoded_data;
endfunction


function automatic logic unsigned [3:0][23:0] decode_s1s2_b(logic unsigned [7:0][2:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] fv_decoded_data; // @ skdecode_top.h:80:13
  logic signed [31:0] fv_i;                   // @ skdecode_top.h:82:17

  // Fixed: dropped ">= 64'd0" -- data_to_be_decoded is unsigned, so that half of
  // the condition was always true (dead code, unreachable false branch). Also
  // removed the fv_decoded_data initializer below -- the loop unconditionally
  // overwrites all 4 elements every call, so the initial value was never read.
  //   fv_decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };
  for (fv_i = 32'd4; fv_i < 32'd8; fv_i = fv_i + 32'd1) begin
    if (data_to_be_decoded[unsigned'(fv_i)] < 64'd5) begin
      fv_decoded_data[unsigned'(fv_i - 32'd4)] = ((24'd2 - data_to_be_decoded[unsigned'(fv_i)]) + 64'd8380417) % 64'd8380417;
    end else begin
      fv_decoded_data[unsigned'(fv_i - 32'd4)] = 32'd0;
    end
  end

  return fv_decoded_data;
endfunction


function automatic logic unsigned [3:0][23:0] decode_t0(logic unsigned [3:0][12:0] data_to_be_decoded);
  logic unsigned [3:0][23:0] fv_decoded_data; // @ skdecode_top.h:93:13
  logic signed [31:0] fv_i;                   // @ skdecode_top.h:95:17

  // Fixed: removed the fv_decoded_data initializer below -- this loop unconditionally
  // overwrites all 4 elements every call, so the initial value was never read.
  //   fv_decoded_data = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0 };
  for (fv_i = 32'd0; fv_i < 32'd4; fv_i = fv_i + 32'd1) begin
    fv_decoded_data[unsigned'(fv_i)] = ((24'd4096 - data_to_be_decoded[unsigned'(fv_i)]) + 64'd8380417) % 64'd8380417;
  end

  return fv_decoded_data;
endfunction


// Mirrors abr_splitter.sv's share0 math (mode=0/MLDSA): rand reduced mod MLDSA_Q.
// Splitter delays this by 2 cycles (rand_d1/rand_d2) -- callers must apply that
// delay themselves, e.g. $past(x, 2).
function automatic logic unsigned [3:0][23:0] reduce_rand_share0_mldsa(logic unsigned [95:0] rand_word);
  logic unsigned [3:0][23:0] fv_reduced;
  logic unsigned [22:0] fv_raw;
  int fv_i;

  for (fv_i = 0; fv_i < 4; fv_i = fv_i + 1) begin
    fv_raw = rand_word[fv_i*24 +: 23];
    fv_reduced[fv_i] = (fv_raw >= 23'd8380417) ? {1'b0, (fv_raw - 23'd8380417)} : {1'b0, fv_raw};
  end

  return fv_reduced;
endfunction


// Mirrors abr_splitter.sv's share1 math: (data - rand_reduced) mod MLDSA_Q.
// Unlike share0, share1's source register only updates when en_i is high (holds
// when idle) -- callers must model that hold themselves (see model_share1_pre_a/b).
function automatic logic unsigned [3:0][23:0] reduce_share1_mldsa(logic unsigned [95:0] data_word, logic unsigned [95:0] rand_word);
  logic unsigned [3:0][23:0] fv_result;
  logic unsigned [22:0] fv_data_coeff, fv_raw, fv_rand_reduced;
  int fv_i;

  for (fv_i = 0; fv_i < 4; fv_i = fv_i + 1) begin
    fv_data_coeff   = data_word[fv_i*24 +: 23];
    fv_raw          = rand_word[fv_i*24 +: 23];
    fv_rand_reduced = (fv_raw >= 23'd8380417) ? (fv_raw - 23'd8380417) : fv_raw;
    fv_result[fv_i] = (fv_data_coeff >= fv_rand_reduced) ? {1'b0, (fv_data_coeff - fv_rand_reduced)}
                                                          : {1'b0, (fv_data_coeff - fv_rand_reduced + 23'd8380417)};
  end

  return fv_result;
endfunction


endpackage
