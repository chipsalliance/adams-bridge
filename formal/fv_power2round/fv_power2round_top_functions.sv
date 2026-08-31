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
// | Created on 13.03.2025 at 09:29                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_power2round_top_functions;


function logic unsigned [7:0][9:0] compute_r1(logic unsigned [7:0][23:0] data);
  logic unsigned [7:0][9:0] result; // @ power2round_top_pk.h:79:13
  logic unsigned [23:0] sum0;       // @ power2round_top_pk.h:80:13
  logic unsigned [23:0] mask;       // @ power2round_top_pk.h:81:13
  logic signed [31:0] i;            // @ power2round_top_pk.h:83:17

  result = '{ 0: 10'd0, 1: 10'd0, 2: 10'd0, 3: 10'd0, 4: 10'd0, 5: 10'd0, 6: 10'd0, 7: 10'd0 };
  sum0 = 24'd0;
  mask = unsigned'(24'((32'd1 << 32'd10) - 32'd1));

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    sum0 = ((data[unsigned'(i)] << 32'd1) >> 32'd1) + 64'd4095;
    result[unsigned'(i)] = (sum0 >> 32'd13) & mask;
  end

  return result;
endfunction


function logic unsigned [7:0][12:0] compute_r0(logic unsigned [7:0][23:0] data);
  logic unsigned [7:0][12:0] result; // @ power2round_top_pk.h:91:13
  logic unsigned [7:0][9:0] r1;      // @ power2round_top_pk.h:92:13
  logic unsigned [23:0] sum1;        // @ power2round_top_pk.h:93:13
  logic unsigned [23:0] mask;        // @ power2round_top_pk.h:94:13
  logic signed [31:0] i;             // @ power2round_top_pk.h:97:17

  result = '{ 0: 13'd0, 1: 13'd0, 2: 13'd0, 3: 13'd0, 4: 13'd0, 5: 13'd0, 6: 13'd0, 7: 13'd0 };
  r1 = '{ 0: 10'd0, 1: 10'd0, 2: 10'd0, 3: 10'd0, 4: 10'd0, 5: 10'd0, 6: 10'd0, 7: 10'd0 };
  sum1 = 24'd0;
  mask = unsigned'(24'((32'd1 << 32'd13) - 32'd1));
  r1 = compute_r1(data);

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    sum1 = ((data[unsigned'(i)] << 32'd1) >> 32'd1) - (r1[unsigned'(i)] << 32'd13);
    result[unsigned'(i)] = sum1 & mask;
  end

  return result;
endfunction


function logic unsigned [7:0][12:0] skencode(logic unsigned [7:0][12:0] data);
  logic unsigned [7:0][12:0] result; // @ power2round_top_pk.h:105:13
  logic signed [31:0] i;             // @ power2round_top_pk.h:107:17

  result = '{ 0: 13'd0, 1: 13'd0, 2: 13'd0, 3: 13'd0, 4: 13'd0, 5: 13'd0, 6: 13'd0, 7: 13'd0 };

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    result[unsigned'(i)] = 32'd4096 - data[unsigned'(i)];
  end

  return result;
endfunction


function logic unsigned [1:0][31:0] compute_sk_data_output(logic unsigned [7:0][12:0] data, logic unsigned [167:0] thebuffer, logic unsigned [7:0] start, logic isFull);
  logic unsigned [1:0][31:0] result; // @ power2round_top_pk.h:114:13

  result = '{ 0: 32'd0, 1: 32'd0 };
  result[64'd0] = ((data[64'd0] << 32'd0) | (data[64'd1] << 32'd13)) | (data[64'd2] << 32'd26);
  result[64'd1] = ((data[64'd2] >> 32'd6) | (data[64'd3] << 32'd7)) | (data[64'd4] << 32'd20);
  return result;
endfunction


function logic unsigned [1:0][31:0] get_sk_data_output(logic unsigned [167:0] thebuffer);
  logic unsigned [1:0][31:0] result; // @ power2round_top_pk.h:121:13

  result = '{ 0: 32'd0, 1: 32'd0 };
  result[64'd0] = thebuffer;
  result[64'd1] = thebuffer >> 32'd32;
  return result;
endfunction


function logic unsigned [167:0] compute_buffer(logic unsigned [7:0][12:0] data, logic unsigned [167:0] thebuffer, logic unsigned [7:0] start, logic isFull);
  logic unsigned [167:0] result; // @ power2round_top_pk.h:128:13
  logic unsigned [167:0] temp;   // @ power2round_top_pk.h:132:17
  logic unsigned [7:0] shifter;  // @ power2round_top_pk.h:133:17

  result = 168'd0;

  if (isFull) begin
    result = thebuffer >> 32'd64;
  end else begin
    temp = (((((((data[64'd0] << 32'd0) | (data[64'd1] << 32'd13)) | (data[64'd2] << 32'd26)) | (data[64'd3] << 32'd39)) | (data[64'd4] << 32'd52)) | (data[64'd5] << 32'd65)) | (data[64'd6] << 32'd78)) | (data[64'd7] << 32'd91);
    shifter = 8'((start >= 64'd8) ? ((start * 64'd8) - 64'd64) : (start * 64'd8));
    temp = temp << shifter;
    result = thebuffer >> 32'd64;
    result = temp | result;
  end

  return result;
endfunction


endpackage
