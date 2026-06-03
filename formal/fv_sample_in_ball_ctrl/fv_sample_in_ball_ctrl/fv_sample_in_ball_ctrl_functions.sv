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
// | Created on 16.01.2025 at 14:15                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sample_in_ball_ctrl_functions;


function logic unsigned [5:0] compute_addr(logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej, logic [3:0] sampler_valid);
  logic unsigned [7:0] result; // @ sample_in_ball_ctrl.h:47:11
  logic signed [31:0] i;       // @ sample_in_ball_ctrl.h:49:15

  result = data[64'd0];

  for (i = 32'd3; i >= 32'd0; i = i - 32'd1) begin
    if (sampler_valid[unsigned'(i)] && (data[unsigned'(i)] <= rej)) begin
      result = data[unsigned'(i)];
    end
  end

  return result[32'd7:32'd2];
endfunction


function logic unsigned [5:0] upper_range(logic unsigned [7:0] index);
  logic unsigned [7:0] result; // @ sample_in_ball_ctrl.h:59:11

  result = index;
  return result[32'd7:32'd2];
endfunction


function logic unsigned [1:0] lower_range(logic unsigned [7:0] index);
  logic unsigned [7:0] result; // @ sample_in_ball_ctrl.h:65:11

  result = index;
  return result[32'd1:32'd0];
endfunction


function logic unsigned [3:0][22:0] compute_data_0(logic unsigned [3:0][22:0] data, logic unsigned [7:0] index, logic sign);
  logic unsigned [3:0][22:0] result; // @ sample_in_ball_ctrl.h:71:11
  logic unsigned [1:0] j;            // @ sample_in_ball_ctrl.h:72:11

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };
  j = lower_range(index);

  if (j == 64'd0) begin
    result[64'd3] = data[64'd3];
    result[64'd2] = data[64'd2];
    result[64'd1] = data[64'd1];
    result[64'd0] = sign ? 23'd8380416 : 23'd1;
  end else if (j == 64'd1) begin
    result[64'd3] = data[64'd3];
    result[64'd2] = data[64'd2];
    result[64'd1] = sign ? 23'd8380416 : 23'd1;
    result[64'd0] = data[64'd0];
  end else if (j == 64'd2) begin
    result[64'd3] = data[64'd3];
    result[64'd2] = sign ? 23'd8380416 : 23'd1;
    result[64'd1] = data[64'd1];
    result[64'd0] = data[64'd0];
  end else if (j == 64'd3) begin
    result[64'd3] = sign ? 23'd8380416 : 23'd1;
    result[64'd2] = data[64'd2];
    result[64'd1] = data[64'd1];
    result[64'd0] = data[64'd0];
  end

  return result;
endfunction


function logic unsigned [3:0][22:0] compute_data_pre(logic unsigned [3:0][22:0] data0, logic unsigned [3:0][22:0] data1, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j);
  logic unsigned [3:0][22:0] result; // @ sample_in_ball_ctrl.h:103:11
  logic unsigned [1:0] i;            // @ sample_in_ball_ctrl.h:104:11
  logic unsigned [1:0] j;            // @ sample_in_ball_ctrl.h:105:11

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };
  i = lower_range(index_i);
  j = lower_range(index_j);

  if (i == 64'd0) begin
    result[64'd3] = data1[64'd3];
    result[64'd2] = data1[64'd2];
    result[64'd1] = data1[64'd1];
    result[64'd0] = data0[j];
  end else if (i == 64'd1) begin
    result[64'd3] = data1[64'd3];
    result[64'd2] = data1[64'd2];
    result[64'd1] = data0[j];
    result[64'd0] = data1[64'd0];
  end else if (i == 64'd2) begin
    result[64'd3] = data1[64'd3];
    result[64'd2] = data0[j];
    result[64'd1] = data1[64'd1];
    result[64'd0] = data1[64'd0];
  end else if (i == 64'd3) begin
    result[64'd3] = data0[j];
    result[64'd2] = data1[64'd2];
    result[64'd1] = data1[64'd1];
    result[64'd0] = data1[64'd0];
  end

  return result;
endfunction


function logic unsigned [3:0][22:0] compute_data_1(logic unsigned [3:0][22:0] data0, logic unsigned [3:0][22:0] data1, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j, logic sign);
  logic unsigned [3:0][22:0] result; // @ sample_in_ball_ctrl.h:136:11
  logic unsigned [5:0] addr_i;       // @ sample_in_ball_ctrl.h:137:11
  logic unsigned [5:0] addr_j;       // @ sample_in_ball_ctrl.h:138:11
  logic unsigned [1:0] i;            // @ sample_in_ball_ctrl.h:139:11
  logic unsigned [1:0] j;            // @ sample_in_ball_ctrl.h:140:11

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };
  addr_i = upper_range(index_i);
  addr_j = upper_range(index_j);
  i = lower_range(index_i);
  j = lower_range(index_j);

  if (addr_i != addr_j) begin
    result = compute_data_pre(data0, data1, index_i, index_j);
  end else begin
    result = compute_data_0(compute_data_pre(data0, data1, index_i, index_j), index_j, sign);
  end

  return result;
endfunction


function logic is_sampler_hold(logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej, logic [3:0] sampler_valid);
  logic result;          // @ sample_in_ball_ctrl.h:153:11
  logic signed [31:0] i; // @ sample_in_ball_ctrl.h:154:15

  result = 0;

  for (i = 32'd3; i >= 32'd0; i = i - 32'd1) begin
    if ((sampler_valid[unsigned'(i)] && (data[unsigned'(i)] <= rej)) && (i != 32'd3)) begin
      result = 1;
    end
  end

  return result;
endfunction


function logic is_shuffler_hold(logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej, logic read_valid, logic [3:0] sampler_valid);
  logic result;          // @ sample_in_ball_ctrl.h:163:11
  logic signed [31:0] i; // @ sample_in_ball_ctrl.h:164:15

  result = 0;

  for (i = 32'd3; i >= 32'd0; i = i - 32'd1) begin
    if (sampler_valid[unsigned'(i)] && (data[unsigned'(i)] <= rej)) begin
      result = 1;
    end
  end

  return result && (!read_valid);
endfunction


function logic is_data_hold(logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej, logic read_valid, logic [3:0] sampler_valid);
  return is_sampler_hold(data, rej, sampler_valid) || is_shuffler_hold(data, rej, read_valid, sampler_valid);
endfunction


function logic unsigned [1:0] compute_cs(logic unsigned [3:0][7:0] data, logic unsigned [7:0] rej, logic [3:0] sampler_valid);
  logic unsigned [1:0] result; // @ sample_in_ball_ctrl.h:178:11
  logic signed [31:0] i;       // @ sample_in_ball_ctrl.h:179:15

  result = 2'd0;

  for (i = 32'd3; i >= 32'd0; i = i - 32'd1) begin
    if (sampler_valid[unsigned'(i)] && (data[unsigned'(i)] <= rej)) begin
      result = 32'd3;
    end
  end

  return result;
endfunction


function logic unsigned [1:0] compute_we(logic read_valid, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j);
  logic unsigned [5:0] addr_i; // @ sample_in_ball_ctrl.h:188:11
  logic unsigned [5:0] addr_j; // @ sample_in_ball_ctrl.h:189:11

  addr_i = upper_range(index_i);
  addr_j = upper_range(index_j);

  if (!read_valid) begin
    return 2'd0;
  end else begin
    if (addr_i != addr_j) begin
      return 2'd3;
    end else begin
      return 2'd2;
    end
  end
endfunction


endpackage
