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
// | Created on 25.02.2025 at 12:37                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_sample_in_ball_ctrl_pkg::*;


// Functions

function logic unsigned [0:0] c_index_found(logic data_valid, a_unsigned_1_4 mask, a_unsigned_8_4 data, logic unsigned [7:0] rej);
  if (data_valid && (mask[3] == 1'd1) && (data[3] <= rej))
    return 1'd1;
  else if (data_valid && (mask[2] == 1'd1) && (data[2] <= rej))
    return 1'd1;
  else if (data_valid && (mask[1] == 1'd1) && (data[1] <= rej))
    return 1'd1;
  else if (data_valid && (mask[0] == 1'd1) && (data[0] <= rej))
    return 1'd1;
  else
    return 1'd0;
endfunction

function logic unsigned [0:0] c_rej_val_en(logic data_valid, a_unsigned_1_4 mask, a_unsigned_8_4 data, logic unsigned [7:0] rej, logic read_valid);
  logic unsigned [0:0] c_index_found_0_i;

  c_index_found_0_i = c_index_found(data_valid, mask, data, rej);

  return ((c_index_found_0_i != 1'd0) && read_valid);
endfunction

function logic unsigned [7:0] c_valid_sample(logic data_valid, a_unsigned_1_4 mask, a_unsigned_8_4 data, logic unsigned [7:0] rej);
  if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1)
    return data[2'd1];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && 1)
    return data[2'd2];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1)
    return data[2'd1];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && 1 && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && ((data_valid && (mask[3] == 1'd1)) && (data[3] <= rej)) && 1 && 1 && 1)
    return data[2'd3];
  else if (1 && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1)
    return data[2'd1];
  else if (1 && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && 1 && ((data_valid && (mask[2] == 1'd1)) && (data[2] <= rej)) && 1 && 1)
    return data[2'd2];
  else if (1 && 1 && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1 && ((data_valid && (mask[0] == 1'd1)) && (data[0] <= rej)))
    return data[2'd0];
  else if (1 && 1 && 1 && ((data_valid && (mask[1] == 1'd1)) && (data[1] <= rej)) && 1)
    return data[2'd1];
  else if (data_valid && (mask[0] == 1'd1) && (data[0] <= rej))
    return data[2'd0];
  else
    return data[2'd0];
endfunction

function a_unsigned_1_4 comp_mask_d(a_unsigned_1_4 mask, logic valid, logic i_f);
  if (valid && !i_f)
    return '{ 0: 1'd0, 1: mask[1], 2: mask[2], 3: mask[3] };
  else
    return mask;
endfunction

function logic unsigned [5:0] compute_addr(a_unsigned_8_4 data, logic unsigned [7:0] rej, a_bool_4 sampler_valid, logic valid);
  if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return data[1][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return data[2][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return data[1][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1)
    return data[3][7:2];
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return data[1][7:2];
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return data[2][7:2];
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return data[0][7:2];
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return data[1][7:2];
  else if (valid && sampler_valid[0] && (data[0] <= rej))
    return data[0][7:2];
  else if (valid)
    return data[64'd0][7:2];
  else
    return data[64'd0][7:2];
endfunction

function logic unsigned [1:0] compute_cs(a_unsigned_8_4 data, logic unsigned [7:0] rej, a_bool_4 sampler_valid, logic valid);
  if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1)
    return 2'd3;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return 2'd3;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return 2'd3;
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return 2'd3;
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return 2'd3;
  else if (valid && sampler_valid[0] && (data[0] <= rej))
    return 2'd3;
  else if (valid)
    return 2'd0;
  else
    return 2'd0;
endfunction

function a_unsigned_23_4 compute_data_0(a_unsigned_23_4 data, logic unsigned [7:0] index, logic sign);
  logic unsigned [1:0] lower_range_0_i;

  lower_range_0_i = lower_range(index);

  if ((lower_range_0_i == 2'd0))
    return '{ 0: (sign ? 23'd8380416 : 23'd1), 1: data[64'd1], 2: data[64'd2], 3: data[64'd3] };
  else if ((lower_range_0_i == 2'd1))
    return '{ 0: data[64'd0], 1: (sign ? 23'd8380416 : 23'd1), 2: data[64'd2], 3: data[64'd3] };
  else if ((lower_range_0_i == 2'd2))
    return '{ 0: data[64'd0], 1: data[64'd1], 2: (sign ? 23'd8380416 : 23'd1), 3: data[64'd3] };
  else
    return '{ 0: data[64'd0], 1: data[64'd1], 2: data[64'd2], 3: (sign ? 23'd8380416 : 23'd1) };
endfunction

function a_unsigned_23_4 compute_data_1(a_unsigned_23_4 data0, a_unsigned_23_4 data1, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j, logic sign);
  logic unsigned [5:0] upper_range_0_i;
  logic unsigned [5:0] upper_range_1_i;
  logic unsigned [1:0] lower_range_0_i;
  logic unsigned [1:0] lower_range_1_i;
  a_unsigned_23_4 compute_data_pre_0_i;
  a_unsigned_23_4 compute_data_0_0_i;

  upper_range_0_i = upper_range(index_i);
  upper_range_1_i = upper_range(index_j);
  lower_range_0_i = lower_range(index_i);
  lower_range_1_i = lower_range(index_j);
  compute_data_pre_0_i = compute_data_pre(data0, data1, index_i, index_j);
  compute_data_0_0_i = compute_data_0(compute_data_pre_0_i, index_j, sign);

  if ((upper_range_0_i != upper_range_1_i))
    return compute_data_pre_0_i;
  else
    return compute_data_0_0_i;
endfunction

function a_unsigned_23_4 compute_data_pre(a_unsigned_23_4 data0, a_unsigned_23_4 data1, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j);
  logic unsigned [1:0] lower_range_0_i;
  logic unsigned [1:0] lower_range_1_i;

  lower_range_0_i = lower_range(index_i);
  lower_range_1_i = lower_range(index_j);

  if ((lower_range_0_i == 2'd0))
    return '{ 0: data0[lower_range_1_i], 1: data1[64'd1], 2: data1[64'd2], 3: data1[64'd3] };
  else if ((lower_range_0_i == 2'd1))
    return '{ 0: data1[64'd0], 1: data0[lower_range_1_i], 2: data1[64'd2], 3: data1[64'd3] };
  else if ((lower_range_0_i == 2'd2))
    return '{ 0: data1[64'd0], 1: data1[64'd1], 2: data0[lower_range_1_i], 3: data1[64'd3] };
  else
    return '{ 0: data1[64'd0], 1: data1[64'd1], 2: data1[64'd2], 3: data0[lower_range_1_i] };
endfunction

function logic unsigned [1:0] compute_we(logic read_valid, logic unsigned [7:0] index_i, logic unsigned [7:0] index_j);
  logic unsigned [5:0] upper_range_0_i;
  logic unsigned [5:0] upper_range_1_i;

  upper_range_0_i = upper_range(index_i);
  upper_range_1_i = upper_range(index_j);

  if (!read_valid)
    return 2'd0;
  else if ((upper_range_0_i != upper_range_1_i))
    return 2'd3;
  else
    return 2'd2;
endfunction

function logic is_data_hold(a_unsigned_8_4 data, logic unsigned [7:0] rej, logic read_valid, a_bool_4 sampler_valid, logic valid);
  logic is_sampler_hold_0_i;
  logic is_shuffler_hold_0_i;

  is_sampler_hold_0_i = is_sampler_hold(data, rej, sampler_valid, valid);
  is_shuffler_hold_0_i = is_shuffler_hold(data, rej, read_valid, sampler_valid, valid);

  return (is_sampler_hold_0_i || is_shuffler_hold_0_i);
endfunction

function logic is_sampler_hold(a_unsigned_8_4 data, logic unsigned [7:0] rej, a_bool_4 sampler_valid, logic valid);
  if (valid && 1 && 1 && ((sampler_valid[2] && (data[2] <= rej)) && 1) && 1 && ((sampler_valid[1] && (data[1] <= rej)) && 1) && 1 && ((sampler_valid[0] && (data[0] <= rej)) && 1))
    return 1;
  else if (valid && 1 && 1 && ((sampler_valid[2] && (data[2] <= rej)) && 1) && 1 && ((sampler_valid[1] && (data[1] <= rej)) && 1) && 1)
    return 1;
  else if (valid && 1 && 1 && ((sampler_valid[2] && (data[2] <= rej)) && 1) && 1 && 1 && ((sampler_valid[0] && (data[0] <= rej)) && 1))
    return 1;
  else if (valid && 1 && 1 && ((sampler_valid[2] && (data[2] <= rej)) && 1) && 1 && 1)
    return 1;
  else if (valid && 1 && 1 && 1 && ((sampler_valid[1] && (data[1] <= rej)) && 1) && 1 && ((sampler_valid[0] && (data[0] <= rej)) && 1))
    return 1;
  else if (valid && 1 && 1 && 1 && ((sampler_valid[1] && (data[1] <= rej)) && 1) && 1)
    return 1;
  else if (valid && sampler_valid[0] && (data[0] <= rej))
    return 1;
  else if (valid)
    return 0;
  else
    return 0;
endfunction

function logic is_shuffler_hold(a_unsigned_8_4 data, logic unsigned [7:0] rej, logic read_valid, a_bool_4 sampler_valid, logic valid);
  if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && (sampler_valid[3] && (data[3] <= rej)) && 1 && 1 && 1)
    return !read_valid;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return !read_valid;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && 1 && (sampler_valid[2] && (data[2] <= rej)) && 1 && 1)
    return !read_valid;
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1 && (sampler_valid[0] && (data[0] <= rej)))
    return !read_valid;
  else if (valid && 1 && 1 && 1 && (sampler_valid[1] && (data[1] <= rej)) && 1)
    return !read_valid;
  else if (valid && sampler_valid[0] && (data[0] <= rej))
    return !read_valid;
  else if (valid)
    return 0;
  else
    return 0;
endfunction

function logic unsigned [1:0] lower_range(logic unsigned [7:0] index);
  return index[1:0];
endfunction

function logic unsigned [5:0] upper_range(logic unsigned [7:0] index);
  return index[7:2];
endfunction


module fv_sample_in_ball_ctrl_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic sib_data_in_port_vld,
  input logic sib_data_in_port_rdy,
  input a_unsigned_8_4 sib_data_in_port,

  input a_unsigned_8_4 shared_sib_data_in_port,

  input logic data_hold_o,

  input logic sib_done_o,

  input logic unsigned [1:0] cs_o,

  input logic unsigned [1:0] we_o,

  input a_unsigned_6_2 addr_o,

  input logic unsigned [7:0] rej_value_port,

  input logic unsigned [7:0] sampler_valid_port,

  input logic read_valid_port,

  input logic sign_buffer0_port,

  input a_unsigned_23_4 wrdata0_o,

  input a_unsigned_23_4 wrdata1_o,

  input a_unsigned_23_4 rddata0_port,

  input a_unsigned_23_4 rddata1_port,

  input logic data_valid_port,

  input a_bool_4 sampler_data_valid_port,

  input a_unsigned_1_4 sampler_mask,

  input logic unsigned [0:0] index_found,

  input logic unsigned [0:0] rej_value_en_out,

  input logic unsigned [7:0] valid_sample,

  input logic sampler_mask_en,

  input a_unsigned_1_4 sampler_mask_d,

  // States
  input logic IDLE,
  input logic SIGN_BUFFER,
  input logic ACTIVE,
  input logic DONE
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_23_4 compute_data_0_0_i;
assign compute_data_0_0_i = compute_data_0(rddata0_port, sampler_valid_port, sign_buffer0_port);

a_unsigned_23_4 compute_data_1_0_i;
assign compute_data_1_0_i = compute_data_1(rddata0_port, rddata1_port, rej_value_port, sampler_valid_port, sign_buffer0_port);

logic unsigned [0:0] c_index_found_0_i;
assign c_index_found_0_i = c_index_found(data_valid_port, sampler_mask, shared_sib_data_in_port, rej_value_port);

logic unsigned [7:0] c_valid_sample_0_i;
assign c_valid_sample_0_i = c_valid_sample(data_valid_port, sampler_mask, shared_sib_data_in_port, rej_value_port);

a_unsigned_1_4 comp_mask_d_0_i;
assign comp_mask_d_0_i = comp_mask_d(sampler_mask, data_valid_port, (c_index_found_0_i != 1'd0));

a_unsigned_6_2 addr_o_0_i;
assign addr_o_0_i = '{
  0: compute_addr(shared_sib_data_in_port, rej_value_port, sampler_data_valid_port, data_valid_port),
  1: upper_range(rej_value_port)
};

logic is_data_hold_0_i;
assign is_data_hold_0_i = is_data_hold(shared_sib_data_in_port, rej_value_port, read_valid_port, sampler_data_valid_port, data_valid_port);

logic unsigned [1:0] compute_cs_0_i;
assign compute_cs_0_i = compute_cs(shared_sib_data_in_port, rej_value_port, sampler_data_valid_port, data_valid_port);

logic unsigned [1:0] compute_we_0_i;
assign compute_we_0_i = compute_we(read_valid_port, rej_value_port, sampler_valid_port);

logic unsigned [0:0] c_rej_val_en_0_i;
assign c_rej_val_en_0_i = c_rej_val_en(data_valid_port, sampler_mask, shared_sib_data_in_port, rej_value_port, read_valid_port);

logic is_sampler_hold_0_i;
assign is_sampler_hold_0_i = is_sampler_hold(shared_sib_data_in_port, rej_value_port, sampler_data_valid_port, data_valid_port);

logic is_shuffler_hold_0_i;
assign is_shuffler_hold_0_i = is_shuffler_hold(shared_sib_data_in_port, rej_value_port, read_valid_port, sampler_data_valid_port, data_valid_port);


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property run_reset_p;
  reset_sequence |->
  IDLE &&
  addr_o == addr_o_0_i &&
  cs_o == 2'd0 &&
  data_hold_o == 0 &&
  index_found == c_index_found_0_i &&
  rej_value_en_out == 1'd0 &&
  //sampler_mask_d == comp_mask_d_0_i &&
  sampler_mask_en == 0 &&
  sib_done_o == 0 &&
  valid_sample == c_valid_sample_0_i &&
  we_o == 2'd0 &&
  wrdata0_o == compute_data_0_0_i &&
  wrdata1_o == compute_data_1_0_i;
endproperty
run_reset_a: assert property (run_reset_p);


property run_ACTIVE_to_ACTIVE_p;
  ACTIVE
|->
  ACTIVE &&
  addr_o == addr_o_0_i &&
  cs_o == compute_cs_0_i &&
  data_hold_o == is_data_hold_0_i &&
  index_found == c_index_found_0_i &&
  rej_value_en_out == c_rej_val_en_0_i &&
  //sampler_mask_d == comp_mask_d_0_i &&
  sampler_mask_en == (((c_index_found_0_i != 1'd0) && is_sampler_hold_0_i) && !is_shuffler_hold_0_i) &&
  sib_done_o == 0 &&
  valid_sample == c_valid_sample_0_i &&
  we_o == compute_we_0_i &&
  wrdata0_o == compute_data_0_0_i &&
  wrdata1_o == compute_data_1_0_i;
endproperty
run_ACTIVE_to_ACTIVE_a: assert property (disable iff(!rst_n) run_ACTIVE_to_ACTIVE_p);


property run_DONE_to_DONE_p;
  DONE
|->
  DONE &&
  addr_o == addr_o_0_i &&
  cs_o == 2'd0 &&
  data_hold_o == 0 &&
  index_found == c_index_found_0_i &&
  rej_value_en_out == 1'd0 &&
  //sampler_mask_d == comp_mask_d_0_i &&
  sampler_mask_en == 0 &&
  sib_done_o == 1 &&
  valid_sample == c_valid_sample_0_i &&
  we_o == 2'd0 &&
  wrdata0_o == compute_data_0_0_i &&
  wrdata1_o == compute_data_1_0_i;
endproperty
run_DONE_to_DONE_a: assert property (disable iff(!rst_n) run_DONE_to_DONE_p);


property run_IDLE_to_IDLE_p;
  IDLE
|->
  IDLE &&
  addr_o == addr_o_0_i &&
  cs_o == 2'd0 &&
  data_hold_o == 0 &&
  index_found == c_index_found_0_i &&
  rej_value_en_out == 1'd0 &&
  //sampler_mask_d == comp_mask_d_0_i &&
  sampler_mask_en == 0 &&
  sib_done_o == 0 &&
  valid_sample == c_valid_sample_0_i &&
  we_o == 2'd0 &&
  wrdata0_o == compute_data_0_0_i &&
  wrdata1_o == compute_data_1_0_i;
endproperty
run_IDLE_to_IDLE_a: assert property (disable iff(!rst_n) run_IDLE_to_IDLE_p);


property run_SIGN_BUFFER_to_SIGN_BUFFER_p;
  SIGN_BUFFER
|->
  SIGN_BUFFER &&
  addr_o == addr_o_0_i &&
  cs_o == 2'd0 &&
  data_hold_o == 0 &&
  index_found == c_index_found_0_i &&
  rej_value_en_out == 1'd0 &&
  //sampler_mask_d == comp_mask_d_0_i &&
  sampler_mask_en == 0 &&
  sib_done_o == 0 &&
  valid_sample == c_valid_sample_0_i &&
  we_o == 2'd0 &&
  wrdata0_o == compute_data_0_0_i &&
  wrdata1_o == compute_data_1_0_i;
endproperty
run_SIGN_BUFFER_to_SIGN_BUFFER_a: assert property (disable iff(!rst_n) run_SIGN_BUFFER_to_SIGN_BUFFER_p);


property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
run_IDLE_eventually_left_a: assert property (disable iff(!rst_n) run_IDLE_eventually_left_p);


property run_SIGN_BUFFER_eventually_left_p;
  SIGN_BUFFER
|->
  s_eventually(!SIGN_BUFFER);
endproperty
run_SIGN_BUFFER_eventually_left_a: assert property (disable iff(!rst_n) run_SIGN_BUFFER_eventually_left_p);


property run_ACTIVE_eventually_left_p;
  ACTIVE
|->
  s_eventually(!ACTIVE);
endproperty
run_ACTIVE_eventually_left_a: assert property (disable iff(!rst_n) run_ACTIVE_eventually_left_p);


property run_DONE_eventually_left_p;
  DONE
|->
  s_eventually(!DONE);
endproperty
//run_DONE_eventually_left_a: assert property (disable iff(!rst_n) run_DONE_eventually_left_p);
//commented because DONE to IDLE transition doesn't exist as per design

parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  run_consistency_onehot0_state: assert property($onehot0({ ACTIVE, DONE, IDLE, SIGN_BUFFER }));
end


endmodule
