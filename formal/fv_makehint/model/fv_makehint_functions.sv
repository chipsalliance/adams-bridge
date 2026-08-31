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
// | Created on 14.02.2025 at 11:54                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_makehint_functions;


function logic unsigned [3:0][0:0] hintgen_comp(logic unsigned [95:0] r_var, logic unsigned [3:0][0:0] z_neq_z_var);
  logic unsigned [95:0] r;                  // @ makehint.h:87:13
  logic unsigned [3:0][0:0] z_neq_z;        // @ makehint.h:88:13
  logic unsigned [0:0] r_lt_gamma2;         // @ makehint.h:90:13
  logic unsigned [0:0] r_gt_q_minus_gamma2; // @ makehint.h:91:13
  logic unsigned [0:0] r_eq_q_minus_gamma2; // @ makehint.h:92:13
  logic unsigned [0:0] or1_res;             // @ makehint.h:93:13
  logic unsigned [0:0] or2_res;             // @ makehint.h:93:13
  logic unsigned [0:0] and_res;             // @ makehint.h:93:13
  logic unsigned [0:0] not_res;             // @ makehint.h:93:13
  logic unsigned [3:0][0:0] hint;           // @ makehint.h:95:13
  logic unsigned [22:0] r_calc;             // @ makehint.h:97:13
  logic unsigned [22:0] i;                  // @ makehint.h:98:18

  r = r_var;
  z_neq_z = z_neq_z_var;
  r_lt_gamma2 = 1'd0;
  r_gt_q_minus_gamma2 = 1'd0;
  r_eq_q_minus_gamma2 = 1'd0;
  or1_res = 1'd0;
  or2_res = 1'd0;
  and_res = 1'd0;
  not_res = 1'd0;
  hint = '{ 0: 1'd0, 1: 1'd0, 2: 1'd0, 3: 1'd0 };
  r_calc = 23'd0;

  for (i = 23'd0; i < 23'd4; i = i + 23'd1) begin
    r_calc = r[signed'(32'((i * 23'd24))) +: 23];

    if (r_calc <= 64'd261888) begin
      r_lt_gamma2 = 1'd1;
    end else begin
      r_lt_gamma2 = 1'd0;
    end

    if (r_calc >= 64'd8118529) begin
      r_gt_q_minus_gamma2 = 1'd1;
    end else begin
      r_gt_q_minus_gamma2 = 1'd0;
    end

    if (r_calc == 64'd8118529) begin
      r_eq_q_minus_gamma2 = 1'd1;
    end else begin
      r_eq_q_minus_gamma2 = 1'd0;
    end

    or1_res = r_lt_gamma2 | r_gt_q_minus_gamma2;
    and_res = r_eq_q_minus_gamma2 & z_neq_z[i];
    or2_res = ((or1_res != 64'd0) ? 1'd0 : 1'd1) | and_res;
    hint[i] = or2_res;
  end

  return hint;
endfunction


function logic unsigned [3:0][7:0] index_comp(logic unsigned [7:0] index_count);
  logic unsigned [3:0][7:0] index; // @ makehint.h:128:11
  logic unsigned [7:0] i;          // @ makehint.h:129:16

  index = '{ 0: 8'd0, 1: 8'd0, 2: 8'd0, 3: 8'd0 };

  for (i = 8'd0; i < 64'd4; i = i + 8'd1) begin
    index[i] = index_count + i;
  end

  return index;
endfunction


function logic unsigned [7:0][7:0] max_index_buffer_comp(logic unsigned [7:0][7:0] max_index_buffer_var, logic unsigned [7:0] hintsum);
  logic unsigned [7:0][7:0] max_index_buffer; // @ makehint.h:136:11
  logic unsigned [7:0] i;                     // @ makehint.h:137:16

  max_index_buffer = max_index_buffer_var;

  for (i = 8'd1; i < 64'd8; i = i + 8'd1) begin
    max_index_buffer[i - 64'd1] = max_index_buffer[i];
  end

  max_index_buffer[64'd7] = hintsum;
  return max_index_buffer;
endfunction


function logic unsigned [3:0][7:0] max_index_buffer_data_comp(logic unsigned [63:0] max_index_buffer_var, logic unsigned [7:0] sel);
  logic unsigned [3:0][7:0] wr_data;      // @ makehint.h:145:11
  logic unsigned [63:0] max_index_buffer; // @ makehint.h:146:11

  wr_data = '{ 0: 8'd0, 1: 8'd0, 2: 8'd0, 3: 8'd0 };
  max_index_buffer = max_index_buffer_var;

  if (sel == 64'd0) begin
    wr_data[64'd3] = max_index_buffer[32'd7:32'd0];
    wr_data[64'd2] = 32'd0;
    wr_data[64'd1] = 32'd0;
    wr_data[64'd0] = 32'd0;
  end else if (sel == 64'd1) begin
    wr_data[64'd3] = max_index_buffer[32'd39:32'd32];
    wr_data[64'd2] = max_index_buffer[32'd31:32'd24];
    wr_data[64'd1] = max_index_buffer[32'd23:32'd16];
    wr_data[64'd0] = max_index_buffer[32'd15:32'd8];
  end else if (sel == 64'd2) begin
    wr_data[64'd3] = 32'd0;
    wr_data[64'd2] = max_index_buffer[32'd63:32'd56];
    wr_data[64'd1] = max_index_buffer[32'd55:32'd48];
    wr_data[64'd0] = max_index_buffer[32'd47:32'd40];
  end

  return wr_data;
endfunction


endpackage
