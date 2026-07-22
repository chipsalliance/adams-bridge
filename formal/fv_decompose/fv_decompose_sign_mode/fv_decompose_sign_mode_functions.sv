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
// | Created on 20.01.2025 at 15:16                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package decompose_sign_mode_functions;


function logic unsigned [3:0] r1_lut(logic unsigned [22:0] a);
  if (a <= 23'd261888) begin
    return 4'd0;
  end else if (a <= unsigned'(23'(32'd3 * 32'd261888))) begin
    return 4'd1;
  end else if (a <= unsigned'(23'(32'd5 * 32'd261888))) begin
    return 4'd2;
  end else if (a <= unsigned'(23'(32'd7 * 32'd261888))) begin
    return 4'd3;
  end else if (a <= unsigned'(23'(32'd9 * 32'd261888))) begin
    return 4'd4;
  end else if (a <= unsigned'(23'(32'd11 * 32'd261888))) begin
    return 4'd5;
  end else if (a <= unsigned'(23'(32'd13 * 32'd261888))) begin
    return 4'd6;
  end else if (a <= unsigned'(23'(32'd15 * 32'd261888))) begin
    return 4'd7;
  end else if (a <= unsigned'(23'(32'd17 * 32'd261888))) begin
    return 4'd8;
  end else if (a <= unsigned'(23'(32'd19 * 32'd261888))) begin
    return 4'd9;
  end else if (a <= unsigned'(23'(32'd21 * 32'd261888))) begin
    return 4'd10;
  end else if (a <= unsigned'(23'(32'd23 * 32'd261888))) begin
    return 4'd11;
  end else if (a <= unsigned'(23'(32'd25 * 32'd261888))) begin
    return 4'd12;
  end else if (a <= unsigned'(23'(32'd27 * 32'd261888))) begin
    return 4'd13;
  end else if (a <= unsigned'(23'(32'd29 * 32'd261888))) begin
    return 4'd14;
  end else if (a <= unsigned'(23'(32'd31 * 32'd261888))) begin
    return 4'd15;
  end else begin
    return 4'd0;
  end
endfunction


function logic unsigned [3:0][3:0] compute_r1(logic unsigned [3:0][22:0] data);
  logic unsigned [3:0][3:0] result; // @ decompose_sign_mode.h:86:3
  logic signed [31:0] i;            // @ decompose_sign_mode.h:88:7

  result = '{ 0: 4'd0, 1: 4'd0, 2: 4'd0, 3: 4'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    result[unsigned'(i)] = r1_lut(data[unsigned'(i)]);
  end

  return result;
endfunction


function logic unsigned [3:0][0:0] compute_z(logic unsigned [3:0][22:0] data);
  logic unsigned [3:0][0:0] result; // @ decompose_sign_mode.h:95:3
  logic signed [31:0] i;            // @ decompose_sign_mode.h:97:7

  result = '{ 0: 1'd0, 1: 1'd0, 2: 1'd0, 3: 1'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if (r1_lut(data[unsigned'(i)]) == 64'd0) begin
      result[unsigned'(i)] = 32'd0;
    end else begin
      result[unsigned'(i)] = 32'd1;
    end
  end

  return result;
endfunction


function logic unsigned [18:0] compute_r0_mod_2GAMMA2(logic unsigned [22:0] data);
  return 19'(data % unsigned'(19'(32'd2 * 32'd261888)));
endfunction


function logic unsigned [22:0] compute_r0_mod_q(logic unsigned [18:0] data);
  if (data <= 18'd261888) begin
    return data;
  end else begin
    return 23'(data + 64'd7856641);
  end
endfunction


function logic unsigned [3:0][22:0] compute_r0(logic unsigned [3:0][22:0] data);
  logic unsigned [3:0][22:0] result; // @ decompose_sign_mode.h:125:3
  logic signed [31:0] i;             // @ decompose_sign_mode.h:127:7

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if (data[unsigned'(i)] > unsigned'(23'(32'd31 * 32'd261888))) begin
      result[unsigned'(i)] = data[unsigned'(i)];
    end else begin
      result[unsigned'(i)] = compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[unsigned'(i)]));
    end
  end

  return result;
endfunction


function logic unsigned [3:0][22:0] compute_r0_1(logic unsigned [3:0][22:0] data, logic valid);
  logic unsigned [3:0][22:0] result; // @ decompose_sign_mode.h:139:3
  logic signed [31:0] i;             // @ decompose_sign_mode.h:141:7

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if (data[unsigned'(i)] > unsigned'(23'(32'd31 * 32'd261888))) begin
      result[unsigned'(i)] = data[unsigned'(i)];
    end else begin
      if (!valid) begin
        result[unsigned'(i)] = 32'd0;
      end else begin
        result[unsigned'(i)] = compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[unsigned'(i)]));
      end
    end
  end

  return result;
endfunction


function logic unsigned [3:0][22:0] compute_r0_2(logic unsigned [3:0][22:0] data, logic unsigned [3:0] valid, logic unsigned [3:0][22:0] data2);
  logic unsigned [3:0][22:0] result; // @ decompose_sign_mode.h:158:3
  logic signed [31:0] i;             // @ decompose_sign_mode.h:160:7

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if (data[unsigned'(i)] > unsigned'(23'(32'd31 * 32'd261888))) begin
      result[unsigned'(i)] = data[unsigned'(i)];
    end else begin
      if (valid == 64'd0) begin
        result[unsigned'(i)] = data2[unsigned'(i)];
      end else begin
        result[unsigned'(i)] = compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[unsigned'(i)]));
      end
    end
  end

  return result;
endfunction


function logic unsigned [3:0][22:0] compute_r0_3(logic unsigned [3:0][22:0] data, logic valid, logic unsigned [3:0][22:0] data2);
  logic unsigned [3:0][22:0] result; // @ decompose_sign_mode.h:177:3
  logic signed [31:0] i;             // @ decompose_sign_mode.h:179:7

  result = '{ 0: 23'd0, 1: 23'd0, 2: 23'd0, 3: 23'd0 };

  for (i = 32'd0; i < 32'd4; i = i + 32'd1) begin
    if (data[unsigned'(i)] > unsigned'(23'(32'd31 * 32'd261888))) begin
      result[unsigned'(i)] = data[unsigned'(i)];
    end else begin
      if (!valid) begin
        result[unsigned'(i)] = data2[unsigned'(i)];
      end else begin
        result[unsigned'(i)] = compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[unsigned'(i)]));
      end
    end
  end

  return result;
endfunction


function logic is_buffer(logic unsigned [13:0] data);
  if ((data % 64'd4) == 64'd3) begin
    return 1;
  end else begin
    return 0;
  end
endfunction


endpackage
