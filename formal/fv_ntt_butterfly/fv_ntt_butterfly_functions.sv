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
// | Created on 19.03.2025 at 18:17                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_butterfly_functions;


function logic unsigned [22:0] compute_a_min_b(logic unsigned [22:0] a, logic unsigned [22:0] b);
  logic unsigned [22:0] result; // @ ntt_butterfly.h:15:5

  result = 23'd0;

  if (a >= b) begin
    result = a - b;
  end else begin
    result = (a - b) + 64'd8380417;
  end

  return result;
endfunction


function logic unsigned [22:0] div2(logic unsigned [22:0] data);
  logic unsigned [22:0] result; // @ ntt_butterfly.h:28:5

  result = 23'd0;

  if (data[32'd0] != 64'd0) begin
    result = (data >> 32'd1) + unsigned'(23'((32'd8380417 + 32'd1) / 32'd2));
  end else begin
    result = data >> 32'd1;
  end

  return result;
endfunction


function logic unsigned [22:0] compute_u(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm, logic unsigned [0:0] acc);
  logic unsigned [22:0] result;  // @ ntt_butterfly.h:39:5
  logic unsigned [22:0] result1; // @ ntt_butterfly.h:40:5

  result = 23'd0;
  result1 = 23'((u + v) % 64'd8380417);

  if (nm == 64'd0) begin
    result = (u + 23'((v * w) % 64'd8380417)) % 64'd8380417;
  end else if (nm == 64'd1) begin
    if (result1[32'd0] != 64'd0) begin
      result = (result1 >> 32'd1) + unsigned'(23'((32'd8380417 + 32'd1) / 32'd2));
    end else begin
      result = result1 >> 32'd1;
    end
  end else if (nm == 64'd2) begin
    if (acc != 64'd0) begin
      result = (w + 23'((u * v) % 64'd8380417)) % 64'd8380417;
    end else begin
      result = 23'((u * v) % 64'd8380417);
    end
  end else if (nm == 64'd3) begin
    result = result1;
  end else if (nm == 64'd4) begin
    result = compute_a_min_b(u, v);
  end else begin
    result = 32'd0;
  end

  return result;
endfunction


function logic unsigned [22:0] compute_v(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm);
  logic unsigned [22:0] result;  // @ ntt_butterfly.h:74:5
  logic unsigned [22:0] result1; // @ ntt_butterfly.h:75:5
  logic unsigned [22:0] result2; // @ ntt_butterfly.h:76:5
  logic unsigned [22:0] result3; // @ ntt_butterfly.h:77:5

  result = 23'd0;
  result1 = 23'((v * w) % 64'd8380417);
  result2 = compute_a_min_b(u, v);
  result3 = 23'((result2 >> 32'd1) + 64'h3FF001);

  if (nm == 64'd0) begin
    if (u >= result1) begin
      result = u - result1;
    end else begin
      result = (u - result1) + 64'd8380417;
    end
  end else if (nm == 64'd1) begin
    result = 23'((div2(result2) * w) % 64'd8380417);
  end else begin
    result = 32'd0;
  end

  return result;
endfunction


function logic unsigned [22:0] compute_pwm(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm, logic unsigned [0:0] acc);
  logic unsigned [22:0] result; // @ ntt_butterfly.h:97:5

  result = 23'd0;

  if (nm == 64'd2) begin
    if (acc != 64'd0) begin
      result = (w + 23'((u * v) % 64'd8380417)) % 64'd8380417;
    end else begin
      result = 23'((u * v) % 64'd8380417);
    end
  end else if (nm == 64'd3) begin
    result = 23'((u + v) % 64'd8380417);
  end else if (nm == 64'd4) begin
    result = compute_a_min_b(u, v);
  end else begin
    result = 32'd0;
  end

  return result;
endfunction


endpackage
