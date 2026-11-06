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


package fv_ntt_butterfly_functions;


function automatic logic unsigned [22:0] compute_a_min_b(logic unsigned [22:0] a, logic unsigned [22:0] b, logic unsigned [0:0] mlkem);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly.h:15:5
  logic unsigned [63:0] fv_q;

  fv_result = 23'd0;
  fv_q = mlkem ? 64'd3329 : 64'd8380417;

  if (a >= b) begin
    fv_result = a - b;
  end else begin
    fv_result = 23'((a - b) + fv_q);
  end

  return fv_result;
endfunction


function automatic logic unsigned [22:0] div2(logic unsigned [22:0] data, logic unsigned [0:0] mlkem);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly.h:28:5
  logic unsigned [63:0] fv_q_div2_odd;

  fv_result = 23'd0;
  fv_q_div2_odd = mlkem ? 64'd1665 : 64'd4190209;

  if (data[32'd0] != 64'd0) begin
    fv_result = (data >> 32'd1) + unsigned'(23'(fv_q_div2_odd));
  end else begin
    fv_result = data >> 32'd1;
  end

  return fv_result;
endfunction


function automatic logic unsigned [22:0] compute_u(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm, logic unsigned [0:0] acc, logic unsigned [0:0] mlkem);
  logic unsigned [22:0] fv_result;  // @ ntt_butterfly.h:39:5
  logic unsigned [22:0] fv_result1; // @ ntt_butterfly.h:40:5
  logic unsigned [63:0] fv_q;
  logic unsigned [63:0] fv_q_div2_odd;

  fv_result = 23'd0;
  fv_q = mlkem ? 64'd3329 : 64'd8380417;
  fv_q_div2_odd = mlkem ? 64'd1665 : 64'd4190209;
  fv_result1 = 23'((u + v) % fv_q);

  if (nm == 64'd0) begin
    fv_result = 23'((u + 23'((v * w) % fv_q)) % fv_q);
  end else if (nm == 64'd1) begin
    if (fv_result1[32'd0] != 64'd0) begin
      fv_result = (fv_result1 >> 32'd1) + unsigned'(23'(fv_q_div2_odd));
    end else begin
      fv_result = fv_result1 >> 32'd1;
    end
  end else if (nm == 64'd2) begin
    if (acc != 64'd0) begin
      fv_result = 23'((w + 23'((u * v) % fv_q)) % fv_q);
    end else begin
      fv_result = 23'((u * v) % fv_q);
    end
  end else if (nm == 64'd3) begin
    fv_result = fv_result1;
  end else if (nm == 64'd4) begin
    fv_result = compute_a_min_b(u, v, mlkem);
  end else begin
    fv_result = 32'd0;
  end

  return fv_result;
endfunction


function automatic logic unsigned [22:0] compute_v(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm, logic unsigned [0:0] mlkem);
  logic unsigned [22:0] fv_result;  // @ ntt_butterfly.h:74:5
  logic unsigned [22:0] fv_result1; // @ ntt_butterfly.h:75:5
  logic unsigned [22:0] fv_result2; // @ ntt_butterfly.h:76:5
  logic unsigned [63:0] fv_q;

  fv_result = 23'd0;
  fv_q = mlkem ? 64'd3329 : 64'd8380417;
  fv_result1 = 23'((v * w) % fv_q);
  fv_result2 = compute_a_min_b(u, v, mlkem);

  if (nm == 64'd0) begin
    if (u >= fv_result1) begin
      fv_result = u - fv_result1;
    end else begin
      fv_result = 23'((u - fv_result1) + fv_q);
    end
  end else if (nm == 64'd1) begin
    fv_result = 23'((div2(fv_result2, mlkem) * w) % fv_q);
  end else begin
    fv_result = 32'd0;
  end

  return fv_result;
endfunction


function automatic logic unsigned [22:0] compute_pwm(logic unsigned [22:0] u, logic unsigned [22:0] v, logic unsigned [22:0] w, logic unsigned [2:0] nm, logic unsigned [0:0] acc, logic unsigned [0:0] mlkem);
  logic unsigned [22:0] fv_result; // @ ntt_butterfly.h:97:5
  logic unsigned [63:0] fv_q;

  fv_result = 23'd0;
  fv_q = mlkem ? 64'd3329 : 64'd8380417;

  if (nm == 64'd2) begin
    if (mlkem) begin
      fv_result = 23'd0; // MLKEM: pwm_res_o = 0 in PWM mode (result goes via pairwm path)
    end else if (acc != 64'd0) begin
      fv_result = 23'((w + 23'((u * v) % fv_q)) % fv_q);
    end else begin
      fv_result = 23'((u * v) % fv_q);
    end
  end else if (nm == 64'd3) begin
    fv_result = 23'((u + v) % fv_q);
  end else if (nm == 64'd4) begin
    fv_result = compute_a_min_b(u, v, mlkem);
  end else begin
    fv_result = 32'd0;
  end

  return fv_result;
endfunction


endpackage
