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
// | Created on 06.02.2025 at 15:24                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_ntt_masked_pwm_functions;


function logic unsigned [45:0] add(logic unsigned [45:0] u, logic unsigned [1:0][45:0] v);
  logic unsigned [45:0] temp; // @ ntt_masked_pwm.h:15:5

  temp = 46'd0;
  temp = 46'((((u + v[64'd0]) + v[64'd1]) % 64'h400000000000) % 64'd8380417);
  //temp = 46'(((u) % 64'h400000000000) % 64'd8380417);
  return temp;
endfunction


function logic unsigned [45:0] mult(logic unsigned [1:0][45:0] u, logic unsigned [1:0][45:0] v);
  return 46'((((u[64'd0] + u[64'd1]) * (v[64'd0] + v[64'd1])) % 64'h400000000000) % 64'd8380417);
endfunction


function logic unsigned [45:0] compute_pwm(logic unsigned [1:0][45:0] u, logic unsigned [1:0][45:0] v, logic unsigned [1:0][45:0] w, logic unsigned [0:0] acc);
  if (acc != 64'd0) begin
    return add(mult(u, v), w);
  end else begin
    return mult(u, v);
  end
endfunction


endpackage
