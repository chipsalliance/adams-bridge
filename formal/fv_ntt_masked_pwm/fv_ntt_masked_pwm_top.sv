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

module fv_ntt_masked_pwm_top

import fv_ntt_masked_pwm_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_pwm_functions::*;

(
  input     pi_reset_n,
  input   pi_clk,

  // Ports
  
  input   pi_sub,

  input a_unsigned_46_2 pi_u,

  input a_unsigned_46_2 pi_v,

  input a_unsigned_46_2 pi_w
  
  //input a_unsigned_2_46 po_res
);

fv_ntt_masked_pwm_constraints fv_constraints_i(.*);

endmodule

bind ntt_masked_pwm fv_ntt_masked_pwm_top fv_ntt_masked_pwm_i(
    .pi_clk (clk),
    .pi_reset_n (reset_n && !zeroize),
    .pi_u (u),
    .pi_v (v),
    .pi_w (w)
    //.po_res(res)
);