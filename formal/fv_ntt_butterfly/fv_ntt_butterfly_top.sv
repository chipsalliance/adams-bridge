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

module fv_ntt_butterfly

import ntt_defines_pkg::*;
import ntt_butterfly_functions::*;

(
  input     pi_reset_n,
  input   pi_clk,

  // Ports
  
  input logic [2:0]  pi_mode,

  input   pi_accumulate,

  input   unsigned [22:0] pi_opu_i,

  input   unsigned [22:0] pi_opv_i,

  input   unsigned [22:0] pi_opw_i,

  input   unsigned [22:0] po_u_o,

  input   unsigned [22:0] po_v_o,

  input   unsigned [22:0] po_pwm_res_o
);

fv_constraints_wip fv_constraints_wip_i(.*);

endmodule

bind ntt_butterfly fv_ntt_butterfly fv_ntt_butterfly_i(
    .pi_clk (clk),
    .pi_reset_n (reset_n && !zeroize),
    .pi_mode(mode),
    .pi_accumulate(accumulate),
    .pi_opu_i (opu_i),
    .pi_opv_i (opv_i),
    .pi_opw_i (opw_i),
    .po_u_o(u_o),
    .po_v_o(v_o),
    .po_pwm_res_o(pwm_res_o)
);