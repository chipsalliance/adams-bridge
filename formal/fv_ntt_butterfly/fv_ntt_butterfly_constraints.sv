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

module fv_constraints_wip

import ntt_defines_pkg::*;
import ntt_butterfly_functions::*;

(
input     pi_reset_n,
  input   pi_clk,

  // Ports
  
  input logic [2:0]   pi_mode,

  input   pi_accumulate,

  input   unsigned [22:0] pi_opu_i,

  input   unsigned [22:0] pi_opv_i,

  input   unsigned [22:0] pi_opw_i,

  input   unsigned [22:0] po_u_o,

  input   unsigned [22:0] po_v_o,

  input   unsigned [22:0] po_pwm_res_o
);

default clocking default_clk @(posedge pi_clk); endclocking

//Constraint to make mode selection signal input stable
property stable_mode;
    $stable(ntt_butterfly.mode);
endproperty
assume_stable_mode: assume property(disable iff (!pi_reset_n) stable_mode);

//Constraint to limit the input value to Q (8380417)
property max_input;
    ntt_butterfly.opu_i < 'h7fe001 &&
    ntt_butterfly.opv_i < 'h7fe001 &&
    ntt_butterfly.opw_i < 'h7fe001;
endproperty
assume_max_input: assume property(disable iff (!pi_reset_n) max_input);

//Constraint to make accumulate input signal stable
property stable_acc;
    $stable(ntt_butterfly.accumulate);
endproperty
assume_stable_acc: assume property(disable iff (!pi_reset_n) stable_acc);

//Constraint to make mlkem input 0
property no_mlkem;
    !ntt_butterfly.mlkem;
endproperty
assume_no_mlkem: assume property(disable iff (!pi_reset_n) no_mlkem);

endmodule