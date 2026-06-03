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

module fv_ntt_masked_gs_butterfly_constraints

import fv_ntt_masked_gs_butterfly_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_gs_butterfly_functions::*;

(
input     pi_reset_n,
  input   pi_clk,

  // Ports
  
  input   pi_sub,

  input a_unsigned_46_2 pi_u,

  input a_unsigned_46_2 pi_v,

  input a_unsigned_46_2 pi_w
);

default clocking default_clk @(posedge pi_clk); endclocking


//Constraint to limit the input value to Q (8380417)
property rnd_q;

    ntt_masked_gs_butterfly.opu_i[0] + ntt_masked_gs_butterfly.opu_i[1]  < 'h7FE001 &&
    ntt_masked_gs_butterfly.opv_i[0] + ntt_masked_gs_butterfly.opv_i[1] < 'h7FE001 &&
    ntt_masked_gs_butterfly.opw_i[0] + ntt_masked_gs_butterfly.opw_i[1] < 'h7FE001 
    ;
endproperty
assume_rnd_q: assume property(disable iff (!pi_reset_n) rnd_q);

//Constraint to make mode selection signal input stable
property stable_mode;
    $stable(ntt_masked_gs_butterfly.mode);
endproperty
assume_stable_mode: assume property(disable iff (!pi_reset_n) stable_mode);

//Constraint to make accumulate input signal stable
property stable_acc;
    $stable(ntt_masked_gs_butterfly.accumulate);
endproperty
assume_stable_acc: assume property(disable iff (!pi_reset_n) stable_acc);

endmodule