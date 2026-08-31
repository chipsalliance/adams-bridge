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

module fv_ntt_masked_BFU_mult_constraints

import fv_ntt_masked_BFU_mult_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_BFU_mult_functions::*;

(
input     pi_reset_n,
  input   pi_clk,

  // Ports
  
  input   pi_sub,

  input a_unsigned_46_2 pi_u,

  input a_unsigned_46_2 pi_v,
  
  input a_unsigned_2_46 po_res
);

default clocking default_clk @(posedge pi_clk); endclocking

//Constraint to limit the inputs value to Q (8380417)
property rnd_q;

    ntt_masked_BFU_mult.u[0] + ntt_masked_BFU_mult.u[1]  < ('h7FE001) &&
    ntt_masked_BFU_mult.v[0] + ntt_masked_BFU_mult.v[1] < ('h7FE001) 
    ;
endproperty
assume_rnd_q: assume property(disable iff (!pi_reset_n) rnd_q);

endmodule