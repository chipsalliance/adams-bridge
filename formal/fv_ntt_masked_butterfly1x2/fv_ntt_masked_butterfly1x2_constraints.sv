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

module fv_ntt_masked_butterfly1x2_constraints

import fv_ntt_masked_butterfly1x2_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_butterfly1x2_functions::*;

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

//Constraint to limit the inputs value to Q (8380417)
property input_constraint;

    ntt_masked_butterfly1x2.uvw_i.u00_i[0] + ntt_masked_butterfly1x2.uvw_i.u00_i[1]  < 'h7FE001 &&
    ntt_masked_butterfly1x2.uvw_i.v00_i[0] + ntt_masked_butterfly1x2.uvw_i.v00_i[1]  < 'h7FE001 &&
    ntt_masked_butterfly1x2.uvw_i.w00_i[0] + ntt_masked_butterfly1x2.uvw_i.w00_i[1]  < 'h7FE001 &&
    ntt_masked_butterfly1x2.uvw_i.u01_i[0] + ntt_masked_butterfly1x2.uvw_i.u01_i[1]  < 'h7FE001 &&
    ntt_masked_butterfly1x2.uvw_i.v01_i[0] + ntt_masked_butterfly1x2.uvw_i.v01_i[1]  < 'h7FE001 &&
    ntt_masked_butterfly1x2.uvw_i.w01_i[0] + ntt_masked_butterfly1x2.uvw_i.w01_i[1]  < 'h7FE001 
    ;
endproperty
assume_input_constraint: assume property(disable iff (!pi_reset_n) input_constraint);

//Constraint to limit the inputs value to Q (8380417)
property input_constraint_2;

    (ntt_masked_butterfly1x2.u10_packed[0] + ntt_masked_butterfly1x2.u10_packed[1])  < 'h7FE001;
endproperty
assume_input_constraint_2: assume property(disable iff (!pi_reset_n) input_constraint_2);

//Constraint to make mode selection signal input stable
property stable_mode;
    $stable(ntt_masked_butterfly1x2.mode);
endproperty
assume_stable_mode: assume property(disable iff (!pi_reset_n) stable_mode);

endmodule