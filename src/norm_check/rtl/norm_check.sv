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
//======================================================================
//
// norm_check.sv
// --------
// Performs: invalid = (coeff > bound) && (coeff < q-bound)

module norm_check
    import norm_check_defines_pkg::*;
    import abr_params_pkg::*;
    #(
        parameter MLDSA_Q = 8380417
    )
    (
        input wire enable,
        //The bound is selected by the controller from the active parameter set,
        //so the same comparator serves every ML-DSA parameter set.
        input wire [REG_SIZE-2:0] bound_i,
        input wire [REG_SIZE-2:0] opa_i,
        output logic invalid
    );

    logic [REG_SIZE-2:0] q_minus_bound;

    always_comb q_minus_bound = MLDSA_Q - bound_i;

    always_comb invalid = enable & (opa_i >= bound_i) & (opa_i <= q_minus_bound);
endmodule