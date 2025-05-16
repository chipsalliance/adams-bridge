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
        parameter MLDSA_Q = 8380417,
        parameter GAMMA1 = 2**19,
        // parameter MLDSA_GAMMA2 = (MLDSA_Q-1)/32,
        parameter BETA = 120,
        parameter GAMMA1_MINUS_BETA = GAMMA1 - BETA,
        parameter GAMMA2_MINUS_BETA = MLDSA_GAMMA2 - BETA
    )
    (
        input wire enable,
        input chk_norm_mode_t mode,
        input wire [REG_SIZE-2:0] opa_i,
        output logic invalid
    );

    logic [REG_SIZE-2:0] bound;
    logic [REG_SIZE-2:0] q_minus_bound;

    always_comb begin
        case(mode)
            z_bound:    bound = GAMMA1_MINUS_BETA;
            r0_bound:   bound = GAMMA2_MINUS_BETA;
            ct0_bound:  bound = MLDSA_GAMMA2;
            default:    bound = 'h0;
        endcase

        q_minus_bound = MLDSA_Q - bound;
    end

    always_comb invalid = enable & (opa_i >= bound) & (opa_i <= q_minus_bound);
endmodule