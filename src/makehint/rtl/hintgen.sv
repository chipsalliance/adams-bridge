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
// hintgen.sv
// --------
// Processes (r, z) inputs and produces a 4-bit hint vector per coefficient
// of a given polynomial.
//======================================================================

module hintgen
    import abr_params_pkg::*;
    #(
        parameter REG_SIZE = 23,
        parameter MLDSA_Q = 23'd8380417,
        // parameter GAMMA2 = (MLDSA_Q-1)/32,
        parameter Q_MINUS_GAMMA2 = MLDSA_Q - MLDSA_GAMMA2
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire enable,
        input wire [REG_SIZE-1:0] r,
        input wire z_neq_z,
        output logic h

    );

    logic r_lt_gamma2;
    logic r_gt_q_minus_gamma2;
    logic r_eq_q_minus_gamma2;
    logic or1_res, or2_res, and_res, not_res;

    //TODO: need flop here? commenting out for now
    // always_ff @(posedge clk or negedge reset_n) begin
    //     if (!reset_n)
    //         h <= 'b0;
    //     else if (zeroize)
    //         h <= 'b0;
    //     else if (enable)
    //         h <= or2_res;
    //     else
    //         h <= 'b0;
    // end

    assign h = (enable & ~zeroize) ? or2_res : 'b0;

    always_comb begin
        r_lt_gamma2         = (r <= MLDSA_GAMMA2)   ? 1'b1 : 1'b0;
        r_gt_q_minus_gamma2 = (r >= Q_MINUS_GAMMA2) ? 1'b1 : 1'b0;
        r_eq_q_minus_gamma2 = (r == Q_MINUS_GAMMA2) ? 1'b1 : 1'b0;
    end

    always_comb begin
        or1_res = r_lt_gamma2 | r_gt_q_minus_gamma2;
        and_res = r_eq_q_minus_gamma2 & z_neq_z;
        not_res = ~or1_res;
        or2_res = not_res | and_res;
    end
endmodule