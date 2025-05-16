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
// decompose_r1_lut.sv
// --------
// Breaks down input coefficient r into highbits(r)
// Follows a look up table to determine the value of r1 based on input r
// In a corner case, when r is greater than 31γ2+1 and less than q-1, r1 is made 0
//======================================================================

module decompose_r1_lut
    import abr_params_pkg::*;
    #(
        parameter REG_SIZE = 23
    )
    (
        input wire [REG_SIZE-1:0] r,
        output logic [3:0] r1,
        output logic r_corner, //Indicates if coeff r is in the corner case range
        output logic z_nez
    );

    always_comb begin
        r_corner = 'b0;
        if      (r <=   MLDSA_GAMMA2)  r1 = 'd0;
        else if (r <= 3*MLDSA_GAMMA2)  r1 = 'd1;
        else if (r <= 5*MLDSA_GAMMA2)  r1 = 'd2;
        else if (r <= 7*MLDSA_GAMMA2)  r1 = 'd3;
        else if (r <= 9*MLDSA_GAMMA2)  r1 = 'd4;
        else if (r <= 11*MLDSA_GAMMA2) r1 = 'd5;
        else if (r <= 13*MLDSA_GAMMA2) r1 = 'd6;
        else if (r <= 15*MLDSA_GAMMA2) r1 = 'd7;
        else if (r <= 17*MLDSA_GAMMA2) r1 = 'd8;
        else if (r <= 19*MLDSA_GAMMA2) r1 = 'd9;
        else if (r <= 21*MLDSA_GAMMA2) r1 = 'd10;
        else if (r <= 23*MLDSA_GAMMA2) r1 = 'd11;
        else if (r <= 25*MLDSA_GAMMA2) r1 = 'd12;
        else if (r <= 27*MLDSA_GAMMA2) r1 = 'd13;
        else if (r <= 29*MLDSA_GAMMA2) r1 = 'd14;
        else if (r <= 31*MLDSA_GAMMA2) r1 = 'd15;
        else 
            begin                     
                r1 = 'd0;
                r_corner = 'b1;
            end
    end

    always_comb z_nez = (r1 != 'h0);

endmodule