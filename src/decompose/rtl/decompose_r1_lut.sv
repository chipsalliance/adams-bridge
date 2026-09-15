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
        //Selects gamma2 = (q-1)/88 (ML-DSA-44). Public control, never secret.
        input wire gamma2_88_i,
        output logic [MLDSA_W1_COEFF_W-1:0] r1,
        output logic r_corner, //Indicates if coeff r is in the corner case range
        output logic z_nez
    );

    //The bucket chain is r1 = i for the lowest i with r <= (2i+1)*gamma2, and the
    //corner case otherwise. Descending iteration gives the same priority as the
    //original if/else-if chain: the lowest matching i assigns last and wins.
    logic [MLDSA_W1_COEFF_W-1:0] r1_m32;
    logic                        r_corner_m32;

    always_comb begin
        r1_m32       = '0;
        r_corner_m32 = 1'b1;
        for (int i = MLDSA_M_32-1; i >= 0; i--) begin
            if (r <= ((2*i)+1)*MLDSA_GAMMA2_32) begin
                r1_m32       = MLDSA_W1_COEFF_W'(i);
                r_corner_m32 = 1'b0;
            end
        end
    end

    generate
        if (ABR_NEED_GAMMA2_88) begin : gen_m88
            //44-bucket chain, only elaborated when ML-DSA-44 is enabled.
            logic [MLDSA_W1_COEFF_W-1:0] r1_m88;
            logic                        r_corner_m88;

            always_comb begin
                r1_m88       = '0;
                r_corner_m88 = 1'b1;
                for (int i = MLDSA_M_88-1; i >= 0; i--) begin
                    if (r <= ((2*i)+1)*MLDSA_GAMMA2_88) begin
                        r1_m88       = MLDSA_W1_COEFF_W'(i);
                        r_corner_m88 = 1'b0;
                    end
                end
            end

            always_comb begin
                r1       = gamma2_88_i ? r1_m88       : r1_m32;
                r_corner = gamma2_88_i ? r_corner_m88 : r_corner_m32;
            end
        end
        else begin : gen_m32_only
            always_comb begin
                r1       = r1_m32;
                r_corner = r_corner_m32;
            end
        end
    endgenerate

    always_comb z_nez = (r1 != 'h0);

endmodule