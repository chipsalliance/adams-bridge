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
// skdecode_s1s2_unpack.sv
// --------
// This mux unpacks s1 and s2 polynomials from sk input. 3-bit input values
// are converted into 24-bit output values which are the final coefficients of
// s1 and s2 poly to be stored in memory

// coeff = eta - sk_data[MLDSA_ETA_W-1:0]
// where MLDSA_ETA_W = bitlen(2*eta), eta = 2 and sk_data is part of the incoming sk

// Input data must be in the range of -2 to 2 (mapped to 0 to 4 in positive range)
// Any value outside of this range is invalid and will trigger an error interrupt to FW and stops the process

module skdecode_s1s2_unpack
    import abr_params_pkg::*;
    (
        //Packed field is 3 bits at eta = 2 and 4 bits at eta = 4. The field is
        //always presented right justified in 4 bits. Public parameter, never secret.
        input logic [3:0] data_i,
        input logic eta4_i,
        input logic enable,
        output logic [REG_SIZE-1:0] data_o,
        output logic valid_o,
        output logic error_o
    );

    logic [REG_SIZE-1:0] eta_minus_data;
    logic [3:0] eta, two_eta;

    always_comb begin
        eta     = eta4_i ? 4'd4 : 4'd2;
        two_eta = eta4_i ? 4'd8 : 4'd4;
    end

    always_comb begin
        data_o  = '0;
        valid_o = '0;
        error_o = '0;
        eta_minus_data = '0;
        
        if (enable) begin
            //FIPS 204 5.6: the packed value v encodes the coefficient eta - v,
            //so v in [0, eta] maps to [eta, 0] and v in (eta, 2*eta] maps to the
            //negative range q - (v - eta). Anything above 2*eta is invalid.
            //At eta = 2 this reproduces the original literal table exactly.
            eta_minus_data = REG_SIZE'(eta - data_i);

            if (data_i <= eta) begin
                data_o  = eta_minus_data;
                error_o = 1'b0;
            end
            else if (data_i <= two_eta) begin
                data_o  = REG_SIZE'(MLDSA_Q - (data_i - eta));
                error_o = 1'b0;
            end
            else begin
                data_o  = '0;
                error_o = 1'b1;
            end

            valid_o = 1;
        end
    end

endmodule