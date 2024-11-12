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

// coeff = eta - sk_data[eta_size-1:0]
// where eta_size = bitlen(2*eta), eta = 2 and sk_data is part of the incoming sk

// Input data must be in the range of -2 to 2 (mapped to 0 to 4 in positive range)
// Any value outside of this range is invalid and will trigger an error interrupt to FW and stops the process

module skdecode_s1s2_unpack
    #(
        parameter REG_SIZE = 24,
        parameter MLDSA_ETA = 2,
        parameter ETA_SIZE = 3, //$clog2(2*MLDSA_ETA),
        parameter MLDSA_Q = 8380417
    )
    (
        input wire [ETA_SIZE-1:0] data_i,
        input wire enable,
        output logic [REG_SIZE-1:0] data_o,
        output logic valid_o,
        output logic error_o
    );

    logic [REG_SIZE-1:0] eta_minus_data;

    always_comb begin
        data_o  = '0;
        valid_o = '0;
        error_o = '0;
        eta_minus_data = '0;
        
        if (enable) begin
            error_o = 'b0;
            eta_minus_data = REG_SIZE'(MLDSA_ETA - data_i);

            unique case(data_i)
                3'h0: data_o = 'h2;
                3'h1: data_o = 'h1;
                3'h2: data_o = 'h0; 
                3'h3: data_o = MLDSA_Q-1;
                3'h4: data_o = MLDSA_Q-2;
                default: begin
                    data_o   = 'h0;
                    error_o  = 'b1;
                end
            endcase

            valid_o = 'b1;
        end
    end

endmodule