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
// barrett_reduction.sv
// -----------

module barrett_reduction #(
    parameter int prime = 3329,
    parameter int REG_SIZE = $clog2(prime)
)(
    input  logic [2*REG_SIZE-1:0]   x,
    output logic [REG_SIZE-1:0]     inv, // x / prime
    output logic [REG_SIZE-1:0]     r    // x % prime
);

    // K is derived from REG_SIZE
    localparam int K = 2*REG_SIZE;

    // Compute M = floor(2^K / Q)
    localparam logic [REG_SIZE:0] m = (1 << K) / prime;

    logic [3*REG_SIZE:0]   mult_full;
    logic [REG_SIZE:0]     u_est, u_plus_one;
    logic [2*REG_SIZE:0]   u_prime, r_est, r_sub_prime;
    logic additional_reduction;

    assign mult_full = x * m;

    assign u_est = mult_full >> K;
    assign u_prime = u_est * prime;
    assign r_est = {1'b0, x} - u_prime;

    // conditional outputs
    assign r_sub_prime = r_est - prime;
    assign u_plus_one = u_est + 1;

    //condition for the output
    assign additional_reduction = (r_est >= prime);

    // Compute output
    assign r   = additional_reduction? r_sub_prime[REG_SIZE-1 : 0] : r_est[REG_SIZE-1 : 0];
    assign inv = additional_reduction? u_plus_one[REG_SIZE-1 : 0] : u_est[REG_SIZE-1 : 0];

endmodule
