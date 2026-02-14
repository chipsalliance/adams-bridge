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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_ntt_mlkem_masked_BFU_mult_constraints
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter WIDTH      = 24,
    parameter HALF_WIDTH = WIDTH/2
    //#$localparams
    //$#//
) (
    //#$ports
    input                        pi_clk,
    input                        pi_reset_n,
    input                        pi_zeroize,
    input [1:0][WIDTH-1:0]       pi_u,
    input [1:0][WIDTH-1:0]       pi_v,
    input [4:0][13:0]            pi_rnd,
    input [WIDTH-1:0]            pi_rnd_24bit,
    input logic [1:0][WIDTH-1:0] po_res
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

//Constraint to limit the input value to MLKEM_Q
property pi_constraint;
    pi_u[0] + pi_u[1]  < 32'(MLKEM_Q) &&
    pi_v[0] + pi_v[1] < 32'(MLKEM_Q)
    ;
endproperty
assume_pi_constraint: assume property(disable iff (!pi_reset_n | pi_zeroize) pi_constraint);

endmodule

