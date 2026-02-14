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


module fv_ntt_mlkem_masked_butterfly1x2_constraints
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter MLKEM_SHARE_WIDTH = 24,
    parameter MLKEM_Q_WIDTH     = MLKEM_SHARE_WIDTH/2
    //#$localparams
    //$#//
) (
    //#$ports
    input                        pi_clk,
    input                        pi_reset_n,
    input                        pi_zeroize,
    input mlkem_masked_bf_uvwi_t pi_uvw_i,
    input [4:0][13:0]            pi_rnd_i,
    input bf_uvo_t               po_uv_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

//Constraint to limit the inputs value to MLKEM_Q
property input_constraint;

    pi_uvw_i.u00_i[0] + pi_uvw_i.u00_i[1]  < MLKEM_Q &&
    pi_uvw_i.v00_i[0] + pi_uvw_i.v00_i[1]  < MLKEM_Q &&
    pi_uvw_i.w00_i[0] + pi_uvw_i.w00_i[1]  < MLKEM_Q &&
    pi_uvw_i.u01_i[0] + pi_uvw_i.u01_i[1]  < MLKEM_Q &&
    pi_uvw_i.v01_i[0] + pi_uvw_i.v01_i[1]  < MLKEM_Q &&
    pi_uvw_i.w01_i[0] + pi_uvw_i.w01_i[1]  < MLKEM_Q 
    ;
endproperty
assume_input_constraint: assume property(disable iff (!pi_reset_n | pi_zeroize) input_constraint);

endmodule

