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


module fv_ntt_karatsuba_pairwm_constraints
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    //#$localparams
    //$#//
) (
    //#$ports
    input                      pi_clk,
    input                      pi_reset_n,
    input                      pi_zeroize,
    input                      pi_accumulate,
    input mlkem_pwo_uvwzi_t    pi_pwo_uvw_i,
    input [MLKEM_REG_SIZE-1:0] pi_pwo_z_i,
    input mlkem_pwo_t          po_pwo_uv_o
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    //Constraint to make accumulate signal input stable
    assume_stable_accumulate: assume property (disable iff(!pi_reset_n | pi_zeroize)
        $stable(pi_accumulate)
    );

    //Constraint the u0 and u1 inputs to be less than Q
    assume_u_range: assume property (disable iff(!pi_reset_n | pi_zeroize)
        pi_pwo_uvw_i.u0_i < MLKEM_Q &&
        pi_pwo_uvw_i.u1_i < MLKEM_Q
    );

    //Constraint the v0 and v1 inputs to be less than Q
    assume_v_range: assume property (disable iff(!pi_reset_n | pi_zeroize)
        pi_pwo_uvw_i.v0_i < MLKEM_Q &&
        pi_pwo_uvw_i.v1_i < MLKEM_Q
    );

    //Constraint the w0 and w1 accumulate inputs to be less than Q
    assume_w_range: assume property (disable iff(!pi_reset_n | pi_zeroize)
        pi_pwo_uvw_i.w0_i < MLKEM_Q &&
        pi_pwo_uvw_i.w1_i < MLKEM_Q
    );

     //Constraint the zeta input to be less than Q
    assume_zeta_range: assume property (disable iff(!pi_reset_n | pi_zeroize)
        pi_pwo_z_i < MLKEM_Q
    );
    
endmodule

