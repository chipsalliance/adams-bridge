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

module fv_ntt_butterfly2x2_constraints
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
 (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input mode_t                            pi_mode,
    input                                   pi_enable,
    input                                   pi_mlkem,
    input bf_uvwi_t                         pi_uvw_i,
    input pwo_uvwi_t                        pi_pw_uvw_i,
    input                                   pi_accumulate,
    input mlkem_pairwm_zeta_t               pi_mlkem_pairwm_zeta13_i,
    input bf_uvo_t                          po_uv_o,
    input pwo_t                             po_pwo_uv_o,
    input logic                             po_ready_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

// Intent: pi_accumulate must not change mid-operation, only between operations
property stable_acc;
    $stable(pi_accumulate);
endproperty
assume_stable_acc: assume property (
  disable iff (!pi_reset_n | pi_zeroize) stable_acc);

// Intent: pi_mode must not change mid-operation, only between operations
property stable_mode;
    $stable(pi_mode);
endproperty
assume_stable_mode: assume property (
  disable iff (!pi_reset_n | pi_zeroize) stable_mode);

// Intent: pi_mlkem must not change mid-operation, only between operations
property stable_mlkem;
    $stable(pi_mlkem);
endproperty
assume_stable_mlkem: assume property (
  disable iff (!pi_reset_n | pi_zeroize) stable_mlkem);

// Intent: pi_pw_uvw_i is driven to 0 the cycle after reset/zeroize deasserts,
// so downstream properties see a known value instead of X on the first cycle
property pw_uvw_i;
    $past(!pi_reset_n | pi_zeroize)
|->
    pi_pw_uvw_i == 0;
endproperty
assume_pw_uvw_i: assume property (pw_uvw_i);

// Intent: bound every uvw/pw_uvw operand to < MLKEM_Q (3329) whenever the DUT
// is in MLKEM mode, since the RTL's modular arithmetic assumes this range
property q_mlkem;
    pi_mlkem == 1'd1
|->
    pi_uvw_i.u00_i    < MLKEM_Q &&
    pi_uvw_i.u01_i    < MLKEM_Q &&
    pi_uvw_i.v00_i    < MLKEM_Q &&
    pi_uvw_i.v01_i    < MLKEM_Q &&
    pi_uvw_i.w00_i    < MLKEM_Q &&
    pi_uvw_i.w01_i    < MLKEM_Q &&
    pi_uvw_i.w10_i    < MLKEM_Q &&
    pi_uvw_i.w11_i    < MLKEM_Q &&
    pi_pw_uvw_i.u0_i  < MLKEM_Q &&
    pi_pw_uvw_i.v0_i  < MLKEM_Q &&
    pi_pw_uvw_i.w0_i  < MLKEM_Q &&
    pi_pw_uvw_i.u1_i  < MLKEM_Q &&
    pi_pw_uvw_i.v1_i  < MLKEM_Q &&
    pi_pw_uvw_i.w1_i  < MLKEM_Q &&
    pi_pw_uvw_i.u2_i  < MLKEM_Q &&
    pi_pw_uvw_i.v2_i  < MLKEM_Q &&
    pi_pw_uvw_i.w2_i  < MLKEM_Q &&
    pi_pw_uvw_i.u3_i  < MLKEM_Q &&
    pi_pw_uvw_i.v3_i  < MLKEM_Q &&
    pi_pw_uvw_i.w3_i  < MLKEM_Q
    ;
endproperty
assume_q_mlkem: assume property (q_mlkem);

// Intent: bound every uvw/pw_uvw operand to < MLDSA_Q ('h7FE001) whenever the
// DUT is in MLDSA mode, since the RTL's modular arithmetic assumes this range
property q_mldsa;
    pi_mlkem == 1'd0
|->
    pi_uvw_i.u00_i    < MLDSA_Q &&
    pi_uvw_i.u01_i    < MLDSA_Q &&
    pi_uvw_i.v00_i    < MLDSA_Q &&
    pi_uvw_i.v01_i    < MLDSA_Q &&
    pi_uvw_i.w00_i    < MLDSA_Q &&
    pi_uvw_i.w01_i    < MLDSA_Q &&
    pi_uvw_i.w10_i    < MLDSA_Q &&
    pi_uvw_i.w11_i    < MLDSA_Q &&
    pi_pw_uvw_i.u0_i  < MLDSA_Q &&
    pi_pw_uvw_i.v0_i  < MLDSA_Q &&
    pi_pw_uvw_i.w0_i  < MLDSA_Q &&
    pi_pw_uvw_i.u1_i  < MLDSA_Q &&
    pi_pw_uvw_i.v1_i  < MLDSA_Q &&
    pi_pw_uvw_i.w1_i  < MLDSA_Q &&
    pi_pw_uvw_i.u2_i  < MLDSA_Q &&
    pi_pw_uvw_i.v2_i  < MLDSA_Q &&
    pi_pw_uvw_i.w2_i  < MLDSA_Q &&
    pi_pw_uvw_i.u3_i  < MLDSA_Q &&
    pi_pw_uvw_i.v3_i  < MLDSA_Q &&
    pi_pw_uvw_i.w3_i  < MLDSA_Q
    ;
endproperty
assume_q_mldsa: assume property (q_mldsa);

// G4: Constrain MLKEM Karatsuba zeta inputs to < MLKEM_Q.
// The RTL feeds z0_i/z1_i directly into ntt_karatsuba_pairwm;
// values >= MLKEM_Q would produce results outside the MLKEM field.
property mlkem_zeta_range;
    pi_mlkem
|->
    pi_mlkem_pairwm_zeta13_i.z0_i < MLKEM_Q &&
    pi_mlkem_pairwm_zeta13_i.z1_i < MLKEM_Q;
endproperty
assume_mlkem_zeta_range: assume property (
  disable iff (!pi_reset_n | pi_zeroize) mlkem_zeta_range);

endmodule

