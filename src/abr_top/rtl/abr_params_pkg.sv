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
//
//======================================================================
//
// abr_params_pkg.sv
// --------
// Common params and defines for ML-DSA 87
//
//======================================================================

`ifndef ABR_PARAMS_PKG
`define ABR_PARAMS_PKG

package abr_params_pkg;

  //----------------------------------------------------------------
  // Parameter sets
  //
  // The core implements every ML-DSA and ML-KEM parameter set. The
  // active set is selected at runtime via the PARAM_SET register field.
  //----------------------------------------------------------------
  //Runtime parameter set encodings. RSVD must be rejected by abr_ctrl.
  typedef enum logic [1:0] {
    MLDSA_PARAM_44   = 2'b00,
    MLDSA_PARAM_65   = 2'b01,
    MLDSA_PARAM_87   = 2'b10,
    MLDSA_PARAM_RSVD = 2'b11
  } mldsa_param_set_e;

  typedef enum logic [1:0] {
    MLKEM_PARAM_512  = 2'b00,
    MLKEM_PARAM_768  = 2'b01,
    MLKEM_PARAM_1024 = 2'b10,
    MLKEM_PARAM_RSVD = 2'b11
  } mlkem_param_set_e;

  //Decode of the ABR_CTRL.PARAM_SET register field. The register encoding is
  //deliberately NOT the internal enum encoding: register 2'b00 must select the
  //category 5 set so that software unaware of the field, and the reset value,
  //both keep the pre-existing behaviour.
  function automatic mldsa_param_set_e mldsa_param_set_decode(input logic [1:0] reg_val);
    case (reg_val)
      2'b00  : mldsa_param_set_decode = MLDSA_PARAM_87;   //reset default
      2'b01  : mldsa_param_set_decode = MLDSA_PARAM_44;
      2'b10  : mldsa_param_set_decode = MLDSA_PARAM_65;
      default: mldsa_param_set_decode = MLDSA_PARAM_RSVD;
    endcase
  endfunction

  function automatic mlkem_param_set_e mlkem_param_set_decode(input logic [1:0] reg_val);
    case (reg_val)
      2'b00  : mlkem_param_set_decode = MLKEM_PARAM_1024; //reset default
      2'b01  : mlkem_param_set_decode = MLKEM_PARAM_512;
      2'b10  : mlkem_param_set_decode = MLKEM_PARAM_768;
      default: mlkem_param_set_decode = MLKEM_PARAM_RSVD;
    endcase
  endfunction

  //Every defined parameter set is implemented; only the reserved encoding is
  //rejected.
  function automatic bit mldsa_param_set_supported(input mldsa_param_set_e s);
    mldsa_param_set_supported = (s != MLDSA_PARAM_RSVD);
  endfunction

  function automatic bit mlkem_param_set_supported(input mlkem_param_set_e s);
    mlkem_param_set_supported = (s != MLKEM_PARAM_RSVD);
  endfunction

  //gamma2 = (q-1)/GAMMA2_DIV. FIPS 204 Table 1: 32 for ML-DSA-65/87, 88 for ML-DSA-44.
  parameter int MLDSA_GAMMA2_DIV_32 = 32;
  parameter int MLDSA_GAMMA2_DIV_88 = 88;

  //Per-set dimensions (FIPS 204 Table 1 / FIPS 203 Table 2)
  function automatic int mldsa_k_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44: mldsa_k_of = 4;
      MLDSA_PARAM_65: mldsa_k_of = 6;
      default       : mldsa_k_of = 8;
    endcase
  endfunction

  function automatic int mldsa_l_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44: mldsa_l_of = 4;
      MLDSA_PARAM_65: mldsa_l_of = 5;
      default       : mldsa_l_of = 7;
    endcase
  endfunction

  function automatic int mldsa_eta_of(mldsa_param_set_e s);
    //ML-DSA-65 is the only set with eta = 4
    mldsa_eta_of = (s == MLDSA_PARAM_65) ? 4 : 2;
  endfunction

  function automatic int mldsa_tau_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44: mldsa_tau_of = 39;
      MLDSA_PARAM_65: mldsa_tau_of = 49;
      default       : mldsa_tau_of = 60;
    endcase
  endfunction

  function automatic int mldsa_omega_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44: mldsa_omega_of = 80;
      MLDSA_PARAM_65: mldsa_omega_of = 55;
      default       : mldsa_omega_of = 75;
    endcase
  endfunction

  //lambda in bits; c~ occupies 2*lambda bits = lambda/4 bytes
  function automatic int mldsa_lambda_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44: mldsa_lambda_of = 128;
      MLDSA_PARAM_65: mldsa_lambda_of = 192;
      default       : mldsa_lambda_of = 256;
    endcase
  endfunction

  //c~ is 2*lambda bits = lambda/4 bytes: 32 / 48 / 64 for -44 / -65 / -87.
  //Category 5 returns 64, which is the width the c~ register is instantiated at,
  //so every expression derived from this collapses to the previous constant there.
  function automatic int mldsa_ctilde_bytes_of(mldsa_param_set_e s);
    mldsa_ctilde_bytes_of = mldsa_lambda_of(s) / 4;
  endfunction

  function automatic int mldsa_ctilde_dwords_of(mldsa_param_set_e s);
    mldsa_ctilde_dwords_of = mldsa_ctilde_bytes_of(s) / 4;
  endfunction

  //log2(gamma1): 17 for ML-DSA-44, 19 otherwise
  function automatic int mldsa_gamma1_w_of(mldsa_param_set_e s);
    mldsa_gamma1_w_of = (s == MLDSA_PARAM_44) ? 17 : 19;
  endfunction

  //z is packed at 1+log2(gamma1) bits per coefficient, 256 coefficients per
  //polynomial, l polynomials: 8*l*(1+gamma1_w) dwords = 576 / 800 / 1120
  function automatic int mldsa_sig_z_dwords_of(mldsa_param_set_e s);
    mldsa_sig_z_dwords_of = 8 * mldsa_l_of(s) * (1 + mldsa_gamma1_w_of(s));
  endfunction

  //gamma2 divisor: (q-1)/88 for ML-DSA-44, (q-1)/32 otherwise
  function automatic int mldsa_gamma2_div_of(mldsa_param_set_e s);
    mldsa_gamma2_div_of = (s == MLDSA_PARAM_44) ? MLDSA_GAMMA2_DIV_88
                                                : MLDSA_GAMMA2_DIV_32;
  endfunction

  //beta = tau * eta (FIPS 204 Table 1)
  function automatic int mldsa_beta_of(mldsa_param_set_e s);
    case (s)
      MLDSA_PARAM_44 : mldsa_beta_of = 78;
      MLDSA_PARAM_65 : mldsa_beta_of = 196;
      default        : mldsa_beta_of = 120;
    endcase
  endfunction

  function automatic int mlkem_k_of(mlkem_param_set_e s);
    case (s)
      MLKEM_PARAM_512 : mlkem_k_of = 2;
      MLKEM_PARAM_768 : mlkem_k_of = 3;
      default         : mlkem_k_of = 4;
    endcase
  endfunction

  //eta1: 3 for ML-KEM-512, 2 otherwise. eta2 is always 2.
  function automatic int mlkem_eta1_of(mlkem_param_set_e s);
    mlkem_eta1_of = (s == MLKEM_PARAM_512) ? 3 : 2;
  endfunction

  function automatic int mlkem_du_of(mlkem_param_set_e s);
    mlkem_du_of = (s == MLKEM_PARAM_1024) ? 11 : 10;
  endfunction

  function automatic int mlkem_dv_of(mlkem_param_set_e s);
    mlkem_dv_of = (s == MLKEM_PARAM_1024) ? 5 : 4;
  endfunction

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter MLDSA_Q = 23'd8380417;
  parameter MLDSA_Q_WIDTH = $clog2(MLDSA_Q) + 1; //24
  parameter REG_SIZE = 24;
  parameter MLDSA_N = 256;
  parameter MLDSA_GAMMA2 = (MLDSA_Q-1)/MLDSA_GAMMA2_DIV_32;
  //gamma2 takes two values across the parameter sets.
  parameter MLDSA_GAMMA2_32 = (MLDSA_Q-1)/MLDSA_GAMMA2_DIV_32;
  parameter MLDSA_GAMMA2_88 = (MLDSA_Q-1)/MLDSA_GAMMA2_DIV_88;

  function automatic int mldsa_gamma1_of(mldsa_param_set_e s);
    mldsa_gamma1_of = 1 << mldsa_gamma1_w_of(s);
  endfunction

  function automatic int mldsa_gamma2_of(mldsa_param_set_e s);
    mldsa_gamma2_of = (MLDSA_Q-1)/mldsa_gamma2_div_of(s);
  endfunction

  //Number of HighBits buckets m = (q-1)/(2*gamma2) = GAMMA2_DIV/2. A w1
  //coefficient lies in [0, m-1] and UseHint is modulo m (FIPS 204 Alg. 40).
  parameter int MLDSA_W1_MOD_32 = MLDSA_GAMMA2_DIV_32/2; //16
  parameter int MLDSA_W1_MOD_88 = MLDSA_GAMMA2_DIV_88/2; //44
  //Storage is sized for the largest parameter set; a lower set is a strict
  //prefix of it and costs no extra memory.
  parameter MLDSA_K = 8;
  //Named _MAX to avoid colliding with the module-local MLDSA_L parameters in
  //sig{en,de}code_z_defines_pkg, which are wildcard-imported alongside this pkg.
  parameter MLDSA_L_MAX = 7;
  parameter MLDSA_D = 13;
  parameter MLDSA_ETA = 2;
  parameter MLDSA_ETA_W = 3;
  //Widest eta over the parameter sets: bitlen(2*eta) = 3 for eta=2, 4 for eta=4
  parameter MLDSA_ETA_MAX = 4;
  parameter MLDSA_ETA_W_MAX = 4;
  parameter [10:0][7:0] PREHASH_OID = 88'h0302040365014886600906;

  parameter MLKEM_NTT_N = 128;
  parameter MLKEM_REG_SIZE = 12;
  
  parameter MLKEM_Q = 12'd3329;
  parameter MLKEM_Q_WIDTH = $clog2(MLKEM_Q); //12
  parameter MLKEM_N = 256;
  parameter MLKEM_K = 4;
  parameter MLKEM_ETA = 2;
  //eta1 = 3 only for ML-KEM-512; eta2 is always 2
  parameter MLKEM_ETA1_MAX = 3;

  parameter COEFF_PER_CLK = 4;

  parameter MLDSA_NUM_SHARES = 2; //set this to 1 if masking disabled
  parameter MLDSA_SHARE_WIDTH = MLDSA_Q_WIDTH * MLDSA_NUM_SHARES;
  
  parameter MLKEM_NUM_SHARES = 2; //set this to 1 if masking disabled
  parameter MLKEM_SHARE_WIDTH = MLKEM_Q_WIDTH * MLKEM_NUM_SHARES;

  //Memory interface
  parameter ABR_MEM_DATA_WIDTH = COEFF_PER_CLK * MLDSA_Q_WIDTH; //96

  parameter ABR_MEM_INST0_DEPTH = 1600/2; //9.375 KB
  parameter ABR_MEM_INST0_ADDR_W = $clog2(ABR_MEM_INST0_DEPTH);
  parameter ABR_MEM_INST0_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_INST1_DEPTH = 64; //0.75 KB
  parameter ABR_MEM_INST1_ADDR_W = $clog2(ABR_MEM_INST1_DEPTH);
  parameter ABR_MEM_INST1_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_INST2_DEPTH = 1536; //18 KB
  parameter ABR_MEM_INST2_ADDR_W = $clog2(ABR_MEM_INST2_DEPTH);
  parameter ABR_MEM_INST2_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_W1_DEPTH = 512;
  parameter ABR_MEM_W1_ADDR_W = $clog2(ABR_MEM_W1_DEPTH);
  // w1 memory holds the MakeHint boolean (z != z') for 4 coefficients per word,
  // one bit each. It is independent of gamma2 and is 4 for every set.
  parameter ABR_MEM_W1_DATA_W = 4;
  // Bit width of a single encoded w1 coefficient: 4 bits for m = 16
  // (ML-DSA-65/87) and 6 bits for m = 44 (ML-DSA-44).
  parameter MLDSA_W1_COEFF_W   = 6;
  // omega is NOT monotonic in the security level (44:80, 65:55, 87:75), so the
  // hint-array widths are sized to the max over the parameter sets.
  parameter int MLDSA_OMEGA_MAX = 80;

  //Size of the encoded h field of the signature, (omega + k) bytes. This is not
  //MLDSA_OMEGA_MAX + MLDSA_K: the largest omega (80, ML-DSA-44) and the largest
  //k (8, ML-DSA-87) never occur together. Per set: 44 -> 84, 65 -> 61, 87 -> 83.
  parameter int MLDSA_SIG_H_BYTES_MAX = 84;
  
  parameter ABR_MEM_MAX_DEPTH = ABR_MEM_INST2_DEPTH;
  parameter ABR_MEM_ADDR_WIDTH = $clog2(ABR_MEM_MAX_DEPTH) + 3; //+ 3 bits for bank selection
  
  typedef enum logic [2:0] {
    MLDSA_NONE        = 3'b000,
    MLDSA_KEYGEN      = 3'b001,
    MLDSA_SIGN        = 3'b010,
    MLDSA_VERIFY      = 3'b011,
    MLDSA_KEYGEN_SIGN = 3'b100
  } mldsa_cmd_e;
  
  typedef enum logic [2:0] {
    MLKEM_NONE        = 3'b000,
    MLKEM_KEYGEN      = 3'b001,
    MLKEM_ENCAPS      = 3'b010,
    MLKEM_DECAPS      = 3'b011,
    MLKEM_KEYGEN_DEC  = 3'b100
  } mlkem_cmd_e;

  //NAME identifies the algorithm, not a parameter set: the core implements every
  //parameter set, so the string does not change with PARAM_SET. Names are space
  //padded to eight bytes.
  parameter [63  : 0] MLDSA_CORE_NAME        = 64'h20205341_2D444D4C; // "ML-DSA  "
  parameter [63  : 0] MLDSA_CORE_VERSION     = 64'h00000000_3000342E; // "4.0"
  parameter [63  : 0] MLKEM_CORE_NAME        = 64'h2020454D_2D4B4D4C; // "ML-KEM  "
  parameter [63  : 0] MLKEM_CORE_VERSION     = 64'h00000000_3000342E; // "4.0"

  // Implementation parameters
  parameter ABR_REG_WIDTH = 32;

  //Common structs
  typedef enum logic [1:0] {RW_IDLE = 2'b00, RW_READ = 2'b01, RW_WRITE = 2'b10} mem_rw_mode_e;

  typedef struct packed {
      mem_rw_mode_e rd_wr_en;
      logic [ABR_MEM_ADDR_WIDTH-1:0] addr;
  } mem_if_t;

endpackage

`endif
//======================================================================
// EOF abr_params_pkg.sv
//======================================================================
