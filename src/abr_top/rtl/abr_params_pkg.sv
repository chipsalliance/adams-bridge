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
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter MLDSA_Q = 23'd8380417;
  parameter MLDSA_Q_WIDTH = $clog2(MLDSA_Q) + 1; //24
  parameter REG_SIZE = 24;
  parameter MLDSA_N = 256;
  parameter MLDSA_GAMMA2 = (MLDSA_Q-1)/32;
  parameter MLDSA_K = 8;
  parameter [10:0][7:0] PREHASH_OID = 88'h0302040365014886600906;

  parameter MLKEM_NTT_N = 128;
  parameter MLKEM_REG_SIZE = 12;
  
  parameter MLKEM_Q = 12'd3329;
  parameter MLKEM_Q_WIDTH = $clog2(MLKEM_Q); //12
  parameter MLKEM_N = 256;
  parameter MLKEM_K = 4;
  parameter MLKEM_ETA = 2;

  parameter COEFF_PER_CLK = 4;

  parameter MLDSA_NUM_SHARES = 2; //set this to 1 if masking disabled
  parameter MLDSA_SHARE_WIDTH = MLDSA_Q_WIDTH * MLDSA_NUM_SHARES;
  
  parameter MLKEM_NUM_SHARES = 2; //set this to 1 if masking disabled
  parameter MLKEM_SHARE_WIDTH = MLKEM_Q_WIDTH * MLKEM_NUM_SHARES;

  //Can be 1 or 2 only
  parameter ABR_NUM_NTT = 1;
  
  //Memory interface
  parameter ABR_MEM_DATA_WIDTH = COEFF_PER_CLK * MLDSA_Q_WIDTH; //96
  parameter ABR_MEM_MASKED_DATA_WIDTH = (COEFF_PER_CLK * MLDSA_NUM_SHARES) * (MLDSA_Q_WIDTH * MLDSA_NUM_SHARES); //384

  parameter ABR_MEM_MASKED_INST = 3;

  //parameter ABR_MEM_INST0_DEPTH = 1664; //19.5 KB
  //parameter ABR_MEM_INST0_ADDR_W = $clog2(ABR_MEM_INST0_DEPTH);
  parameter ABR_MEM_INST0_DEPTH = 1664/2; //9.75 KB
  parameter ABR_MEM_INST0_ADDR_W = $clog2(ABR_MEM_INST0_DEPTH);
  parameter ABR_MEM_INST0_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_INST1_DEPTH = 576; //6.75 KB
  parameter ABR_MEM_INST1_ADDR_W = $clog2(ABR_MEM_INST1_DEPTH);
  parameter ABR_MEM_INST1_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_INST2_DEPTH = 1472; //17.25 KB
  parameter ABR_MEM_INST2_ADDR_W = $clog2(ABR_MEM_INST2_DEPTH);
  parameter ABR_MEM_INST2_DATA_W = ABR_MEM_DATA_WIDTH;
  parameter ABR_MEM_INST3_DEPTH = 64; //3 KB
  parameter ABR_MEM_INST3_ADDR_W = $clog2(ABR_MEM_INST3_DEPTH);
  parameter ABR_MEM_INST3_DATA_W = ABR_MEM_MASKED_DATA_WIDTH;
  parameter ABR_MEM_W1_DEPTH = 512;
  parameter ABR_MEM_W1_ADDR_W = $clog2(ABR_MEM_W1_DEPTH);
  parameter ABR_MEM_W1_DATA_W = 4;
  
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

  parameter [63  : 0] MLDSA_CORE_NAME        = 64'h3837412D_44534D4C; // "MLDSA-87"
  parameter [63  : 0] MLDSA_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"
  parameter [63  : 0] MLKEM_CORE_NAME        = 64'h32343130_4D2D4B45; // "KEM-1024"
  parameter [63  : 0] MLKEM_CORE_VERSION     = 64'h00000000_3030312e; // "1.00"

  // Implementation parameters
  parameter DATA_WIDTH = 32;

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
