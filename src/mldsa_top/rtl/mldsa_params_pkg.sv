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
// mldsa_params_pkg.sv
// --------
// Common params and defines for ML-DSA 87
//
//======================================================================

`ifndef MLDSA_PARAMS_PKG
`define MLDSA_PARAMS_PKG

package mldsa_params_pkg;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter MLDSA_Q = 23'd8380417;
  parameter MLDSA_Q_WIDTH = $clog2(MLDSA_Q) + 1;
  parameter REG_SIZE = 24; //FIXME
  parameter MLDSA_N = 256;
  parameter MLDSA_GAMMA2 = (MLDSA_Q-1)/32;
  parameter MLDSA_K = 8;
  parameter [10:0][7:0] PREHASH_OID = 88'h0302040365014886600906;
  
  parameter COEFF_PER_CLK = 4;

//Memory interface - FIXME calculate the width based on depth not the other way
  parameter MLDSA_MEM_MAX_DEPTH = 1664; //FIXME
  parameter MLDSA_MEM_DATA_WIDTH = COEFF_PER_CLK * MLDSA_Q_WIDTH;
  parameter MLDSA_MEM_ADDR_WIDTH = $clog2(MLDSA_MEM_MAX_DEPTH) + 3; //+ 3 bits for bank selection

  parameter MLDSA_MEM_INST0_DEPTH = 1664; //19.5 KB
  parameter MLDSA_MEM_INST0_ADDR_W = $clog2(MLDSA_MEM_INST0_DEPTH);
  parameter MLDSA_MEM_INST1_DEPTH = 576; //6.75 KB
  parameter MLDSA_MEM_INST1_ADDR_W = $clog2(MLDSA_MEM_INST1_DEPTH);
  parameter MLDSA_MEM_INST2_DEPTH = 1408; //16.5 KB
  parameter MLDSA_MEM_INST2_ADDR_W = $clog2(MLDSA_MEM_INST2_DEPTH);
  parameter MLDSA_MEM_INST3_DEPTH = 128; //1.5 KB
  parameter MLDSA_MEM_INST3_ADDR_W = $clog2(MLDSA_MEM_INST3_DEPTH);
  parameter MLDSA_MEM_W1_DEPTH = 512;

  parameter MLDSA_KEYGEN      = 3'b001;
  parameter MLDSA_SIGN        = 3'b010;
  parameter MLDSA_VERIFY      = 3'b011;
  parameter MLDSA_KEYGEN_SIGN = 3'b100;

  parameter [63  : 0] MLDSA_CORE_NAME        = 64'h30; //FIXME
  parameter [63  : 0] MLDSA_CORE_VERSION     = 64'h0;  //FIXME

  // Implementation parameters
  parameter DATA_WIDTH = 32;

  //Common structs
  typedef enum logic [1:0] {RW_IDLE = 2'b00, RW_READ = 2'b01, RW_WRITE = 2'b10} mem_rw_mode_e;

  typedef struct packed {
      mem_rw_mode_e rd_wr_en;
      logic [MLDSA_MEM_ADDR_WIDTH-1:0] addr;
  } mem_if_t;

endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================
