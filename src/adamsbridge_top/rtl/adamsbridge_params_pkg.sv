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
  parameter DILITHIUM_Q = 23'd8380417;
  parameter DILITHIUM_Q_W = $clog2(DILITHIUM_Q) + 1;
  parameter REG_SIZE = 24; //FIXME
  parameter DILITHIUM_N = 256;
  
  parameter COEFF_PER_CLK = 4;

//Memory interface - FIXME calculate the width based on depth not the other way
  parameter ABR_MEM_MAX_DEPTH = 2496; //FIXME
  parameter ABR_MEM_DATA_WIDTH = COEFF_PER_CLK * DILITHIUM_Q_W;
  parameter ABR_MEM_ADDR_WIDTH = $clog2(ABR_MEM_MAX_DEPTH) + 3; //+ 3 bits for bank selection

  parameter ABR_MEM_INST0_DEPTH = 2496;
  parameter ABR_MEM_INST0_ADDR_W = $clog2(ABR_MEM_INST0_DEPTH);
  parameter ABR_MEM_INST1_DEPTH = 1088;
  parameter ABR_MEM_INST1_ADDR_W = $clog2(ABR_MEM_INST1_DEPTH);
  parameter ABR_MEM_INST2_DEPTH = 1408;
  parameter ABR_MEM_INST2_ADDR_W = $clog2(ABR_MEM_INST2_DEPTH);
  parameter ABR_MEM_INST3_DEPTH = 576;
  parameter ABR_MEM_INST3_ADDR_W = $clog2(ABR_MEM_INST3_DEPTH);

  parameter MEM_ADDR_WIDTH = 15; //FIXME REMOVE
  parameter MEM_DEPTH = 2**MEM_ADDR_WIDTH; //FIXME REMOVE
  parameter MEM_DATA_WIDTH = COEFF_PER_CLK*DILITHIUM_Q_W; //FIXME REMOVE

  parameter ABR_KEYGEN      = 3'b001;
  parameter ABR_SIGN        = 3'b010;
  parameter ABR_VERIFY      = 3'b011;
  parameter ABR_KEYGEN_SIGN = 3'b100;

  parameter [63  : 0] ABR_CORE_NAME        = 64'h30; //FIXME
  parameter [63  : 0] ABR_CORE_VERSION     = 64'h0;  //FIXME

  // Implementation parameters
  parameter DATA_WIDTH           = 32;

  //Common structs
  typedef enum logic [1:0] {RW_IDLE = 2'b00, RW_READ = 2'b01, RW_WRITE = 2'b10} mem_rw_mode_e;

  typedef struct packed {
      mem_rw_mode_e rd_wr_en;
      logic [ABR_MEM_ADDR_WIDTH-1:0] addr;
  } mem_if_t;

endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================