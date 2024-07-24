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
// required parameters and register address for ECC Secp384r1.
//
//======================================================================

`ifndef ABR_PARAMS_PKG
`define ABR_PARAMS_PKG

package abr_params_pkg;

  //----------------------------------------------------------------
  // Internal constant and parameter definitions.
  //----------------------------------------------------------------
  parameter DILITHIUM_Q = 8380417;
  parameter DILITHIUM_Q_W = $clog2(DILITHIUM_Q) + 1;
  parameter DILITHIUM_N = 256;
  
  parameter COEFF_PER_CLK = 4;

//Memory interface - FIXME calculate the width based on depth not the other way
  parameter ABR_MEM_INST_DEPTH = 2432; //FIXME
  parameter ABR_MEM_DATA_WIDTH = COEFF_PER_CLK * DILITHIUM_Q_W;
  parameter ABR_MEM_ADDR_WIDTH = $clog2(ABR_MEM_INST_DEPTH) + 1; //FIXME added a bit for bank selecting

  parameter MEM_ADDR_WIDTH = 15;
  parameter MEM_DEPTH = 2**MEM_ADDR_WIDTH;
  parameter MEM_DATA_WIDTH = COEFF_PER_CLK*DILITHIUM_Q_W;

  parameter ABR_KEYGEN = 2'b01;
  parameter ABR_SIGN   = 2'b10;
  parameter ABR_VERIFY = 2'b11;

  parameter [63  : 0] ABR_CORE_NAME        = 64'h30; //FIXME
  parameter [63  : 0] ABR_CORE_VERSION     = 64'h0;  //FIXME

  // Implementation parameters
  parameter DATA_WIDTH           = 32;

endpackage

`endif
//======================================================================
// EOF ecc_params.sv
//======================================================================
