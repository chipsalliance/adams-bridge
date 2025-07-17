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
// ntt_wrapper_pkg.sv
//======================================================================

`ifndef MLDSA_NTT_WRAPPER
`define MLDSA_NTT_WRAPPER

package ntt_wrapper_pkg;

  import abr_params_pkg::*;
  import ntt_defines_pkg::*;

  // NTT wrapper parameters
  parameter AHB_ADDR_WIDTH = 12;
  parameter AHB_DATA_WIDTH = 64;
  parameter MEM_DEPTH = 2**AHB_ADDR_WIDTH; // 4096


  parameter STATUS_REG = MEM_DEPTH - 1; // 4095
  parameter ENABLE_REG = MEM_DEPTH - 2; // 4094
  parameter CTRL_REG = MEM_DEPTH - 3; // 4093
  parameter BASE_ADDR_REG = MEM_DEPTH - 4; // 4092
  parameter SAMPLER_INPUT_0_REG = MEM_DEPTH - 5; // 4091
  parameter SAMPLER_INPUT_1_REG = MEM_DEPTH - 6; // 4090
  parameter SAMPLER_INPUT_2_REG = MEM_DEPTH - 7; // 4089
  parameter SAMPLER_INPUT_3_REG = MEM_DEPTH - 8; // 4088
  parameter LFSR_EN_REG = MEM_DEPTH - 9; // 4085
  parameter LFSR_SEED0_0_REG = MEM_DEPTH - 10; // 4084
  parameter LFSR_SEED0_1_REG = MEM_DEPTH - 11; // 4083
  parameter LFSR_SEED1_0_REG = MEM_DEPTH - 12; // 4082
  parameter LFSR_SEED1_1_REG = MEM_DEPTH - 13; // 4081
endpackage
    
`endif
