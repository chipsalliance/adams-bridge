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
// sampler_pkg.sv
// --------
// required parameters for sampler top
//
//======================================================================

`ifndef ABR_SAMPLER_PKG
`define ABR_SAMPLER_PKG

package sampler_pkg;
  import abr_params_pkg::*;

  parameter ABR_COEFF_CNT = 256;

//SHA3 Configuration
// Keccak Rounds per clock
  parameter RoundsPerClock = 2;
// Do not enable masking //TODO
  parameter Sha3EnMasking = 0;
  parameter Sha3Share = (Sha3EnMasking) ? 2 : 1;

//Sampler Configurations
//Rej Sampler
  parameter REJS_NUM_SAMPLERS     = 5;
  parameter REJS_SAMPLE_W         = 24;
  parameter REJS_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter REJS_PISO_BUFFER_W    = 1440;
  parameter REJS_PISO_INPUT_RATE  = 1344;
  parameter REJS_PISO_OUTPUT_RATE = 120;

//Rej Bounded
  parameter REJB_NUM_SAMPLERS     = 8;
  parameter REJB_SAMPLE_W         = 4;
  parameter REJB_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter REJB_VLD_SAMPLES_W    = 24;
  parameter REJB_VALUE            = 15;
  parameter REJB_VLD_SAMPLE_W     = $clog2(REJB_VALUE);
  parameter REJB_PISO_BUFFER_W    = 1334;
  parameter REJB_PISO_INPUT_RATE  = 1088;
  parameter REJB_PISO_OUTPUT_RATE = 32;

//Exp Mask
  parameter EXP_NUM_SAMPLERS     = 4;
  parameter EXP_SAMPLE_W         = 20;
  parameter EXP_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter EXP_VLD_SAMPLE_W     = 24;
  parameter EXP_PISO_BUFFER_W    = 1152;
  parameter EXP_PISO_INPUT_RATE  = 1088;
  parameter EXP_PISO_OUTPUT_RATE = 80;

//Sample In Ball
  parameter SIB_NUM_SAMPLERS     = 4;
  parameter SIB_SAMPLE_W         = 8;
  parameter SIB_TAU              = 60;
  parameter SIB_PISO_BUFFER_W    = 1344;
  parameter SIB_PISO_INPUT_RATE  = 1088;
  parameter SIB_PISO_OUTPUT_RATE = 32;

  //common structures
  typedef enum logic [3:0] {
    ABR_SAMPLER_NONE,
    //SHA/SHAKE only modes
    ABR_SHAKE256,
    ABR_SHAKE128,
    //SAMPLER MODES
    ABR_REJ_SAMPLER,
    ABR_EXP_MASK,
    ABR_REJ_BOUNDED,
    ABR_SAMPLE_IN_BALL
  } abr_sampler_mode_e;

endpackage

`endif
