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
// abr_sampler_pkg.sv
// --------
// required parameters for sampler top
//
//======================================================================

`ifndef ABR_SAMPLER_PKG
`define ABR_SAMPLER_PKG

package abr_sampler_pkg;
  import abr_params_pkg::*;

  parameter ABR_COEFF_CNT = 256;

//SHA3 Configuration
// Keccak Rounds per clock
  parameter RoundsPerClock = 2;
// Do not enable masking
  parameter Sha3EnMasking = 0;
  parameter Sha3Share = (Sha3EnMasking) ? 2 : 1;

//Sampler Configurations
//MLDSA Rej Sampler
  parameter MLDSA_REJS_NUM_SAMPLERS     = 5;
  parameter MLDSA_REJS_SAMPLE_W         = 24;

//MLKEM Rej Sampler
  parameter MLKEM_REJS_NUM_SAMPLERS     = 10;
  parameter MLKEM_REJS_SAMPLE_W         = 12;

  //Rej Sampler common params
  //MLDSA and MLKEM output rate should match
  parameter REJS_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter REJS_PISO_BUFFER_W    = 1440;
  parameter REJS_PISO_INPUT_RATE  = 1344;
  parameter REJS_PISO_OUTPUT_RATE = MLDSA_REJS_NUM_SAMPLERS*MLDSA_REJS_SAMPLE_W;

//Rej Bounded
  parameter REJB_NUM_SAMPLERS     = 8;
  parameter REJB_SAMPLE_W         = 4;
  parameter REJB_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter REJB_VLD_SAMPLES_W    = 24;
  parameter REJB_VALUE            = 15;
  parameter REJB_VLD_SAMPLE_W     = $clog2(REJB_VALUE);
  parameter REJB_PISO_BUFFER_W    = 1334;
  parameter REJB_PISO_INPUT_RATE  = 1088;
  parameter REJB_PISO_OUTPUT_RATE = REJB_NUM_SAMPLERS*REJB_SAMPLE_W;

//Exp Mask
  parameter EXP_NUM_SAMPLERS     = 4;
  parameter EXP_SAMPLE_W         = 20;
  parameter EXP_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter EXP_VLD_SAMPLE_W     = 24;
  parameter EXP_PISO_BUFFER_W    = 1152;
  parameter EXP_PISO_INPUT_RATE  = 1088;
  parameter EXP_PISO_OUTPUT_RATE = EXP_NUM_SAMPLERS*EXP_SAMPLE_W;

//Sample In Ball
  parameter SIB_NUM_SAMPLERS     = 4;
  parameter SIB_SAMPLE_W         = 8;
  parameter SIB_TAU              = 60;
  parameter SIB_PISO_BUFFER_W    = 1344;
  parameter SIB_PISO_INPUT_RATE  = 1088;
  parameter SIB_PISO_OUTPUT_RATE = SIB_NUM_SAMPLERS*SIB_SAMPLE_W;

  //CBD Sampler
  parameter CBD_NUM_SAMPLERS     = COEFF_PER_CLK;
  parameter CBD_SAMPLE_W         = 2*MLKEM_ETA;
  parameter CBD_VLD_SAMPLES      = COEFF_PER_CLK;
  parameter CBD_PISO_BUFFER_W    = 1344;
  parameter CBD_PISO_INPUT_RATE  = 1088;
  parameter CBD_PISO_OUTPUT_RATE = CBD_NUM_SAMPLERS*CBD_SAMPLE_W;


  //declare fsm state variables
  typedef enum logic [2:0] {
    ABR_SAMPLER_IDLE   = 3'b000,
    ABR_SAMPLER_PROC   = 3'b001,
    ABR_SAMPLER_WAIT   = 3'b010,
    ABR_SAMPLER_RUN    = 3'b011,
    ABR_SAMPLER_DONE   = 3'b100
  } abr_sampler_fsm_state_e;

  typedef enum logic [2:0] {
    ABR_REJS_MODE,
    ABR_REJB_MODE,
    ABR_EXP_MODE,
    ABR_SIB_MODE,
    ABR_CBD_MODE
  } abr_piso_mode_e;

  //common structures
  typedef enum logic [4:0] {
    ABR_SAMPLER_NONE,
    //SHA/SHAKE only modes
    ABR_SHAKE256,
    ABR_SHAKE128,
    ABR_SHA512,
    ABR_SHA256,
    //SAMPLER MODES
    MLDSA_REJ_SAMPLER,
    MLKEM_REJ_SAMPLER,
    ABR_EXP_MASK,
    ABR_REJ_BOUNDED,
    ABR_SAMPLE_IN_BALL,
    ABR_CBD_SAMPLER
  } abr_sampler_mode_e;

endpackage

`endif
