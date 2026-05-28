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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |

// | Created on 12.12.2024 at 10:40                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package global_package;


typedef enum logic unsigned [2:0] { NoOp, Keygen, Sign, Verify, KeygenSign } e_InstructionType;

typedef enum logic unsigned [3:0] {None = 0, Ntt = 1, Intt = 2, Pwm = 3, PwmSampler = 5, PwmAccuSampler = 6, Pwa = 7, Pws = 8 } e_NttMode;

typedef enum logic unsigned [2:0] { Shake256 = 1, RejSampler = 3, ExpMask = 4, RejBounded = 5, SampleInBall = 6 } e_SamplerMode;

//typedef logic unsigned [9:0][31:0] a_unsigned_32_10;

typedef struct packed {
  logic unsigned [14:0] source_addr;
  logic unsigned [14:0] destination;
} st_DecomposeType;

typedef logic unsigned [647:0][31:0] a_unsigned_32_648;

typedef logic unsigned [7:0][31:0] a_unsigned_32_8;

typedef struct packed {
  e_InstructionType instr;
  a_unsigned_32_8 seed;
  a_unsigned_32_8 sign_rnd;
  logic unsigned [511:0] tr;
  a_unsigned_32_648 pk;
  logic unsigned [39167:0] sk_in;
} st_FromApiType;

typedef struct packed {
  logic unsigned [15:0] immediate;
  logic unsigned [14:0] source_addr;
} st_NormCheckType;

typedef struct packed {
  e_NttMode mode;
  logic unsigned [14:0] operand1;
  logic unsigned [14:0] operand2;
  logic unsigned [14:0] destination;
} st_NttType;

typedef struct packed {
  logic unsigned [14:0] destination;
} st_PkDecodeType;

typedef struct packed {
  logic unsigned [14:0] t_addr;
} st_Power2RoundType;

typedef logic unsigned [15:0][31:0] a_unsigned_32_16;

typedef struct packed {
  logic unsigned [255:0] rho;
  logic unsigned [511:0] rho_prime;
  logic unsigned [255:0] K;
  logic unsigned [511:0] mu;
  logic unsigned [15:0] kappa;
  a_unsigned_32_16 c;
} st_RegsType;

typedef struct packed {
  logic unsigned [14:0] destination;
} st_SigDecodeType;

typedef struct packed {
  logic unsigned [14:0] coeff_addr;
} st_SkEncodeType;

typedef struct packed {
  logic unsigned [511:0] tr;
  logic unsigned [39167:0] sk_out;
} st_ToApiType;

typedef struct packed {
  e_SamplerMode mode;
  logic unsigned [14:0] destination;
} st_ToSamplerType;

typedef struct packed {
  logic unsigned [14:0] operand1;
  logic unsigned [14:0] operand2;
} st_UseHintType;

typedef logic unsigned [6:0][14:0] a_unsigned_15_7;

typedef logic unsigned [7:0][14:0] a_unsigned_15_8;

typedef logic unsigned [9:0][31:0] a_unsigned_32_10;

typedef logic unsigned [16:0][31:0] a_unsigned_32_17;


// Constants

parameter logic unsigned [15:0] norm_check_z_immediate = 16'd0;


endpackage
