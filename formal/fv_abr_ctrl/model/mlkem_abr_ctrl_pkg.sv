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
// | Created on 11.09.2025 at 19:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package mlkem_abr_ctrl_pkg;


typedef enum logic unsigned [2:0] { NoOp, MlkemKeygen, MlkemkeygenDecap, MlkemEncap, MlkemDecap } e_InstructionType;

typedef enum logic unsigned [3:0] { Ntt = 1, Intt = 2, Pwm = 3, PwmAccum = 4, PwmSampler = 5, PwmAccuSampler = 6, Pwa = 7, Pws = 8 } e_NttMode;

typedef enum logic unsigned [2:0] { Sha512 = 0, Shake256 = 1, Sha256 = 2, RejSampler = 3, Cbd = 7 } e_SamplerMode;

typedef logic unsigned [7:0][31:0] a_unsigned_32_8;

typedef struct packed {
  e_InstructionType instr;
  a_unsigned_32_8 seed;
  a_unsigned_32_8 seed_z;
  logic unsigned [255:0] rho;
  logic unsigned [511:0] sigma;
  logic unsigned [255:0] sigma_z;
  logic unsigned [511:0] tr;
} st_FromApiType;

typedef struct packed {
  e_NttMode mode;
  logic unsigned [14:0] operand1;
  logic unsigned [14:0] operand2;
  logic unsigned [14:0] destination;
  logic masking_en;
  logic shuffle_en;
} st_NttType;

typedef struct packed {
  logic encaps_wr_ack;
  logic decaps_wr_ack;
  logic api_ek_reg_wr_dec;
  logic api_dk_reg_wr_dec;
  logic unsigned [5:0] api_ek_reg_waddr;
  logic unsigned [5:0] api_dk_reg_waddr;
  logic unsigned [31:0] api_ek_reg_wdata;
  logic unsigned [31:0] api_dk_reg_wdata;
} st_RegsApiType;

typedef struct packed {
  logic unsigned [255:0] rho;
  logic unsigned [511:0] sigma;
  logic unsigned [255:0] sigma_z;
} st_RegsType;

typedef struct packed {
  logic unsigned [511:0] tr;
  logic unsigned [39167:0] sk_out;
} st_ToApiType;

typedef struct packed {
  e_SamplerMode mode;
  logic unsigned [14:0] destination;
} st_ToSamplerType;

typedef struct packed {
  logic unsigned [1:0] mode;
  logic unsigned [2:0] poly;
  logic compare_mode_o;
  logic unsigned [14:0] src0;
  logic unsigned [14:0] src1;
  logic unsigned [14:0] dest;
} st_toCompressType;

typedef struct packed {
  logic unsigned [1:0] mode;
  logic unsigned [2:0] poly;
  logic unsigned [14:0] src0;
  logic unsigned [14:0] src1;
  logic unsigned [14:0] dest;
} st_toDeCompressType;

typedef struct packed {
  logic unsigned [63:0] data;
  logic unsigned [7:0] strobe;
} st_to_keccakType;

typedef logic unsigned [3:0][14:0] a_unsigned_15_4;


endpackage
