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
// | Created on 21.11.2024 at 16:31                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sigdecode_z_top_functions;

import fv_sigdecode_z_top_pkg::*;


// Functions

function a_unsigned_24_8 decode(a_unsigned_20_8 data);
  logic unsigned [23:0] decode_coefficient_0_i;
  logic unsigned [23:0] decode_coefficient_1_i;
  logic unsigned [23:0] decode_coefficient_2_i;
  logic unsigned [23:0] decode_coefficient_3_i;
  logic unsigned [23:0] decode_coefficient_4_i;
  logic unsigned [23:0] decode_coefficient_5_i;
  logic unsigned [23:0] decode_coefficient_6_i;
  logic unsigned [23:0] decode_coefficient_7_i;

  decode_coefficient_0_i = decode_coefficient(data[0]);
  decode_coefficient_1_i = decode_coefficient(data[1]);
  decode_coefficient_2_i = decode_coefficient(data[2]);
  decode_coefficient_3_i = decode_coefficient(data[3]);
  decode_coefficient_4_i = decode_coefficient(data[4]);
  decode_coefficient_5_i = decode_coefficient(data[5]);
  decode_coefficient_6_i = decode_coefficient(data[6]);
  decode_coefficient_7_i = decode_coefficient(data[7]);

  return '{
      0: decode_coefficient_0_i,
      1: decode_coefficient_1_i,
      2: decode_coefficient_2_i,
      3: decode_coefficient_3_i,
      4: decode_coefficient_4_i,
      5: decode_coefficient_5_i,
      6: decode_coefficient_6_i,
      7: decode_coefficient_7_i
  };
endfunction

function logic unsigned [23:0] decode_coefficient(logic unsigned [19:0] data);
  return 24'((('h87E001 - 24'(data)) % 8380417));
endfunction


endpackage
