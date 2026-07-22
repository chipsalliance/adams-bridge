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
// | Created on 13.03.2025 at 09:29                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_sigencode_z_top_functions;

import fv_sigencode_z_top_pkg::*;

// Functions

function a_unsigned_20_8 encode(a_unsigned_24_8 data);
  logic unsigned [19:0] encode_coefficient_0_i;
  logic unsigned [19:0] encode_coefficient_1_i;
  logic unsigned [19:0] encode_coefficient_2_i;
  logic unsigned [19:0] encode_coefficient_3_i;
  logic unsigned [19:0] encode_coefficient_4_i;
  logic unsigned [19:0] encode_coefficient_5_i;
  logic unsigned [19:0] encode_coefficient_6_i;
  logic unsigned [19:0] encode_coefficient_7_i;

  encode_coefficient_0_i = encode_coefficient(data[0]);
  encode_coefficient_1_i = encode_coefficient(data[1]);
  encode_coefficient_2_i = encode_coefficient(data[2]);
  encode_coefficient_3_i = encode_coefficient(data[3]);
  encode_coefficient_4_i = encode_coefficient(data[4]);
  encode_coefficient_5_i = encode_coefficient(data[5]);
  encode_coefficient_6_i = encode_coefficient(data[6]);
  encode_coefficient_7_i = encode_coefficient(data[7]);

  return '{
      0: encode_coefficient_0_i,
      1: encode_coefficient_1_i,
      2: encode_coefficient_2_i,
      3: encode_coefficient_3_i,
      4: encode_coefficient_4_i,
      5: encode_coefficient_5_i,
      6: encode_coefficient_6_i,
      7: encode_coefficient_7_i
  };
endfunction

function logic unsigned [19:0] encode_coefficient(logic unsigned [23:0] data);
  if ((data > 24'h80000))
    return (20'hFE001 + { (24'h80000 - data) }[19:0]);
  else
    return { (24'h80000 - data) }[19:0];
endfunction

endpackage
