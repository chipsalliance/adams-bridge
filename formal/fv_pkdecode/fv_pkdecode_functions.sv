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
// | Created on 07.01.2025 at 18:20                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_pkdecode_functions;


function logic unsigned [7:0][23:0] encoded_coeffs(logic unsigned [79:0] data);
  logic unsigned [7:0][23:0] result; // @ pkdecode.h:49:13
  logic unsigned [23:0] temp;        // @ pkdecode.h:50:13
  logic unsigned [23:0] mask;        // @ pkdecode.h:51:13
  logic signed [31:0] i;             // @ pkdecode.h:52:17

  result = '{ 0: 24'd0, 1: 24'd0, 2: 24'd0, 3: 24'd0, 4: 24'd0, 5: 24'd0, 6: 24'd0, 7: 24'd0 };
  temp = 24'd0;
  mask = unsigned'(24'((32'd1 << 32'd10) - 32'd1));

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    temp = (data >> (32'd10 * i)) & mask;
    result[unsigned'(i)] = temp << 32'd13;
  end

  return result;
endfunction


endpackage
