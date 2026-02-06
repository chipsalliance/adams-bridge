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
// | Created on 05.08.2025 at 16:36                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package ntt_ctrl_ct_mlkem_functions;


function logic unsigned [6:0] twiddle_end_addr(logic unsigned [2:0] count);
  logic unsigned [6:0] result; // @ ntt_ctrl_ct_mlkem.h:62:5

  result = 7'd0;

  case (count)
    64'd0: begin
      result = 32'd0;
    end
    64'd1: begin
      result = 32'd3;
    end
    64'd2: begin
      result = 32'd15;
    end
    64'd3: begin
      result = 32'd63;
    end
    default: begin
      result = 32'd0;
    end
  endcase

  return result;
endfunction


function logic unsigned [6:0] twiddle_offset(logic unsigned [2:0] count);
  logic unsigned [6:0] result; // @ ntt_ctrl_ct_mlkem.h:86:2

  result = 7'd0;

  case (count)
    64'd0: begin
      result = 32'd0;
    end
    64'd1: begin
      result = 32'd1;
    end
    64'd2: begin
      result = 32'd5;
    end
    64'd3: begin
      result = 32'd21;
    end
    default: begin
      result = 32'd0;
    end
  endcase

  return result;
endfunction


function logic unsigned [6:0] twiddle_rand_offset(logic unsigned [2:0] count, logic unsigned [1:0] ptr, logic unsigned [3:0] chunk);
  logic unsigned [6:0] result; // @ ntt_ctrl_ct_mlkem.h:110:3

  result = 7'd0;

  case (count)
    64'd0: begin
      result = 32'd0;
    end
    64'd1: begin
      result = ptr;
    end
    64'd2: begin
      result = ((chunk % 64'd4) * 64'd4) + ptr;
    end
    64'd3: begin
      result = (chunk * 64'd4) + ptr;
    end
    default: begin
      result = 32'd0;
    end
  endcase

  return result;
endfunction


endpackage
