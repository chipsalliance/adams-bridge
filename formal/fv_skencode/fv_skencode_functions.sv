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
// | Created on 05.04.2025 at 12:39                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


package fv_skencode_functions;


function logic unsigned [31:0] encode(logic unsigned [7:0][23:0] data_to_be_encoded);
  logic unsigned [31:0] encoded_data;  // @ skencode.h:106:17
  logic unsigned [7:0] encoding_error; // @ skencode.h:107:17
  logic unsigned [31:0] top_zeros;     // @ skencode.h:108:17
  logic signed [31:0] i;               // @ skencode.h:110:21

  encoded_data = 32'd0;
  encoding_error = 8'd0;
  top_zeros = 32'hFFFFFF;

  for (i = 32'd0; i < 32'd8; i = i + 32'd1) begin
    if (((64'd2 < data_to_be_encoded[unsigned'(i)]) && (data_to_be_encoded[unsigned'(i)] < 64'd8380415)) || (64'd8380416 < data_to_be_encoded[unsigned'(i)])) begin
      encoded_data = (24'd0 << unsigned'(24'(i * 32'd3))) | encoded_data;
      encoding_error = (8'd1 << unsigned'(8'(i))) | encoding_error;
    end else begin
      encoded_data = ((((24'd2 + 64'd8380417) - data_to_be_encoded[unsigned'(i)]) % 64'd8380417) << unsigned'(24'(i * 32'd3))) | encoded_data;
      encoding_error = (8'd0 << unsigned'(8'(i))) | encoding_error;
    end
  end

  encoded_data = encoded_data & top_zeros;
  return encoded_data;
endfunction


function logic unsigned [0:0] encode_error(logic unsigned [7:0][23:0] data_to_be_encoded);
  logic unsigned [31:0] encoded_data;  // @ skencode.h:150:17
  logic unsigned [7:0] encoding_error; // @ skencode.h:151:17
  logic unsigned [31:0] top_zeros;     // @ skencode.h:152:17
  logic signed [31:0] i_0;             // @ skencode.h:154:21
  logic unsigned [0:0] error_flag;     // @ skencode.h:161:17
  logic signed [31:0] i_1;             // @ skencode.h:162:22

  encoded_data = 32'd0;
  encoding_error = 8'd0;
  top_zeros = 32'hFFFFFF;

  for (i_0 = 32'd0; i_0 < 32'd8; i_0 = i_0 + 32'd1) begin
    if (((64'd2 < data_to_be_encoded[unsigned'(i_0)]) && (data_to_be_encoded[unsigned'(i_0)] < 64'd8380415)) || (64'd8380416 < data_to_be_encoded[unsigned'(i_0)])) begin
      encoding_error = (8'd1 << unsigned'(8'(i_0))) | encoding_error;
    end else begin
      encoding_error = (8'd0 << unsigned'(8'(i_0))) | encoding_error;
    end
  end

  error_flag = 1'd0;

  for (i_1 = 32'd0; i_1 < 32'd8; i_1 = i_1 + 32'd1) begin
    error_flag = error_flag | encoding_error[i_1];
  end

  return error_flag;
endfunction


function logic unsigned [31:0] bitwise_or(logic unsigned [31:0] operandA, logic unsigned [31:0] operandB);
  return 32'(operandA | operandB);
endfunction


function logic unsigned [13:0] shift_amount(logic unsigned [13:0] num_api_operands);
  return 14'((num_api_operands % 64'd3) * 64'd8);
endfunction


function logic unsigned [13:0] shift_amount_first(logic unsigned [13:0] num_api_operands);
  return 14'((64'd3 - (num_api_operands % 64'd3)) * 64'd8);
endfunction


endpackage
