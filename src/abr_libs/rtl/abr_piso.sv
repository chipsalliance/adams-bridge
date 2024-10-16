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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either sibress or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


module abr_piso
  //    import ::*;
  #(
     parameter PISO_NUM_MODE    = 1
    ,parameter PISO_BUFFER_W    = 1344
    ,parameter integer PISO_INPUT_RATE[PISO_NUM_MODE-1:0]  = {1088}
    ,parameter integer PISO_OUTPUT_RATE[PISO_NUM_MODE-1:0] = {80}
  )
  (
    input logic                          clk,
    input logic                          rst_b,
    input logic                          zeroize,
    
    //input data
    input  logic [$clog2(PISO_NUM_MODE)-1:0] mode,
    input  logic                             valid_i,
    output logic                             hold_o,
    input  logic [PISO_INPUT_RATE[0]-1:0]    data_i,

    //Output data 
    output logic                             valid_o,
    input  logic                             hold_i,
    output logic [PISO_OUTPUT_RATE[0]-1:0]   data_o

  );

  parameter PISO_PTR_W = $clog2(PISO_BUFFER_W);
  parameter BUFFER_W_DELTA = PISO_BUFFER_W - PISO_INPUT_RATE[0];

  logic [PISO_BUFFER_W-1:0] buffer, buffer_d;
  logic [PISO_PTR_W-1:0] buffer_wr_ptr, buffer_wr_ptr_d;

  logic buffer_wr, buffer_rd;
  logic update_buffer;

  //hold when not enough room for full input data
  always_comb hold_o = buffer_wr_ptr > (PISO_BUFFER_W[PISO_PTR_W-1:0] - PISO_INPUT_RATE[mode][PISO_PTR_W-1:0]);

  always_comb data_o = buffer[PISO_OUTPUT_RATE[0]-1:0];
  always_comb valid_o = buffer_wr_ptr >= PISO_OUTPUT_RATE[mode][PISO_PTR_W-1:0];

  always_comb buffer_wr = valid_i & ~hold_o;
  always_comb buffer_rd = valid_o & ~hold_i;
  always_comb update_buffer = buffer_rd | buffer_wr;

  //storage element
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      buffer <= '0;
      buffer_wr_ptr <= '0;
    end else if (zeroize) begin
      buffer <= '0;
      buffer_wr_ptr <= '0;
    end else if (update_buffer) begin
      buffer <= buffer_d;
      buffer_wr_ptr <= buffer_wr_ptr_d;
    end 
  end

  //write pointer control
  always_comb begin
    unique case ({buffer_rd, buffer_wr}) 
      2'b00 : buffer_wr_ptr_d = buffer_wr_ptr;
      2'b01 : buffer_wr_ptr_d = buffer_wr_ptr + PISO_INPUT_RATE[mode][PISO_PTR_W-1:0];
      2'b10 : buffer_wr_ptr_d = buffer_wr_ptr - PISO_OUTPUT_RATE[mode][PISO_PTR_W-1:0];
      2'b11 : buffer_wr_ptr_d = buffer_wr_ptr + (PISO_INPUT_RATE[mode][PISO_PTR_W-1:0] - PISO_OUTPUT_RATE[mode][PISO_PTR_W-1:0]);
      default : buffer_wr_ptr_d = buffer_wr_ptr;
    endcase
  end

  logic [PISO_BUFFER_W-1:0] buffer_wdata;
  logic [PISO_BUFFER_W-1:0] buffer_wdata_mask;

  always_comb begin
    buffer_wdata = '0;
    buffer_wdata_mask = '1;
    for (int i = 0; i < PISO_NUM_MODE; i++) begin
      if (i == mode) begin
        buffer_wdata_mask = PISO_BUFFER_W'(buffer_wdata_mask >> (PISO_BUFFER_W[PISO_PTR_W-1:0] - PISO_INPUT_RATE[mode][PISO_PTR_W-1:0]));
      end
    end
    buffer_wdata = {{BUFFER_W_DELTA{1'b0}},data_i} & buffer_wdata_mask;
  end

  //buffer next logic
  always_comb begin
    unique case ({buffer_rd, buffer_wr})
      2'b00 : buffer_d = buffer;
      2'b10 : buffer_d = PISO_BUFFER_W'(buffer >> PISO_OUTPUT_RATE[mode]);
      2'b01 : buffer_d = PISO_BUFFER_W'(buffer_wdata << buffer_wr_ptr) | buffer;
      2'b11 : buffer_d = PISO_BUFFER_W'(buffer_wdata << (buffer_wr_ptr - PISO_OUTPUT_RATE[mode][PISO_PTR_W-1:0])) | PISO_BUFFER_W'(buffer >> PISO_OUTPUT_RATE[mode]);

      default : buffer_d = buffer;
    endcase
  end
 // {{PISO_BUFFER_W - PISO_INPUT_RATE[mode]{1'b0}},

endmodule
