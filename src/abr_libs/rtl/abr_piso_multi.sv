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

// PISO supports multiple modes of operation, each with unique input and output rates

module abr_piso_multi #(
  parameter int NUM_MODES = 5,
  parameter int PISO_BUFFER_W = 1344,
  parameter int PISO_PTR_W = $clog2(PISO_BUFFER_W),
  parameter int PISO_ACT_INPUT_RATE = 1088,
  parameter int PISO_ACT_OUTPUT_RATE = 80,
  parameter int INPUT_RATES [NUM_MODES] = '{1088, 1088, 1088, 1088, 1088},
  parameter int OUTPUT_RATES[NUM_MODES] = '{80, 80, 80, 80, 80}
)(
  input  logic                          clk,
  input  logic                          rst_b,
  input  logic                          zeroize,
  input  logic [$clog2(NUM_MODES)-1:0]  mode,
  input  logic                          valid_i,
  output logic                          hold_o,
  input  logic [PISO_ACT_INPUT_RATE-1:0] data_i,
  output logic                          valid_o,
  input  logic                          hold_i,
  output logic [PISO_ACT_OUTPUT_RATE-1:0] data_o
);

  localparam BUFFER_W_DELTA = PISO_BUFFER_W - PISO_ACT_INPUT_RATE;

  logic [PISO_BUFFER_W-1:0] buffer, buffer_d;
  logic [PISO_PTR_W-1:0] buffer_wr_ptr, buffer_wr_ptr_d;
  logic [PISO_PTR_W-1:0] current_input_rate, current_output_rate;

  logic buffer_wr, buffer_rd;
  logic update_buffer;

  // Select input/output rates based on mode
  always_comb begin
    current_input_rate  = INPUT_RATES[mode][PISO_PTR_W-1:0];
    current_output_rate = OUTPUT_RATES[mode][PISO_PTR_W-1:0];
  end

  // Flow control
  always_comb hold_o  = buffer_wr_ptr > (PISO_BUFFER_W[PISO_PTR_W-1:0] - current_input_rate);
  always_comb data_o  = buffer[PISO_ACT_OUTPUT_RATE-1:0];
  always_comb valid_o = buffer_wr_ptr >= current_output_rate;

  always_comb buffer_wr = valid_i & ~hold_o;
  always_comb buffer_rd = valid_o & ~hold_i;
  always_comb update_buffer = buffer_rd | buffer_wr;

  // Storage element
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

  // Write pointer control
  always_comb begin
    unique case ({buffer_rd, buffer_wr})
      2'b00 : buffer_wr_ptr_d = buffer_wr_ptr;
      2'b01 : buffer_wr_ptr_d = buffer_wr_ptr + current_input_rate;
      2'b10 : buffer_wr_ptr_d = buffer_wr_ptr - current_output_rate;
      2'b11 : buffer_wr_ptr_d = buffer_wr_ptr + (current_input_rate - current_output_rate);
      default : buffer_wr_ptr_d = buffer_wr_ptr;
    endcase
  end

  // Write data and mask
  logic [PISO_BUFFER_W-1:0] buffer_wdata;
  logic [PISO_BUFFER_W-1:0] buffer_wdata_mask;

  always_comb begin
    buffer_wdata = '0;
    buffer_wdata_mask = '1;
    buffer_wdata_mask = PISO_BUFFER_W'(buffer_wdata_mask >> (PISO_BUFFER_W[PISO_PTR_W-1:0] - current_input_rate));
    buffer_wdata = {{BUFFER_W_DELTA{1'b0}}, data_i} & buffer_wdata_mask;
  end

  // Buffer update logic
  always_comb begin
    unique case ({buffer_rd, buffer_wr})
      2'b00 : buffer_d = buffer;
      2'b10 : buffer_d = PISO_BUFFER_W'(buffer >> current_output_rate);
      2'b01 : buffer_d = PISO_BUFFER_W'(buffer_wdata << buffer_wr_ptr) | buffer;
      2'b11 : buffer_d = PISO_BUFFER_W'(buffer_wdata << (buffer_wr_ptr - current_output_rate)) |
                         PISO_BUFFER_W'(buffer >> current_output_rate);
      default : buffer_d = buffer;
    endcase
  end

endmodule
