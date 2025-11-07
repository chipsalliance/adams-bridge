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

// Pre-Allocated read latency buffer for covering SRAM read latencies
// Variable width read and write
// Intended for use where space can be pre-allocated at SRAM read time so that room is available
// in the buffer when the data arrives. Needs to be sized appropriately to cover the read latency while
// providing max throughput on the buffer output.
// Writes are pushed onto the buffer WR_WIDTH at a time when data_valid_i is asserted
// Outputs are presented valid once RD_WIDTH entries are valid in the buffer

module abr_rd_lat_buffer
  #(
   parameter WR_WIDTH = 128
  ,parameter RD_WIDTH = 64
  ,parameter BUFFER_DEPTH = WR_WIDTH + RD_WIDTH
  )
  (
  input logic clk,
  input logic rst_b,

  input logic zeroize,

  //input data
  input  logic                data_valid_i,
  input  logic [WR_WIDTH-1:0] data_i,
  //output data
  output logic                data_valid_o,
  output logic [RD_WIDTH-1:0] data_o

  );

  logic buffer_rd, buffer_wr;
  logic update_buffer;

  //Buffer
  logic [BUFFER_DEPTH-1:0] buffer, buffer_d, buffer_shift, buffer_wr_data_shift;
  logic [$clog2(BUFFER_DEPTH):0] wr_ptr, wr_ptr_d;

  //Read when we have NUM_RD worth of valid data
  always_comb buffer_rd = wr_ptr >= RD_WIDTH;
  //Write as long as we have 1 valid sample and not full
  always_comb buffer_wr = data_valid_i;
  //update buffer for any read or write
  always_comb update_buffer = buffer_rd | buffer_wr;

  always_comb begin
    //next write pointer
    if (buffer_wr & buffer_rd)
      wr_ptr_d = wr_ptr + WR_WIDTH - RD_WIDTH;
    else if (buffer_wr)
      wr_ptr_d = wr_ptr + WR_WIDTH;
    else if (buffer_rd)
      wr_ptr_d = wr_ptr - RD_WIDTH;
    else
      wr_ptr_d = wr_ptr;
  end

  //Shift the buffer contents and append new samples
  always_comb begin
    //shift the write data left by the wr_ptr, or wr_ptr - RD_WIDTH if there is a read
    buffer_wr_data_shift = buffer_wr & buffer_rd ? BUFFER_DEPTH'(data_i << (wr_ptr - RD_WIDTH)) : 
                           buffer_wr             ? BUFFER_DEPTH'(data_i << wr_ptr) : '0;

    //shift the buffer data right by NUM_RD if there is a read
    buffer_shift = buffer_rd ? BUFFER_DEPTH'(buffer >> RD_WIDTH) : buffer;

    //OR together the write data and the buffer data
    buffer_d = buffer_shift | buffer_wr_data_shift;
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      buffer <= '0;
      wr_ptr <= '0;
    end else if (zeroize) begin
      buffer <= '0;
      wr_ptr <= '0;
    end else if (update_buffer) begin
      buffer <= buffer_d;
      wr_ptr <= wr_ptr_d;
    end 
  end

  //Output is valid when we have NUM_RD worth of valid data
  always_comb data_valid_o = buffer_rd & ~zeroize;
  always_comb data_o = buffer[RD_WIDTH-1:0];

endmodule