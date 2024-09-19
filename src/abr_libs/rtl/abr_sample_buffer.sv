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

// Sample Buffer takes in NUM_WR samples and valid bits
// Valid samples are packed and shifted onto a buffer
// Outputs are presented valid once NUM_RD entries are valid in the buffer

module abr_sample_buffer
  //    import ::*;
  #(
   parameter NUM_WR = 5
  ,parameter NUM_RD  = 4
  ,parameter BUFFER_DATA_W = 32
  ,parameter OPT_BUFFER_DEPTH = 0
  ,localparam BUFFER_DEPTH = (NUM_WR + NUM_RD)
  ,localparam BUF_W = BUFFER_DEPTH*BUFFER_DATA_W
  )
  (
  input logic clk,
  input logic rst_b,

  input logic zeroize,

  //input data
  input  logic [NUM_WR-1:0]                    data_valid_i,
  input  logic [NUM_WR-1:0][BUFFER_DATA_W-1:0] data_i,
  output logic                                 buffer_full_o,
  //output data
  output logic                                 data_valid_o,
  output logic [NUM_RD-1:0][BUFFER_DATA_W-1:0] data_o

  );

  logic buffer_rd, buffer_wr;
  logic update_buffer;

  //Incoming samples to write to buffer
  logic [BUFFER_DEPTH-1:0][BUFFER_DATA_W-1:0] buffer_wr_data, buffer_wr_data_shift;
  logic [BUFFER_DEPTH-1:0] buffer_wr_valid, buffer_wr_valid_shift;

  //Valid sample buffer
  logic [BUFFER_DEPTH-1:0] buffer_valid, buffer_valid_d, buffer_valid_shift;
  logic [BUFFER_DEPTH-1:0][BUFFER_DATA_W-1:0] buffer, buffer_d, buffer_shift;
  logic [$clog2(BUFFER_DEPTH):0] num_valid;


  //Buffer is full when it can't take a full write cycle
  //Check for at least N entries available, where N is the difference between WR/RD bandwidth
  generate
    if (NUM_WR == NUM_RD)  always_comb buffer_full_o = '0;
    else                   always_comb buffer_full_o = buffer_valid[(BUFFER_DEPTH-(NUM_WR-NUM_RD))];
  endgenerate
  //Read when we have NUM_RD worth of valid data
  always_comb buffer_rd = buffer_valid[NUM_RD-1]; 
  //Write as long as we have 1 valid sample and not full
  always_comb buffer_wr = (|data_valid_i) & ~buffer_full_o;
  //update buffer for any read or write
  always_comb update_buffer = buffer_rd | buffer_wr;

  always_comb begin
    //count the valid entries in the buffer already
    num_valid = '0;
    for (int i = 0; i < BUFFER_DEPTH; i++) begin
      if (buffer_valid[i] == 1'b1) num_valid += 1'b1;
    end
  end

  //Concat the valid samples
  logic [$clog2(BUFFER_DEPTH)-1:0] sample_wr_ptr;
  always_comb begin
    sample_wr_ptr = '0;
    buffer_wr_data = '0;
    buffer_wr_valid = '0;
    for (int sample = 0; sample < NUM_WR; sample++) begin
      if (data_valid_i[sample]) begin
        //concat the next valid sample
        buffer_wr_data[sample_wr_ptr] = data_i[sample][BUFFER_DATA_W-1:0];
        buffer_wr_valid[sample_wr_ptr] = 1'b1;
        //increment the write pointer
        sample_wr_ptr += 1;
      end
    end

    //shift the write data left by the count, or count - NUM_RD if there is a read
    buffer_wr_data_shift = buffer_rd ? buffer_wr_data << (num_valid - NUM_RD)*BUFFER_DATA_W : 
                                       buffer_wr_data << (num_valid)*BUFFER_DATA_W;
    buffer_wr_valid_shift = buffer_wr ?
                            (buffer_rd ? buffer_wr_valid << (num_valid - NUM_RD) :
                                         buffer_wr_valid << (num_valid)) : '0;
  end

  //Shift the buffer contents and append new samples
  always_comb begin
    //shift the buffer data right by NUM_RD if there is a read
    buffer_shift = buffer_rd ? BUF_W'(buffer >> (NUM_RD*BUFFER_DATA_W)) : buffer;
    buffer_valid_shift = buffer_rd ? BUFFER_DEPTH'(buffer_valid >> NUM_RD) : buffer_valid;

    //OR together the write data and the buffer data
    buffer_d = buffer_shift | buffer_wr_data_shift;
    buffer_valid_d = buffer_valid_shift | buffer_wr_valid_shift;
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      buffer <= '0;
      buffer_valid <= '0;
    end else if (zeroize) begin
      buffer <= '0;
      buffer_valid <= '0;
    end else if (update_buffer) begin
      buffer <= buffer_d;
      buffer_valid <= buffer_valid_d;
    end 
  end

  //Output is valid when we have NUM_RD worth of valid data
  always_comb data_valid_o = buffer_rd & ~zeroize;
  always_comb data_o = buffer[NUM_RD-1:0];

endmodule