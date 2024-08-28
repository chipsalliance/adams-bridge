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
//======================================================================
//
// decompose_w1_encode.sv
// --------
// 1. Decompose produces 4-bits * 4 = 16-bits of r1 per cycle. This needs to be
//      consumed by Keccak which takes 64-bits per cycle. w1_encode block buffers
//      16-bits per cycle and asserts a valid every 4 cycles indicating 64-bits are ready
//      for Keccak to sample. 
// 2. Keccak also needs an enable once every 1088 bits (block length) to process the buffered
//      data. w1_encode also provides this enable by counting 17 iterations of buffer valid
//      i.e., 17 * 64-bits = 1088 bits. For every 17 4-cycle loops, keccak is enabled.
// 3. Corner case: the 1st iteration of Keccak takes mu || w1 as input where mu is 512 bits
//      So, only 576 bits of w1 are needed and then Keccak can be enabled. In this case,
//      the keccak_en is asserted after 9 loops (9*64-bits = 576 bits). 
// 4. w1_encode must be performed on 8 input polynomials. Once 8-rounds are Keccak are done,
//      high level controller issues the last round with padding and enables Keccak.

module decompose_w1_encode
    import mldsa_params_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire w1_encode_enable, //level not pulse. Indicates r1 lut is valid from decompose block
        input wire [3:0][3:0] r1_i,

        output logic [63:0] w1_o,
        output logic buffer_en,
        output logic keccak_en,
        
        input wire keccak_done,
        output logic w1_encode_done
    );

    localparam KECCAK_LOOPS_FIRST = 9;
    localparam KECCAK_LOOPS_SUBSEQ = 17;
    localparam BUFFER_CYC = 4;

    //Enable counter
    logic [4:0] keccak_count;
    logic [1:0] buffer_count;
    logic [2:0] rounds_count;

    //Flags
    logic w1_en_reg;
    logic init_count_first, init_count_subseq;
    logic decr_buf_count;
    logic decr_kec_count;

    //Generate a pulse to init counters
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            w1_en_reg <= 'b0;
        else if (zeroize)
            w1_en_reg <= 'b0;
        else
            w1_en_reg <= w1_encode_enable;
    end
    assign init_count_first = w1_encode_enable & ~w1_en_reg;
    assign init_count_subseq = w1_encode_enable & keccak_en;

    //Decr logic
    assign decr_buf_count = w1_en_reg;
    assign decr_kec_count = buffer_en;

    //Buffer enable counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            buffer_count <= 'h0;
        else if (zeroize)
            buffer_count <= 'h0;
        else if (init_count_first)
            buffer_count <= BUFFER_CYC-1;
        else if (decr_buf_count)
            buffer_count <= buffer_count - 'h1;
    end

    //Keccak enable counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            keccak_count <= 'h0;
        else if (zeroize)
            keccak_count <= 'h0;
        else if (init_count_first)
            keccak_count <= KECCAK_LOOPS_FIRST-1;
        else if (init_count_subseq)
            keccak_count <= KECCAK_LOOPS_SUBSEQ-1;
        else if (decr_kec_count && (keccak_count > 'h0))
            keccak_count <= keccak_count - 'h1;
    end

    //Rounds counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            rounds_count <= 'h0;
        else if (zeroize)
            rounds_count <= 'h0;
        else if (init_count_first)
            rounds_count <= MLDSA_K-1;
        else if (keccak_en && (rounds_count > 0))
            rounds_count <= rounds_count - 'h1;
    end

    assign buffer_en        = w1_en_reg && (buffer_count == 'h0);
    //TODO: delay keccak_en by 1 cyc to give time for buffer to latch values?
    assign keccak_en        = w1_en_reg && (keccak_count == 'h0) && (buffer_count == 'h0);
    assign w1_encode_done   = keccak_done && (rounds_count == 'h0);

    //r1 shift reg
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            w1_o <= 'h0;
        else if (zeroize)
            w1_o <= 'h0;
        else if (w1_encode_enable)
            w1_o <= {r1_i, w1_o[63:16]};
    end

endmodule