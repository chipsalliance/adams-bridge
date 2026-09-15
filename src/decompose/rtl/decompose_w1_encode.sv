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
    import abr_params_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire w1_encode_enable, //level not pulse. Indicates r1 lut is valid from decompose block
        input wire [3:0][MLDSA_W1_COEFF_W-1:0] r1_i,
        //Selects gamma2 = (q-1)/88 (ML-DSA-44), i.e. 6-bit w1 coefficients.
        //Public control, never secret.
        input wire gamma2_88_i,

        output logic [63:0] w1_o,
        output logic buffer_en
    );

    logic [63:0] w1_32;
    logic        buffer_en_32;

    localparam BUFFER_CYC = 4;

    //Enable counter
    logic [1:0] buffer_count;

    //Flags
    logic w1_en_reg;
    logic init_count_first;
    logic decr_buf_count;

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

    //Decr logic
    assign decr_buf_count = w1_en_reg;

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

    assign buffer_en_32     = w1_en_reg && (buffer_count == 'h0);

    //r1 shift reg. 4 coefficients x 4 bits = 16 bits per cycle divides 64, so a
    //plain shift register fills one word every BUFFER_CYC cycles.
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            w1_32 <= 'h0;
        else if (zeroize)
            w1_32 <= 'h0;
        else if (w1_encode_enable)
            w1_32 <= {r1_i[3][3:0], r1_i[2][3:0], r1_i[1][3:0], r1_i[0][3:0], w1_32[63:16]};
    end

    //--------------------------------------------------------------------------
    // ML-DSA-44 path: 6-bit coefficients give 24 bits per cycle, which does NOT
    // divide 64, so a shift register cannot be used. Accumulate into a wider
    // register and emit a 64-bit word whenever at least 64 bits are pending.
    // The bit count is always a multiple of 8 (gcd(24,64) = 8), so the insert
    // position is a byte shift. Over 8 cycles 192 bits are produced and exactly
    // 3 words are emitted; a 256-coefficient polynomial is 1536 bits = 24 words,
    // so every polynomial starts and ends byte-aligned.
    //--------------------------------------------------------------------------
    generate
        if (ABR_NEED_GAMMA2_88) begin : gen_w1_88
            localparam int ACC_W = 88; //max pending bits before an emit is 56+24

            logic [ACC_W-1:0] acc, acc_base, acc_nxt;
            logic [2:0]       cnt8, cnt8_base; //pending bytes, 0..7
            logic [23:0]      din24;
            logic             emit;
            logic [63:0]      w1_88;
            logic             buffer_en_88;

            always_comb begin
                din24     = {r1_i[3], r1_i[2], r1_i[1], r1_i[0]};
                acc_base  = init_count_first ? '0 : acc;
                cnt8_base = init_count_first ? '0 : cnt8;
                acc_nxt   = acc_base | (ACC_W'(din24) << {cnt8_base, 3'b000});
                //3 more bytes pending; emit as soon as the total reaches 8
                emit      = (cnt8_base >= 3'd5);
            end

            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    acc          <= '0;
                    cnt8         <= '0;
                    w1_88        <= '0;
                    buffer_en_88 <= 1'b0;
                end
                else if (zeroize) begin
                    acc          <= '0;
                    cnt8         <= '0;
                    w1_88        <= '0;
                    buffer_en_88 <= 1'b0;
                end
                else begin
                    buffer_en_88 <= w1_encode_enable & emit;
                    if (w1_encode_enable) begin
                        acc   <= emit ? (acc_nxt >> 64)    : acc_nxt;
                        cnt8  <= emit ? (cnt8_base - 3'd5) : (cnt8_base + 3'd3);
                        if (emit) w1_88 <= acc_nxt[63:0];
                    end
                end
            end

            always_comb begin
                w1_o      = gamma2_88_i ? w1_88        : w1_32;
                buffer_en = gamma2_88_i ? buffer_en_88 : buffer_en_32;
            end
        end
        else begin : gen_w1_32_only
            always_comb begin
                w1_o      = w1_32;
                buffer_en = buffer_en_32;
            end
        end
    endgenerate

endmodule