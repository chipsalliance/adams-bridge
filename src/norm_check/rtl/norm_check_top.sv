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
// norm_check_top.sv
// --------
// Performs the 3 validity checks (z, r0, ct0) needed for signing algorithm based on mode selection
// Generates one final invalid bit that is accumulated across all polynomials of the chosen vector
// Since this module only has to read from memory, two addresses are read per cycle to increase bandwidth
// and reduce latency, i.e. 8 coeffs are processed per cycle, and 8 check units are instantiated

// Once the norm_check_done is asserted, the invalid flag needs to be latched at the top level
// for future use in signing algo. Assuming it takes 1 cycle to latch the value, ready is asserted 1 cycle later
// to let HLC know that norm_check operation is done for that vector and next one can be queued
// TODO: see if this needs any changes

// TODO: embed z and r0 checks in decompose?
// TODO: need a restart input (other than zeroize)

module norm_check_top
    import abr_params_pkg::*;
    import norm_check_defines_pkg::*;
    #(
        parameter MLDSA_N = 256
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire norm_check_enable,
        input chk_norm_mode_t mode,

        input wire [5:0] randomness,

        input wire [ABR_MEM_ADDR_WIDTH-1:0] mem_base_addr,
        output mem_if_t mem_rd_req,
        input [4*REG_SIZE-1:0] mem_rd_data,
        output logic invalid,
        output logic norm_check_ready,
        output logic norm_check_done
    );

    logic [3:0] check_a_invalid;
    logic check_enable, check_enable_reg;
    logic norm_check_done_int;

    generate 
        for (genvar i = 0; i < 4; i++) begin : gen_check_a_invalid
            norm_check check_inst (
                .enable(check_enable_reg),
                .mode(mode),
                .opa_i(mem_rd_data[(REG_SIZE-2)+(i*REG_SIZE):i*REG_SIZE]),
                .invalid(check_a_invalid[i])
            );
        end
    endgenerate

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            norm_check_done <= 'b0;
        else if (zeroize)
            norm_check_done <= 'b0;
        else
            norm_check_done <= norm_check_done_int;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if  (!reset_n) 
            invalid <= 'b0;
        else if (zeroize | norm_check_done) 
            invalid <= 'b0;
        else 
            invalid <= invalid | (|check_a_invalid);// |  (|check_b_invalid);
    end

    //Delay flops
    //Give one cycle for HLC to capture invalid flag
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)  begin
            norm_check_ready         <= 'b0;
            check_enable_reg         <= 'b0;
        end
        else if (zeroize)  begin
            norm_check_ready         <= 'b0;
            check_enable_reg         <= 'b0;
        end
        else  begin
            norm_check_ready         <= norm_check_done;
            check_enable_reg         <= check_enable;
        end

    end

    norm_check_ctrl
    norm_check_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .norm_check_enable(norm_check_enable),
        .randomness(randomness),
        .mode(mode),
        .mem_base_addr(mem_base_addr),
        .mem_rd_req(mem_rd_req),
        .norm_check_done(norm_check_done_int),
        .check_enable(check_enable)
    );


endmodule