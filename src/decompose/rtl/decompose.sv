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
// decompose.sv
// --------
// Breaks down r coefficient into high and low bits such that
// r = r1*(2*GAMMA2) + r0 mod q where
// r0 is between -GAMMA2 and +GAMMA2. For a corner case where 
// r-r0 = q-1, r1 is made 0 and r0 is reduced by 1 i.e.,
// r0 = r0 - 1 == r mod q (See HW spec for more details)
// Decompose unit also optimizes makehint arch by generating a bit that
// computes z = (r1 != 0) check and directly stores the result in a buffer.
// Makehint is able to read the buffer during hint gen and receives 4 bits per 4 coeff per cycle

// Output of mod_2gamma2 goes through further calc to compute r0 mod+- (2gamma2) mod q. This is the
// final r0 output to be stored in memory.

// Decompose unit produces 3 outputs:
// 1. r0 --> store in memory
// 2. r1 --> pass to sample inball/hash interface
// 3. z_neq_z -->  store in a buffer that is ready by makehint simultaneously when it reads main mem

module decompose 
    import ntt_defines_pkg::*; //TODO: move all global params to config defines/ABR pkg?
    import decompose_defines_pkg::*;
    #(
        parameter DILITHIUM_Q = 23'd8380417,
        parameter GAMMA2 = (DILITHIUM_Q-1)/32,
        parameter Q_MINUS_2GAMMA2 = DILITHIUM_Q - (2*GAMMA2),
        parameter MEM_ADDR_WIDTH = 15
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire decompose_enable,
        input dcmp_mode_t dcmp_mode,
        input wire [MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [MEM_ADDR_WIDTH-1:0] hint_src_base_addr,

        //Input from keccak to w1_encode
        input wire keccak_done,

        //Output to memory - r0
        output mem_if_t mem_rd_req,
        output mem_if_t mem_wr_req,
        input wire [(4*REG_SIZE)-1:0] mem_rd_data,
        output logic [(4*REG_SIZE)-1:0] mem_wr_data,

        //Output to memory - h (sigDecode)
        output mem_if_t mem_hint_rd_req,
        input wire [(4*REG_SIZE)-1:0] mem_hint_rd_data,

        //Output to z mem - z != 0
        output mem_if_t z_mem_wr_req,
        output logic [3:0] z_neq_z,

        //Output of w1_encode - r1
        output logic [63:0] w1_o,
        output logic buffer_en,
        output logic keccak_en, //TODO: need to delay by 1 cycle?

        //TODO: check what high level controller requirement is
        output logic decompose_done,
        output logic w1_encode_done

        
    );

    //Coefficient wires
    logic [3:0][3:0] r1, r1_reg, r1_usehint, r1_mux;
    logic [3:0] r_corner, r_corner_reg;
    logic [3:0][19:0] r0_mod_2gamma2;
    logic [3:0][REG_SIZE-2:0] r0_mod_q, r0, r0_reg; //23-bit value
    logic [(4*REG_SIZE)-1:0] mem_rd_data_reg, mem_hint_rd_data_reg;
    mem_if_t mem_wr_req_int;

    //Control wires
    logic mod_enable, enable_reg, enable_d2;
    logic [3:0] mod_ready;
    logic verify;
    logic [3:0] usehint_ready;

    always_comb verify = (dcmp_mode == verify_op);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            enable_reg <= 'b0;
            enable_d2  <= 'b0;
        end
        else if (zeroize) begin
            enable_reg <= 'b0;
            enable_d2  <= 'b0;
        end
        else begin
            enable_reg <= mod_enable;
            enable_d2  <= enable_reg;
        end
    end

    decompose_ctrl
    #(
        .MEM_ADDR_WIDTH(MEM_ADDR_WIDTH)
    )
    dcmp_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .decompose_enable(decompose_enable),
        .src_base_addr(src_base_addr),
        .dest_base_addr(dest_base_addr),
        .r0_ready(&mod_ready), //all redux units must be ready at the same time
        .mem_rd_req(mem_rd_req),
        .mem_wr_req(mem_wr_req_int), //TODO: flop?
        .mod_enable(mod_enable),
        .decompose_done(decompose_done)
    );

    generate
        for (genvar i = 0; i < 4; i++) begin
            decompose_r1_lut #(
                .REG_SIZE(REG_SIZE-1)
            ) 
            r1_lut_inst (
                .r(mem_rd_data[(REG_SIZE-2)+(i*REG_SIZE):i*REG_SIZE]),
                .r1(r1[i]),
                .r_corner(r_corner[i]),
                .z_nez(z_neq_z[i])
            );
        end
    endgenerate

    generate
        for(genvar i = 0; i < 4; i++) begin
            decompose_mod_2gamma2 #(
                .REG_SIZE(REG_SIZE-1)
            )
            dcmp_redux_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .add_en_i(enable_reg),
                .opa_i(mem_rd_data[(REG_SIZE-2)+(i*REG_SIZE):i*REG_SIZE]),
                .res_o(r0_mod_2gamma2[i]),
                .ready_o(mod_ready[i])
            );
        end
    endgenerate

    generate
        for (genvar i = 0; i < 4; i++) begin
            always_comb begin
                r0_mod_q[i] = (r0_mod_2gamma2[i] <= GAMMA2) ? {3'b000, r0_mod_2gamma2[i]} : r0_mod_2gamma2[i] + Q_MINUS_2GAMMA2;
            end
        end
    endgenerate

    //Delay flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            r_corner_reg         <= 'h0;
            mem_rd_data_reg      <= 'h0;
            r0_reg               <= 'h0;
            r1_reg               <= 'h0;
            mem_hint_rd_data_reg <= 'h0;
        end
        else if (zeroize) begin
            r_corner_reg         <= 'h0;
            mem_rd_data_reg      <= 'h0;
            r0_reg               <= 'h0;
            r1_reg               <= 'h0;
            mem_hint_rd_data_reg <= 'h0;
        end
        else begin
            r_corner_reg         <= r_corner;
            mem_rd_data_reg      <= mem_rd_data;
            r0_reg               <= r0;
            r1_reg               <= r1;
            mem_hint_rd_data_reg <= mem_hint_rd_data;
        end
    end

    generate
        for (genvar i = 0; i < 4; i++) begin
            always_comb begin
                r0[i] = r_corner_reg[i] ? mem_rd_data_reg[i*REG_SIZE+(REG_SIZE-1):i*REG_SIZE] : r0_mod_q[i];
                mem_wr_data[i*REG_SIZE+(REG_SIZE-1):i*REG_SIZE] = verify ? 'h0 : {1'b0, r0_reg[i]};
            end
        end
    endgenerate

    generate
        for (genvar i = 0; i < 4; i++) begin
            decompose_usehint #(
                .REG_SIZE(REG_SIZE-1)
            )
            usehint_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .usehint_enable(enable_d2),
                .w0_i(r0[i]),
                .w1_i(r1_reg[i]),
                .hint_i(mem_hint_rd_data_reg[i*REG_SIZE]), //LSB is the hint, rest are 0s
                .w1_o(r1_usehint[i]),
                .ready_o(usehint_ready[i])
                
            );
        end
    endgenerate

    always_comb begin
        z_mem_wr_req.rd_wr_en    = verify ? RW_IDLE : mem_wr_req_int.rd_wr_en;
        z_mem_wr_req.addr        = verify ? 'h0 : mem_wr_req_int.addr - dest_base_addr;
        r1_mux                   = verify & (&usehint_ready) ? r1_usehint : r1_reg;

        mem_wr_req.addr          = verify ? 'h0 : mem_wr_req_int.addr;
        mem_wr_req.rd_wr_en      = verify ? RW_IDLE : mem_wr_req_int.rd_wr_en;

        mem_hint_rd_req.addr     = verify ? (mem_rd_req.addr - src_base_addr + hint_src_base_addr) : 'h0;
        mem_hint_rd_req.rd_wr_en = verify ? mem_rd_req.rd_wr_en : RW_IDLE;
    end

    //w1 Encode
    decompose_w1_encode w1_enc_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .w1_encode_enable(verify ? &usehint_ready : &mod_ready),
        .r1_i(r1_mux),
        .w1_o(w1_o),
        .buffer_en(buffer_en),
        .keccak_en(keccak_en),
        .keccak_done(keccak_done),
        .w1_encode_done(w1_encode_done)
    );
    
endmodule
