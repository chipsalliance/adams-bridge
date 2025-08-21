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

`include "abr_prim_assert.sv"

module decompose 
    import abr_params_pkg::*;
    import decompose_defines_pkg::*;
    #(
        parameter Q_MINUS_2GAMMA2 = MLDSA_Q - (2*MLDSA_GAMMA2)
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire decompose_enable,
        input dcmp_mode_t dcmp_mode,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] hint_src_base_addr,

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

        output logic decompose_done

        
    );

    //Coefficient wires
    logic [3:0][3:0] r1, r1_reg, r1_usehint, r1_mux;
    logic [3:0] r_corner, r_corner_reg;
    logic [3:0][18:0] r0_mod_2gamma2;
    logic [3:0][REG_SIZE-2:0] r0_mod_q, r0, r0_reg; //23-bit value
    logic [(4*REG_SIZE)-1:0] mem_rd_data_reg, mem_hint_rd_data_reg, mem_wr_data_int;
    mem_if_t mem_wr_req_int, mem_hint_rd_req_int, z_mem_wr_req_int;
    logic [3:0] z_neq_z_d1, z_neq_z_d2, z_neq_z_int, z_neq_z_mux;

    //Control wires
    logic mod_enable; 
    logic [1:0] enable_reg;
    logic [3:0] mod_ready;
    logic verify;
    logic [3:0] usehint_ready;

    always_comb verify = (dcmp_mode == verify_op);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            enable_reg <= 'b0;
            z_neq_z_d1 <= 'h0;
            z_neq_z_d2 <= 'h0;
        end
        else if (zeroize) begin
            enable_reg <= 'b0;
            z_neq_z_d1 <= 'h0;
            z_neq_z_d2 <= 'h0;
        end
        else begin
            enable_reg <= {mod_enable, enable_reg[1]};
            z_neq_z_d1 <= z_neq_z_int;
            z_neq_z_d2 <= z_neq_z_d1;
        end
    end

    decompose_ctrl
    dcmp_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .decompose_enable(decompose_enable),
        .src_base_addr(src_base_addr),
        .dest_base_addr(dest_base_addr),
        .r0_ready(&mod_ready), //all redux units must be ready at the same time
        .mem_rd_req(mem_rd_req),
        .mem_wr_req(mem_wr_req_int),
        .mod_enable(mod_enable),
        .decompose_done(decompose_done)
    );

    generate
        for (genvar i = 0; i < 4; i++) begin : gen_r1_lut
            decompose_r1_lut #(
                .REG_SIZE(REG_SIZE-1)
            ) 
            r1_lut_inst (
                .r(mem_rd_data[(REG_SIZE-2)+(i*REG_SIZE):i*REG_SIZE]),
                .r1(r1[i]),
                .r_corner(r_corner[i]),
                .z_nez(z_neq_z_int[i])
            );
        end
    endgenerate

    generate
        for(genvar i = 0; i < 4; i++) begin : gen_dcmp_redux
            decompose_mod_2gamma2 #(
                .REG_SIZE(REG_SIZE-1)
            )
            dcmp_redux_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .add_en_i(enable_reg[1]), //delayed by 1 clk
                .opa_i(mem_rd_data[(REG_SIZE-2)+(i*REG_SIZE):i*REG_SIZE]),
                .res_o(r0_mod_2gamma2[i]),
                .ready_o(mod_ready[i])
            );
        end
    endgenerate

    generate
        for (genvar i = 0; i < 4; i++) begin
            always_comb begin
                r0_mod_q[i] = (r0_mod_2gamma2[i] <= MLDSA_GAMMA2) ? {4'h0, r0_mod_2gamma2[i]} : (REG_SIZE-1)'(r0_mod_2gamma2[i] + Q_MINUS_2GAMMA2);
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
                r0[i] = r_corner_reg[i] ? mem_rd_data_reg[i*REG_SIZE+(REG_SIZE-2):i*REG_SIZE] : r0_mod_q[i];
                mem_wr_data_int[i*REG_SIZE+(REG_SIZE-1):i*REG_SIZE] = verify ? 'h0 : {1'b0, r0_reg[i]};
            end
        end
    endgenerate

    generate
        for (genvar i = 0; i < 4; i++) begin : gen_usehint
            decompose_usehint #(
                .REG_SIZE(REG_SIZE-1)
            )
            usehint_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .usehint_enable(verify & enable_reg[0]), //delayed by 2 clks to match addr input flops
                .w0_i(r0[i]),
                .w1_i(r1_reg[i]),
                .hint_i(mem_hint_rd_data_reg[i*REG_SIZE]), //LSB is the hint, rest are 0s
                .w1_o(r1_usehint[i]),
                .ready_o(usehint_ready[i])
                
            );
        end
    endgenerate

    always_comb begin
        z_neq_z_mux               = verify ? 'h0 : z_neq_z_d2;
        z_mem_wr_req_int.rd_wr_en = verify ? RW_IDLE : mem_wr_req_int.rd_wr_en;
        z_mem_wr_req_int.addr     = verify ? 'h0 : ABR_MEM_ADDR_WIDTH'(mem_wr_req_int.addr - dest_base_addr);
        r1_mux                    = verify & (&usehint_ready) ? r1_usehint : r1_reg;

        mem_hint_rd_req.addr     = verify ? ABR_MEM_ADDR_WIDTH'(mem_rd_req.addr - src_base_addr + hint_src_base_addr) : 'h0;
        mem_hint_rd_req.rd_wr_en = verify ? mem_rd_req.rd_wr_en : RW_IDLE;
    end

    //Output flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            z_mem_wr_req    <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_wr_req      <= '{rd_wr_en: RW_IDLE, addr: '0};

            z_neq_z         <= '0;
            mem_wr_data     <= '0;
        end
        else if (zeroize) begin
            z_mem_wr_req    <= '{rd_wr_en: RW_IDLE, addr: '0};
            mem_wr_req      <= '{rd_wr_en: RW_IDLE, addr: '0};

            z_neq_z         <= '0;
            mem_wr_data     <= '0;
        end
        else begin
            z_mem_wr_req        <= z_mem_wr_req_int;
            mem_wr_req.addr     <= verify ? 'h0 : mem_wr_req_int.addr;
            mem_wr_req.rd_wr_en <= verify ? RW_IDLE : mem_wr_req_int.rd_wr_en;

            z_neq_z             <= z_neq_z_mux;
            mem_wr_data         <= mem_wr_data_int;
        end
    end

    //w1 Encode
    decompose_w1_encode w1_enc_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .w1_encode_enable(verify ? &usehint_ready : &mod_ready),
        .r1_i(r1_mux),
        .w1_o(w1_o),
        .buffer_en(buffer_en)
    );
    

    `ABR_ASSERT_MUTEX(ASSERT_R0_CORNER_MUTEX, {r_corner[0], r1[0]}, clk, reset_n)
    `ABR_ASSERT_MUTEX(ASSERT_R1_CORNER_MUTEX, {r_corner[1], r1[1]}, clk, reset_n)
    `ABR_ASSERT_MUTEX(ASSERT_R2_CORNER_MUTEX, {r_corner[2], r1[2]}, clk, reset_n)
    `ABR_ASSERT_MUTEX(ASSERT_R3_CORNER_MUTEX, {r_corner[3], r1[3]}, clk, reset_n)
endmodule
