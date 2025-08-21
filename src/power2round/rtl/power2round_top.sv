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
// power2round_top.sv
// --------
//======================================================================

module power2round_top
    import abr_params_pkg::*;
    #(
        parameter REG_SIZE = 24,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_N = 256,
        parameter MLDSA_K = 8,
        parameter MLDSA_D = 13,
        parameter AHB_DATA_WIDTH = 32
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] skmem_dest_base_addr, //skmem API base addr - TODO: finalize size
        // input wire [ABR_MEM_ADDR_WIDTH-1:0] pk_dest_base_addr, //reg API base addr - TODO: finalize size

        //Input from internal memory
        output mem_if_t mem_a_rd_req,
        output mem_if_t mem_b_rd_req,
        input wire [(4*REG_SIZE)-1:0] mem_rd_data_a,
        input wire [(4*REG_SIZE)-1:0] mem_rd_data_b,
        //input wire mem_rd_data_valid,  // TODO: 

        //output to sk mem
        output mem_if_t skmem_a_wr_req,
        output mem_if_t skmem_b_wr_req,
        output logic [AHB_DATA_WIDTH-1:0] skmem_wr_data_a,
        output logic [AHB_DATA_WIDTH-1:0] skmem_wr_data_b,

        output logic pk_t1_wren,
        output logic [7:0][9:0] pk_t1_wrdata, // TODO: change to parameter
        output logic [7:0] pk_t1_wr_addr, // TODO: change to parameter

        output logic done
    );


    logic [7:0][REG_SIZE-1:0] mem_data_reg;
    logic [7:0][MLDSA_D-1:0] r0, r0_packed, r0_packed_reg;
    logic [7:0][REG_SIZE-MLDSA_D-2:0] r1, r1_reg;

    logic sk_buff_full;
    logic mem_data_reg_valid, r_valid;
    logic mem_rd_data_valid;

    logic sk_buff_enable;
    logic sk_buff_valid;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            mem_rd_data_valid <= 'h0;
        else if (zeroize)
            mem_rd_data_valid <= 'h0;
        else
            mem_rd_data_valid <= (mem_a_rd_req.rd_wr_en == RW_READ); //assuming data is valid 1 cycle after read request
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_data_reg <= 'h0;
            mem_data_reg_valid <= 'h0;
        end
        else if (zeroize) begin
            mem_data_reg <= 'h0;
            mem_data_reg_valid <= 'h0;
        end
        else if (~sk_buff_full) begin
            {mem_data_reg[3], mem_data_reg[2], mem_data_reg[1], mem_data_reg[0]} <= mem_rd_data_a;
            {mem_data_reg[7], mem_data_reg[6], mem_data_reg[5], mem_data_reg[4]} <= mem_rd_data_b;
            mem_data_reg_valid <= mem_rd_data_valid;
        end
    end

    generate
        for (genvar i = 0; i < 8; i++) begin : gen_r0_r1
            power2round_core #(
                .REG_SIZE(REG_SIZE-1),
                .MLDSA_Q(MLDSA_Q),
                .MLDSA_D(MLDSA_D)
            ) 
            power2round_core_inst (
                .r(mem_data_reg[i][REG_SIZE-2:0]),
                .r0(r0[i]),
                .r1(r1[i])
            );
        end
    endgenerate


    generate
        for (genvar i = 0; i < 8; i++) begin : gen_r0_packed
            power2round_skencode #(
                .REG_SIZE(REG_SIZE-1),
                .MLDSA_Q(MLDSA_Q),
                .MLDSA_D(MLDSA_D)
            ) 
            power2round_skencode_inst (
                .r0(r0[i]),
                .r0_packed(r0_packed[i])
            );
        end
    endgenerate

    generate
        for (genvar i = 0; i < 8; i++) begin
            always_ff @(posedge clk or negedge reset_n) begin
                if (!reset_n) begin
                    r0_packed_reg[i] <= 'h0;
                    r1_reg[i] <= 'h0;
                end
                else if (zeroize) begin
                    r0_packed_reg[i] <= 'h0;
                    r1_reg[i] <= 'h0;
                end
                else if (~sk_buff_full) begin
                    r0_packed_reg[i] <= r0_packed[i];
                    r1_reg[i] <= r1[i];
                end
            end
        end
    endgenerate

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) 
            r_valid <= 'h0;
        else if (zeroize)
            r_valid <= 'h0;
        else if (~sk_buff_full)
            r_valid <= mem_data_reg_valid;
    end

    generate
        for (genvar i = 0; i < 8; i++) begin
            always_comb begin
                pk_t1_wrdata[i] = r1_reg[i];
            end
        end
    endgenerate
    

    abr_sample_buffer #(
        .NUM_WR(13),
        .NUM_RD(8),
        .BUFFER_DATA_W(8)
    )
    sk_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_valid_i({13{sk_buff_enable}}),
        .data_i(r0_packed_reg),
        .buffer_full_o(sk_buff_full),
        .data_valid_o(sk_buff_valid),
        .data_o({skmem_wr_data_b, skmem_wr_data_a})
    );


    power2round_ctrl #(
        .MLDSA_K(MLDSA_K),
        .MLDSA_N(MLDSA_N)
    )
    power2round_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .enable(enable),
        .src_base_addr(src_base_addr),
        .skmem_dest_base_addr(skmem_dest_base_addr),
        // .pk_dest_base_addr(pk_dest_base_addr),
        .r_valid(r_valid),
        .sk_buff_valid(sk_buff_valid),
        .sk_buff_full(|sk_buff_full),
        
        .mem_a_rd_req(mem_a_rd_req),
        .mem_b_rd_req(mem_b_rd_req),
        .skmem_a_wr_req(skmem_a_wr_req),
        .skmem_b_wr_req(skmem_b_wr_req),
        .pk_t1_wren(pk_t1_wren),
        .pk_t1_wr_addr(pk_t1_wr_addr),
        .sk_buff_enable(sk_buff_enable),
        .done(done)
    );

endmodule
