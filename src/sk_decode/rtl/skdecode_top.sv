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
// skdecode_top.sv
// --------
// 1. Decodes sk input from reg API into s1, s2 and t0 polynomials. 
// 2. Output coeffs are all in 24-bit format. 4 coeffs are written to memory per addr.
// 3. Dual writes take place per cycle, hence 8 values are processed per cycle fpr s1s2 unpack
// 4. One enable pulse from HLC will trigger all 3 polynomial decoding and control
//  is transferred back to HLC only after the last poly has been written to memory
// 5. Any invalid input in sk will trigger an error within skdecode and operation 
// is stopped. An error interrupt must be set (TODO: by HLC?) to notify RV core
// TODO: sk reg to skdecode interface. For now, assuming a mux. Can be shift reg?
// 6. Note, this module interfaces with a key memory to retrieve sk input. Since the memory
// interface is 32-bit data port, 8 s1s2 modules can be run in parallel to process 24-bits of data per cycle
// and 4 t0 unpack modules can be run in parallel to process 52-bits of data per cycle. t0 operation
// requires 2 memory reads per cycle and s1s2 requires 1 memory read
//======================================================================

module skdecode_top
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
    #(
        parameter MLDSA_ETA = 2,
        parameter MLDSA_D = 13,
        parameter ETA_SIZE = 3,
        parameter REG_SIZE = 24,
        parameter AHB_DATA_WIDTH = 32
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,
        
        input wire skdecode_enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] keymem_src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [AHB_DATA_WIDTH-1:0] keymem_a_rd_data,
        input wire [AHB_DATA_WIDTH-1:0] keymem_b_rd_data,

        output mem_if_t keymem_a_rd_req,
        output mem_if_t keymem_b_rd_req,
        output mem_if_t mem_a_wr_req,
        output mem_if_t mem_b_wr_req,
        output logic [3:0][REG_SIZE-1:0] mem_a_wr_data,
        output logic [3:0][REG_SIZE-1:0] mem_b_wr_data,
        output logic skdecode_error,
        output logic skdecode_done,
        output logic s1_done,
        output logic s2_done,
        output logic t0_done
    );

    logic s1s2_enable, t0_enable, s1s2_enable_reg, t0_enable_reg;
    logic s1s2_enable_reg_d2, t0_enable_reg_d2;
    logic [7:0] s1s2_valid;
    logic [3:0] t0_valid;
    logic [7:0] s1s2_error;
    logic [7:0][REG_SIZE-1:0] s1s2_data;
    logic [3:0][REG_SIZE-1:0] t0_data;
    logic t0_done_reg;

    //IO flops
    mem_if_t mem_a_wr_req_int, mem_b_wr_req_int, mem_a_wr_req_reg, mem_b_wr_req_reg;
    logic [7:0][ETA_SIZE-1:0] s1s2_buf_data;
    logic [3:0][MLDSA_D-1:0] t0_buf_data;
    logic [3:0][REG_SIZE-1:0] mem_a_wr_data_int, mem_b_wr_data_int, mem_a_wr_data_reg, mem_b_wr_data_reg;
    logic [AHB_DATA_WIDTH-1:0] keymem_a_rd_data_reg, keymem_b_rd_data_reg;

    logic s1s2_buf_stall, t0_buf_stall;
    logic t0_data_valid;
    logic s1s2_data_valid;
    logic t0_buf_full;
    logic s1s2_buf_stall_reg;
    logic s1s2_buf_full;

    logic s1s2_keymem_b_valid;

    //Read address counters
    logic [ABR_MEM_ADDR_WIDTH-1:0] keymem_rd_addr, keymem_rd_addr_nxt;


    //IO flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            s1s2_enable_reg             <= 'h0;
            t0_enable_reg               <= 'h0;
            s1s2_enable_reg_d2          <= 'h0;
            t0_enable_reg_d2            <= 'h0;
            mem_a_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_b_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_a_wr_req_reg.addr       <= 'h0;
            mem_b_wr_req_reg.addr       <= 'h0;
            mem_a_wr_data_reg           <= 'h0;
            mem_b_wr_data_reg           <= 'h0;
            t0_done_reg                 <= 'b0;
            s1s2_keymem_b_valid         <= 'b0;
        end
        else if (zeroize) begin
            s1s2_enable_reg             <= 'h0;
            t0_enable_reg               <= 'h0;
            s1s2_enable_reg_d2          <= 'h0;
            t0_enable_reg_d2            <= 'h0;
            mem_a_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_b_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_a_wr_req_reg.addr       <= 'h0;
            mem_b_wr_req_reg.addr       <= 'h0;
            mem_a_wr_data_reg           <= 'h0;
            mem_b_wr_data_reg           <= 'h0;
            t0_done_reg                 <= 'b0;
            s1s2_keymem_b_valid         <= 'b0;
        end
        else begin
            s1s2_enable_reg             <= s1s2_enable;
            t0_enable_reg               <= t0_enable;
            s1s2_enable_reg_d2          <= s1s2_enable_reg;
            t0_enable_reg_d2            <= t0_enable_reg;
            mem_a_wr_req_reg            <= mem_a_wr_req_int;
            mem_b_wr_req_reg            <= mem_b_wr_req_int;
            mem_a_wr_data_reg           <= mem_a_wr_data_int;
            mem_b_wr_data_reg           <= mem_b_wr_data_int;
            t0_done_reg                 <= t0_done;
            s1s2_keymem_b_valid         <= s1s2_enable & (keymem_b_rd_req.rd_wr_en == RW_READ);
        end
    end

    //Data flop with enable to sync with buf full
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            keymem_a_rd_data_reg <= 'h0;
            keymem_b_rd_data_reg <= 'h0;
        end
        else if (zeroize) begin
            keymem_a_rd_data_reg <= 'h0;
            keymem_b_rd_data_reg <= 'h0;
        end
        else if (~t0_buf_full & ~s1s2_buf_full) begin
            keymem_a_rd_data_reg <= s1s2_keymem_b_valid ? keymem_b_rd_data: keymem_a_rd_data;
            keymem_b_rd_data_reg <= keymem_b_rd_data;

        end
    end

    //Flags
    always_comb begin
        mem_a_wr_data_int  = |s1s2_valid ? s1s2_data[3:0] : |t0_valid ? t0_data[3:0] : 'h0;
        mem_b_wr_data_int  = |s1s2_valid ? s1s2_data[7:4] : |t0_valid ? t0_data[3:0] : 'h0;
        skdecode_error     = |s1s2_error;
    end

    //Assign outputs
    always_comb begin
        mem_a_wr_req = mem_a_wr_req_reg;
        mem_b_wr_req = mem_b_wr_req_reg;
        mem_a_wr_data = mem_a_wr_data_reg;
        mem_b_wr_data = mem_b_wr_data_reg;
    end

    //8 s1s2 unpack instances to process 3*8 = 24-bits per cycle. In this case, one addr of key mem is read per cycle
    generate
        for (genvar i = 0; i < 8; i++) begin : gen_s1s2_unpack
            skdecode_s1s2_unpack #(
                .REG_SIZE(REG_SIZE)
            )
            s1s2_unpack_inst (
                .data_i(s1s2_buf_data[i]),
                .enable(s1s2_data_valid), //from buffer
                .data_o(s1s2_data[i]),
                .valid_o(s1s2_valid[i]),
                .error_o(s1s2_error[i])
            );
        end
    endgenerate

    //4 t0 unpack instances to process 13*4 = 52-bits per cycle. This makes it simpler to interface with key mem that can provide
    //atmost 64-bits per cycle. Remaining bits are accumulated in buffer. in this case, 2 addr of key mem are read per cycle
    generate
        for (genvar i = 0; i < 4; i++) begin : gen_t0_unpack
            skdecode_t0_unpack #(
                .REG_SIZE(REG_SIZE-1)
            )
            t0_unpack_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .enable(t0_data_valid), //from buffer
                .sub_i('1),
                .data_i(t0_buf_data[i]),
                .data_o(t0_data[i]),
                .valid_o(t0_valid[i])
            );
        end
    endgenerate

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            s1s2_buf_stall_reg <= 'b0;
        else if (zeroize)
            s1s2_buf_stall_reg <= 'b0;
        else
            s1s2_buf_stall_reg <= s1s2_buf_stall;
    end

    always_comb begin
        t0_buf_stall = t0_buf_full; //(t0_buf_full & t0_enable_reg);
    end

    abr_sample_buffer #(
        .NUM_WR(16),
        .NUM_RD(13),
        .BUFFER_DATA_W(4)
    )
    t0_sample_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_valid_i((t0_buf_full | ~t0_enable) ? 16'h0 : {16{t0_enable_reg}}),
        .data_i({keymem_b_rd_data_reg, keymem_a_rd_data_reg}),
        .buffer_full_o(t0_buf_full),
        .data_valid_o(t0_data_valid),
        .data_o(t0_buf_data)
    );

    abr_sample_buffer #(
        .NUM_WR(4),
        .NUM_RD(3),
        .BUFFER_DATA_W(8)
    )
    s1s2_sample_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_valid_i(s1s2_buf_stall_reg/*(s1s2_buf_full | ~s1s2_enable)*/ ? 4'h0 : {4{s1s2_enable_reg}}),
        .data_i(keymem_a_rd_data_reg),
        .buffer_full_o(s1s2_buf_full),
        .data_valid_o(s1s2_data_valid),
        .data_o(s1s2_buf_data)
    );

    skdecode_ctrl
    skdecode_ctrl_inst (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .skdecode_enable(skdecode_enable),
        .src_base_addr(keymem_src_base_addr),
        .dest_base_addr(dest_base_addr),
        .s1s2_valid(|s1s2_valid),
        .t0_valid(|t0_valid),
        .s1s2_error(|s1s2_error), //TODO: enable later when tb is fixed to drive input values within range
        .t0_buf_stall(t0_buf_stall), //input from buffer to ctrl
        .mem_a_wr_req(mem_a_wr_req_int),
        .mem_b_wr_req(mem_b_wr_req_int),
        .kmem_a_rd_req(keymem_a_rd_req),
        .kmem_b_rd_req(keymem_b_rd_req),
        .s1s2_enable(s1s2_enable),
        .t0_enable(t0_enable),
        .skdecode_done(skdecode_done),
        .s1_done(s1_done),
        .s2_done(s2_done),
        .t0_done(t0_done),
        .s1s2_buf_stall(s1s2_buf_stall)//(s1s2_buf_full)
    );

endmodule