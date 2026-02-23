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
    (
        input logic clk,
        input logic reset_n,
        input logic zeroize,
        
        input logic skdecode_enable,
        input logic [ABR_MEM_ADDR_WIDTH-1:0] keymem_src_base_addr,
        input logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input logic [1:0][ABR_REG_WIDTH-1:0] keymem_rd_data,
        input logic [1:0] keymem_rd_data_valid,

        output mem_if_t [1:0] keymem_rd_req,
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

    logic s1s2_enable, t0_enable;
    logic [7:0] s1s2_valid;
    logic [3:0] t0_valid;
    logic s1s2_error;
    logic [7:0] s1s2_error_set;
    logic [7:0][REG_SIZE-1:0] s1s2_data;
    logic [3:0][REG_SIZE-1:0] t0_data;
    logic keymem_rd_data_valid_f;

    //IO flops
    mem_if_t mem_a_wr_req_int, mem_b_wr_req_int, mem_a_wr_req_reg, mem_b_wr_req_reg;
    logic [7:0][MLDSA_ETA_W-1:0] s1s2_buf_data;
    logic [3:0][MLDSA_D-1:0] t0_buf_data;
    logic [3:0][REG_SIZE-1:0] mem_a_wr_data_int, mem_b_wr_data_int, mem_a_wr_data_reg, mem_b_wr_data_reg;
    logic [1:0][ABR_REG_WIDTH-1:0] keymem_rd_data_reg;

    logic t0_data_valid;
    logic s1s2_data_valid;

    logic s1s2_keymem_b_valid;

    //IO flops
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_a_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_b_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_a_wr_req_reg.addr       <= '0;
            mem_b_wr_req_reg.addr       <= '0;
            mem_a_wr_data_reg           <= '0;
            mem_b_wr_data_reg           <= '0;
            keymem_rd_data_valid_f      <= '0;
        end
        else if (zeroize) begin
            mem_a_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_b_wr_req_reg.rd_wr_en   <= RW_IDLE;
            mem_a_wr_req_reg.addr       <= '0;
            mem_b_wr_req_reg.addr       <= '0;
            mem_a_wr_data_reg           <= '0;
            mem_b_wr_data_reg           <= '0;
            keymem_rd_data_valid_f      <= '0;
        end
        else begin
            mem_a_wr_req_reg            <= mem_a_wr_req_int;
            mem_b_wr_req_reg            <= mem_b_wr_req_int;
            mem_a_wr_data_reg           <= mem_a_wr_data_int;
            mem_b_wr_data_reg           <= mem_b_wr_data_int;
            keymem_rd_data_valid_f      <= (|keymem_rd_data_valid);
        end
    end

    always_comb s1s2_keymem_b_valid = s1s2_enable & keymem_rd_data_valid[1];

    //Data flop with enable to sync with buf full
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            keymem_rd_data_reg <= '0;
        end
        else if (zeroize) begin
            keymem_rd_data_reg <= '0;
        end
        else begin
            if (keymem_rd_data_valid[0] | s1s2_keymem_b_valid)
                keymem_rd_data_reg[0] <= s1s2_keymem_b_valid ? keymem_rd_data[1]: keymem_rd_data[0];
            if (keymem_rd_data_valid[1] & ~s1s2_enable)
                keymem_rd_data_reg[1] <= keymem_rd_data[1];
        end
    end

    //latch the error indication and assert to controller on done
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            s1s2_error <= '0;
        end
        else if (zeroize) begin
            s1s2_error <= '0;
        end
        else begin
            s1s2_error <= s1s2_error_set ? '1 : 
                          skdecode_done ? '0 : s1s2_error;
        end
    end

    //Flags
    always_comb begin
        mem_a_wr_data_int  = |s1s2_valid ? s1s2_data[3:0] : |t0_valid ? t0_data[3:0] : '0;
        mem_b_wr_data_int  = |s1s2_valid ? s1s2_data[7:4] : |t0_valid ? t0_data[3:0] : '0;
        skdecode_error     = s1s2_error & skdecode_done;
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
            skdecode_s1s2_unpack
            s1s2_unpack_inst (
                .data_i(s1s2_buf_data[i]),
                .enable(s1s2_data_valid), //from buffer
                .data_o(s1s2_data[i]),
                .valid_o(s1s2_valid[i]),
                .error_o(s1s2_error_set[i])
            );
        end
    endgenerate

    //4 t0 unpack instances to process 13*4 = 52-bits per cycle. This makes it simpler to interface with key mem that can provide
    //atmost 64-bits per cycle. Remaining bits are accumulated in buffer. in this case, 2 addr of key mem are read per cycle
    generate
        for (genvar i = 0; i < 4; i++) begin : gen_t0_unpack
            skdecode_t0_unpack
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

    abr_rd_lat_buffer #(
        .WR_WIDTH(64), //rate of sk reads
        .RD_WIDTH(52), //rate of sk mem writes
        .BUFFER_DEPTH(112) //worst case depth
    ) skdec_t0_rd_lat_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_i(keymem_rd_data_reg),
        .data_valid_i(keymem_rd_data_valid_f & t0_enable),
        .data_o(t0_buf_data),
        .data_valid_o(t0_data_valid)
    );

    abr_rd_lat_buffer #(
        .WR_WIDTH(32), //rate of sk reads
        .RD_WIDTH(24), //rate of sk mem writes
        .BUFFER_DEPTH(48) //worst case depth
    ) skdec_s1s2_rd_lat_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize),
        .data_i(keymem_rd_data_reg[0]),
        .data_valid_i(keymem_rd_data_valid_f & s1s2_enable),
        .data_o(s1s2_buf_data),
        .data_valid_o(s1s2_data_valid)
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
        .mem_a_wr_req(mem_a_wr_req_int),
        .mem_b_wr_req(mem_b_wr_req_int),
        .kmem_a_rd_req(keymem_rd_req[0]),
        .kmem_b_rd_req(keymem_rd_req[1]),
        .s1s2_enable(s1s2_enable),
        .t0_enable(t0_enable),
        .skdecode_done(skdecode_done),
        .s1_done(s1_done),
        .s2_done(s2_done),
        .t0_done(t0_done)
    );

endmodule