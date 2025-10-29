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
// power2round_ctrl.sv
// ---------------------

module power2round_ctrl
    import abr_params_pkg::*;
    import power2round_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] skmem_dest_base_addr,
        input wire r_valid,
        input wire sk_buff_valid,

        output mem_if_t mem_a_rd_req,
        output mem_if_t mem_b_rd_req,
        output mem_if_t skmem_a_wr_req,
        output mem_if_t skmem_b_wr_req,
        output logic pk_t1_wren,
        output logic [7 : 0] pk_t1_wr_addr,   // K*N*10 / 8coeff_per_write  TODO: parameter=
        output logic done
    );

    localparam [ABR_MEM_ADDR_WIDTH-1 : 0] MAX_MEM_ADDR = (MLDSA_K * (MLDSA_N/4))-2;
    localparam [ABR_MEM_ADDR_WIDTH-1 : 0] MAX_SKMEM_ADDR = (MLDSA_K * (MLDSA_N/32) * 13)-2;
    localparam [7 : 0] MAX_PK_ADDR = ((MLDSA_K * (MLDSA_N/8))-1);

    power2round_read_state_type read_fsm_state_ps, read_fsm_state_ns;
    power2round_sk_write_state_type sk_write_fsm_state_ps, sk_write_fsm_state_ns;
    power2round_pk_write_state_type pk_write_fsm_state_ps, pk_write_fsm_state_ns;

    
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, mem_rd_addr_nxt, mem_rd_addr_delay, mem_rd_addr_tmp;
    logic [ABR_MEM_ADDR_WIDTH-1:0] skmem_wr_addr, skmem_wr_addr_nxt;
    logic [7 : 0] pk_wr_addr, pk_wr_addr_nxt;
    
    logic rst_mem_rd_addr, incr_mem_rd_addr, last_mem_rd_addr;
    logic rst_skmem_wr_addr, incr_rskmem_wr_addr, last_skmem_wr_addr;
    logic rst_pk_wr_addr, incr_pk_wr_addr, last_pk_wr_addr;

    logic pk_t1_wren_tmp;
    logic [12:0] mem_rd_pace;

    //addr counter
    always_comb mem_rd_addr_nxt = mem_rd_addr + 'h2;
    always_comb skmem_wr_addr_nxt = skmem_wr_addr + 'h2;
    always_comb pk_wr_addr_nxt = pk_wr_addr + 'h1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_addr <= '0;
            mem_rd_addr_delay <= '0;
            skmem_wr_addr <= '0; 
            pk_wr_addr <= '0;
        end
        else if (zeroize) begin
            mem_rd_addr <= '0;
            mem_rd_addr_delay <= '0;
            skmem_wr_addr <= '0;
            pk_wr_addr <= '0;
        end
        else begin
            if (rst_mem_rd_addr)
                mem_rd_addr <= src_base_addr;
            else if (incr_mem_rd_addr & ~last_mem_rd_addr)
                mem_rd_addr <= mem_rd_addr_nxt;
            
            mem_rd_addr_delay <= mem_rd_addr;

            if (rst_skmem_wr_addr)
                skmem_wr_addr <= skmem_dest_base_addr;
            else if (incr_rskmem_wr_addr & ~last_skmem_wr_addr)
                skmem_wr_addr <= skmem_wr_addr_nxt;
            
            if (rst_pk_wr_addr)
                pk_wr_addr <= '0;
            else if (incr_pk_wr_addr & ~last_pk_wr_addr)
                pk_wr_addr <= pk_wr_addr_nxt;
        end
    end

    assign last_mem_rd_addr = (mem_rd_addr == src_base_addr + MAX_MEM_ADDR);
    assign last_skmem_wr_addr = (skmem_wr_addr == skmem_dest_base_addr + MAX_SKMEM_ADDR);
    assign last_pk_wr_addr = (pk_wr_addr == MAX_PK_ADDR);

    // READ FSM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= T_RD_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= T_RD_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    // Pace the memory reads to never overflow the buffer
    // Ensures that buffer is always supplied
    // Rotate the pacer each clock we are reading
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            mem_rd_pace <= 13'b0101101011011;
        else if (zeroize)
            mem_rd_pace <= 13'b0101101011011;
        else if (read_fsm_state_ps == T_RD_MEM)
            mem_rd_pace <= {mem_rd_pace[0], mem_rd_pace[12:1]};
    end

    always_comb begin
        rst_mem_rd_addr = 0;
        incr_mem_rd_addr = 0;

        case(read_fsm_state_ps)
            T_RD_IDLE: begin
                read_fsm_state_ns = enable?  T_RD_MEM : T_RD_IDLE;
                rst_mem_rd_addr = 1;
            end
            T_RD_MEM: begin
                read_fsm_state_ns = last_mem_rd_addr ? T_RD_DONE : T_RD_MEM;
                incr_mem_rd_addr = mem_rd_pace[0];
            end
            T_RD_DONE: begin
                read_fsm_state_ns = T_RD_IDLE;
            end
            default: read_fsm_state_ns = T_RD_IDLE;
        endcase
    end

    // SK MEM WRITE FSM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            sk_write_fsm_state_ps <= SK_WR_IDLE;
        else if (zeroize)
            sk_write_fsm_state_ps <= SK_WR_IDLE;
        else
            sk_write_fsm_state_ps <= sk_write_fsm_state_ns;
    end

    always_comb begin
        rst_skmem_wr_addr = 0;
        incr_rskmem_wr_addr = 0;

        case(sk_write_fsm_state_ps)
            SK_WR_IDLE: begin
                sk_write_fsm_state_ns = (read_fsm_state_ps == T_RD_IDLE)? SK_WR_IDLE : SK_WR_WAIT;
                rst_skmem_wr_addr = 1;
            end
            SK_WR_WAIT: begin
                sk_write_fsm_state_ns = SK_WR_MEM;
            end
            SK_WR_MEM: begin
                sk_write_fsm_state_ns = last_skmem_wr_addr? SK_WR_DONE : SK_WR_MEM;
                incr_rskmem_wr_addr = sk_buff_valid;
            end
            SK_WR_DONE: begin
                sk_write_fsm_state_ns = SK_WR_IDLE;
            end
            default: sk_write_fsm_state_ns = SK_WR_IDLE;
        endcase
    end


    // PK WRITE FSM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            pk_write_fsm_state_ps <= PK_WR_IDLE;
        else if (zeroize)
            pk_write_fsm_state_ps <= PK_WR_IDLE;
        else
            pk_write_fsm_state_ps <= pk_write_fsm_state_ns;
    end

    always_comb begin
        rst_pk_wr_addr = 0;
        incr_pk_wr_addr = 0;

        case(pk_write_fsm_state_ps)
            PK_WR_IDLE: begin
                pk_write_fsm_state_ns = (read_fsm_state_ps == T_RD_IDLE)? PK_WR_IDLE : PK_WR_API;
                rst_pk_wr_addr = 1;
            end
            PK_WR_API: begin
                pk_write_fsm_state_ns = (last_pk_wr_addr & pk_t1_wren_tmp)? PK_WR_DONE : PK_WR_API;
                incr_pk_wr_addr = r_valid;
            end
            PK_WR_DONE: begin
                pk_write_fsm_state_ns = PK_WR_IDLE;
            end
            default: pk_write_fsm_state_ns = PK_WR_IDLE;
        endcase
    end

    always_comb mem_rd_addr_tmp = mem_rd_addr;

    always_comb begin
        mem_a_rd_req.rd_wr_en = (read_fsm_state_ps != T_RD_IDLE) & mem_rd_pace[0] ? RW_READ : RW_IDLE;
        mem_a_rd_req.addr = {mem_rd_addr[13:1],1'b0};

        mem_b_rd_req.rd_wr_en = (read_fsm_state_ps != T_RD_IDLE) & mem_rd_pace[0]  ? RW_READ : RW_IDLE;
        mem_b_rd_req.addr = {mem_rd_addr[13:1],1'b1};

        skmem_a_wr_req.rd_wr_en = ((sk_write_fsm_state_ps == SK_WR_MEM) & sk_buff_valid) ? RW_WRITE : RW_IDLE;
        skmem_a_wr_req.addr = {skmem_wr_addr[13:1],1'b0};

        skmem_b_wr_req.rd_wr_en = ((sk_write_fsm_state_ps == SK_WR_MEM) & sk_buff_valid) ? RW_WRITE : RW_IDLE;
        skmem_b_wr_req.addr = {skmem_wr_addr[13:1],1'b1};

        pk_t1_wren_tmp = (pk_write_fsm_state_ps == PK_WR_API) ? r_valid : '0;
        pk_t1_wr_addr = pk_wr_addr;

    end

    assign pk_t1_wren = pk_t1_wren_tmp;
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            done <= '0;
        else if (zeroize)
            done <= '0;
        else
            done <= (sk_write_fsm_state_ps == SK_WR_DONE);
    end

endmodule