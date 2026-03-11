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
// skdecode_ctrl.sv
// ---------------------
// Enables unpack modules and keeps track of memory writes

module skdecode_ctrl
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
    #(
        parameter MLDSA_L = 7,
        parameter MLDSA_K = 8,
        parameter MLDSA_N = 256
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire skdecode_enable, //One enable for all of s0, s1, t0 unpack
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire s1s2_valid,
        input wire t0_valid,

        output mem_if_t mem_a_wr_req,
        output mem_if_t mem_b_wr_req,
        output mem_if_t kmem_a_rd_req,
        output mem_if_t kmem_b_rd_req, 
        output logic s1s2_enable,
        output logic t0_enable,
        output logic skdecode_done,
        output logic s1_done,
        output logic s2_done,
        output logic t0_done
    );

    //Memory interface wires
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr, mem_wr_addr_nxt, mem_offset;
    logic [ABR_MEM_ADDR_WIDTH-1:0] kmem_rd_addr, kmem_rd_addr_nxt;

    logic incr_wr_addr, incr_skdec_count;
    logic rst_wr_addr, rst_skdec_count;
    logic incr_rd_addr, rst_rd_addr;
    logic last_poly_last_addr;
    logic skdecode_busy;
    logic [3:0] num_poly, num_inst;
    mem_rw_mode_e mem_rw_mode, kmem_a_rw_mode;
    mem_rw_mode_e kmem_b_rw_mode;
    logic [8:0] skdecode_count;
    logic [3:0] poly_count;
    logic s1s2_enable_fsm, t0_enable_fsm;
    logic s1_mode, s2_mode, t0_mode;

    skdec_read_state_e  read_fsm_state_ps, read_fsm_state_ns;
    skdec_write_state_e write_fsm_state_ps, write_fsm_state_ns;

    //Write FSM arcs
    logic arc_SKDEC_WR_IDLE_SKDEC_WR_S1;
    logic arc_SKDEC_WR_S1_SKDEC_WR_STAGE;
    logic arc_SKDEC_WR_S2_SKDEC_WR_STAGE;
    logic arc_SKDEC_WR_T0_SKDEC_WR_STAGE;
    logic arc_SKDEC_WR_STAGE_SKDEC_WR_S2;
    logic arc_SKDEC_WR_STAGE_SKDEC_WR_T0;
    logic arc_SKDEC_WR_STAGE_SKDEC_WR_IDLE;

    //Read FSM arcs
    logic arc_SKDEC_RD_IDLE_SKDEC_RD_S1;
    logic arc_SKDEC_RD_S1_SKDEC_RD_S2;
    logic arc_SKDEC_RD_S2_SKDEC_RD_T0;
    logic arc_SKDEC_RD_T0_SKDEC_RD_IDLE;

    //skdecode counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            skdecode_count <= '0;
        else if (zeroize)
            skdecode_count <= '0;
        else if (rst_skdec_count)
            skdecode_count <= '0;
        else if (incr_skdec_count) begin
            skdecode_count <= (skdecode_count == ((num_poly * MLDSA_N)/num_inst)-1) ? '0 : skdecode_count + 1'b1;
        end
    end

    logic [15:0] mem_rd_pace;

    // Pace the memory reads to never overflow the buffer
    // Ensures that buffer is always supplied
    // Rotate the pacer each clock we are reading
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            mem_rd_pace <= '0;
        else if (zeroize)
            mem_rd_pace <= '0;
        //S1S2 pace
        else if (arc_SKDEC_RD_IDLE_SKDEC_RD_S1 | arc_SKDEC_RD_S1_SKDEC_RD_S2) begin
            mem_rd_pace <= 16'b0111011101110111;
        end
        else if (arc_SKDEC_RD_S2_SKDEC_RD_T0) begin
            mem_rd_pace <= 16'b0111101111011111;
        end
        else if (read_fsm_state_ps != SKDEC_RD_IDLE)
            mem_rd_pace <= {mem_rd_pace[0], mem_rd_pace[15:1]};
    end

    //Write addr counter
    always_comb mem_wr_addr_nxt = (s1_mode | s2_mode) ? (mem_wr_addr + 2) : (mem_wr_addr + 1);

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            mem_wr_addr <= '0;
        else if (zeroize)
            mem_wr_addr <= '0;
        else if (skdecode_enable)
            mem_wr_addr <= dest_base_addr;
        else if (arc_SKDEC_WR_STAGE_SKDEC_WR_T0)
            mem_wr_addr <= mem_a_wr_req.addr; //Latch the last addr written, so we can continue from there for T0 poly //TODO revisit
        else if (incr_wr_addr)
            mem_wr_addr <= mem_wr_addr_nxt;
    end

    //Read addr counter
    always_comb kmem_rd_addr_nxt = t0_enable_fsm ? kmem_rd_addr + 'h2 : kmem_rd_addr + 1'b1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            kmem_rd_addr <= '0;
        else if (zeroize)
            kmem_rd_addr <= '0;
        else if (skdecode_enable)
            kmem_rd_addr <= src_base_addr;
        else if (incr_rd_addr)
            kmem_rd_addr <= kmem_rd_addr_nxt;
    end

    //Flags
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            s1_mode <= 1'b0;
            s2_mode <= 1'b0;
            t0_mode <= 1'b0;
        end
        else if (zeroize) begin
            s1_mode <= 1'b0;
            s2_mode <= 1'b0;
            t0_mode <= 1'b0;
        end
        else begin
            if (arc_SKDEC_WR_IDLE_SKDEC_WR_S1) s1_mode <= 1'b1;
            else if (arc_SKDEC_WR_STAGE_SKDEC_WR_S2) s1_mode <= 1'b0;

            if (arc_SKDEC_WR_STAGE_SKDEC_WR_S2) s2_mode <= 1'b1;
            else if (arc_SKDEC_WR_STAGE_SKDEC_WR_T0) s2_mode <= 1'b0;

            if (arc_SKDEC_WR_STAGE_SKDEC_WR_T0) t0_mode <= 1'b1;
            else if (arc_SKDEC_WR_STAGE_SKDEC_WR_IDLE) t0_mode <= 1'b0;
        end
    end

    always_comb begin
        //write fsm lags behind read fsm, so calculate flags using write states
        skdecode_busy       = (write_fsm_state_ps != SKDEC_WR_IDLE);
        skdecode_done       = (write_fsm_state_ps == SKDEC_WR_IDLE);
        //last addr flag only used in read
        last_poly_last_addr = (skdecode_count == (((num_poly * MLDSA_N)/num_inst)-1));
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            s1_done <= 1'b0;
            s2_done <= 1'b0;
            t0_done <= 1'b0;
        end
        else if (zeroize) begin
            s1_done <= 1'b0;
            s2_done <= 1'b0;
            t0_done <= 1'b0;
        end
        else begin
            if (arc_SKDEC_WR_S1_SKDEC_WR_STAGE)
                s1_done <= 1'b1;
            if (arc_SKDEC_WR_S2_SKDEC_WR_STAGE)
                s2_done <= 1'b1;
            if (arc_SKDEC_WR_T0_SKDEC_WR_STAGE)
                t0_done <= 1'b1;
        end
    end

    //---------------------------------
    //Read fsm
    //---------------------------------
    always_comb begin
        arc_SKDEC_RD_IDLE_SKDEC_RD_S1  = (read_fsm_state_ps == SKDEC_RD_IDLE) & skdecode_enable;
        arc_SKDEC_RD_S1_SKDEC_RD_S2 = (read_fsm_state_ps == SKDEC_RD_S1) & last_poly_last_addr & s1_done & ~s2_done & ~t0_done;
        arc_SKDEC_RD_S2_SKDEC_RD_T0 = (read_fsm_state_ps == SKDEC_RD_S2) & last_poly_last_addr & s1_done & s2_done & ~t0_done;
        arc_SKDEC_RD_T0_SKDEC_RD_IDLE = (read_fsm_state_ps == SKDEC_RD_T0) & last_poly_last_addr & s1_done & s2_done & t0_done;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= SKDEC_RD_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= SKDEC_RD_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    always_comb begin
        read_fsm_state_ns   = read_fsm_state_ps;
        incr_rd_addr        = 1'b0;
        rst_rd_addr         = 1'b0;
        kmem_a_rw_mode      = RW_IDLE;
        kmem_b_rw_mode      = RW_IDLE;
        incr_skdec_count    = 1'b0;
        rst_skdec_count     = 1'b0;
        s1s2_enable_fsm     = 1'b0;
        t0_enable_fsm       = 1'b0;
        num_poly            = MLDSA_L;
        num_inst            = 4'd8;

        unique case(read_fsm_state_ps)
            SKDEC_RD_IDLE: begin
                read_fsm_state_ns   = arc_SKDEC_RD_IDLE_SKDEC_RD_S1 ? SKDEC_RD_S1 : SKDEC_RD_IDLE;
                rst_rd_addr         = 1'b1;
                rst_skdec_count     = 1'b1;
            end
            SKDEC_RD_S1: begin
                read_fsm_state_ns   = arc_SKDEC_RD_S1_SKDEC_RD_S2 ? SKDEC_RD_S2 : SKDEC_RD_S1;
                incr_rd_addr        = ~last_poly_last_addr & mem_rd_pace[0];
                kmem_a_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] & ~kmem_rd_addr[0] ? RW_READ : RW_IDLE;
                kmem_b_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] &  kmem_rd_addr[0] ? RW_READ : RW_IDLE;
                incr_skdec_count    = ~last_poly_last_addr;
                s1s2_enable_fsm     = 1'b1;
                num_poly            = MLDSA_L;
                num_inst            = 4'd8;
                rst_skdec_count     = arc_SKDEC_RD_S1_SKDEC_RD_S2;
            end
            SKDEC_RD_S2: begin
                read_fsm_state_ns   = arc_SKDEC_RD_S2_SKDEC_RD_T0 ? SKDEC_RD_T0 : SKDEC_RD_S2;
                incr_rd_addr        = ~last_poly_last_addr & mem_rd_pace[0];
                kmem_a_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] & ~kmem_rd_addr[0] ? RW_READ : RW_IDLE;
                kmem_b_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] &  kmem_rd_addr[0] ? RW_READ : RW_IDLE;
                incr_skdec_count    = ~last_poly_last_addr;
                s1s2_enable_fsm     = 1'b1;
                num_poly            = MLDSA_K;
                num_inst            = 4'd8;
                rst_skdec_count     = arc_SKDEC_RD_S2_SKDEC_RD_T0;
            end
            SKDEC_RD_T0: begin
                read_fsm_state_ns   = arc_SKDEC_RD_T0_SKDEC_RD_IDLE ? SKDEC_RD_IDLE : SKDEC_RD_T0;
                incr_rd_addr        = ~last_poly_last_addr & mem_rd_pace[0];
                kmem_a_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] ? RW_READ : RW_IDLE;
                kmem_b_rw_mode      = ~last_poly_last_addr & mem_rd_pace[0] ? RW_READ : RW_IDLE;
                incr_skdec_count    = ~last_poly_last_addr;
                t0_enable_fsm       = 1'b1;
                num_poly            = MLDSA_K;
                num_inst            = 4'd4;
                rst_skdec_count     = arc_SKDEC_RD_T0_SKDEC_RD_IDLE;
            end
            default: begin
                read_fsm_state_ns = SKDEC_RD_IDLE;
            end
        endcase
    end

    //---------------------------------
    //Write fsm
    //---------------------------------
    always_comb begin
        //TODO add error conditions
        arc_SKDEC_WR_IDLE_SKDEC_WR_S1    = (write_fsm_state_ps == SKDEC_WR_IDLE) & skdecode_enable;
        arc_SKDEC_WR_S1_SKDEC_WR_STAGE   = (write_fsm_state_ps == SKDEC_WR_S1) & (read_fsm_state_ps == SKDEC_RD_S1) & last_poly_last_addr & !s1s2_valid;
        arc_SKDEC_WR_S2_SKDEC_WR_STAGE   = (write_fsm_state_ps == SKDEC_WR_S2) & (read_fsm_state_ps == SKDEC_RD_S2) & last_poly_last_addr & !s1s2_valid;
        arc_SKDEC_WR_T0_SKDEC_WR_STAGE   = (write_fsm_state_ps == SKDEC_WR_T0) & (read_fsm_state_ps == SKDEC_RD_T0) & last_poly_last_addr & !t0_valid;
        arc_SKDEC_WR_STAGE_SKDEC_WR_S2   = (write_fsm_state_ps == SKDEC_WR_STAGE) & s1_done & ~s2_done & ~t0_done;
        arc_SKDEC_WR_STAGE_SKDEC_WR_T0   = (write_fsm_state_ps == SKDEC_WR_STAGE) & s1_done & s2_done & ~t0_done;
        arc_SKDEC_WR_STAGE_SKDEC_WR_IDLE = (write_fsm_state_ps == SKDEC_WR_STAGE) & s1_done & s2_done & t0_done;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            write_fsm_state_ps <= SKDEC_WR_IDLE;
        else if (zeroize)
            write_fsm_state_ps <= SKDEC_WR_IDLE;
        else
            write_fsm_state_ps <= write_fsm_state_ns;
    end

    always_comb begin
        write_fsm_state_ns  = write_fsm_state_ps;
        incr_wr_addr        = 1'b0;
        rst_wr_addr         = 1'b0;
        mem_rw_mode         = RW_IDLE;

        unique case(write_fsm_state_ps)
            SKDEC_WR_IDLE: begin
                write_fsm_state_ns  = arc_SKDEC_WR_IDLE_SKDEC_WR_S1 ? SKDEC_WR_S1 : SKDEC_WR_IDLE;
                rst_wr_addr         = 1'b1;
            end
            SKDEC_WR_S1: begin
                write_fsm_state_ns  = arc_SKDEC_WR_S1_SKDEC_WR_STAGE ? SKDEC_WR_STAGE : SKDEC_WR_S1;
                incr_wr_addr        = s1s2_valid;
                mem_rw_mode         = s1s2_valid ? RW_WRITE : RW_IDLE;     
            end
            SKDEC_WR_S2: begin
                write_fsm_state_ns  = arc_SKDEC_WR_S2_SKDEC_WR_STAGE ? SKDEC_WR_STAGE : SKDEC_WR_S2;
                incr_wr_addr        = s1s2_valid;
                mem_rw_mode         = s1s2_valid ? RW_WRITE : RW_IDLE;
            end
            SKDEC_WR_T0: begin
                write_fsm_state_ns  = arc_SKDEC_WR_T0_SKDEC_WR_STAGE ? SKDEC_WR_STAGE : SKDEC_WR_T0;
                incr_wr_addr        = t0_valid;
                mem_rw_mode         = t0_valid ? RW_WRITE : RW_IDLE;  
            end
            SKDEC_WR_STAGE: begin
                write_fsm_state_ns = arc_SKDEC_WR_STAGE_SKDEC_WR_S2 ? SKDEC_WR_S2 :
                                     arc_SKDEC_WR_STAGE_SKDEC_WR_T0 ? SKDEC_WR_T0 :
                                     arc_SKDEC_WR_STAGE_SKDEC_WR_IDLE ? SKDEC_WR_IDLE : SKDEC_WR_STAGE;
            end
            default: begin
                write_fsm_state_ns = SKDEC_WR_IDLE;
            end
        endcase
    end

    //Outputs
    always_comb begin
        mem_a_wr_req.addr       = t0_mode ? mem_wr_addr : (s1_mode | s2_mode) ? {mem_wr_addr[ABR_MEM_ADDR_WIDTH-1:1],1'b0} : '0;
        mem_a_wr_req.rd_wr_en   = t0_mode & mem_a_wr_req.addr[0] ? RW_IDLE : mem_rw_mode;

        mem_b_wr_req.addr       = t0_mode ? mem_wr_addr : (s1_mode | s2_mode) ? {mem_wr_addr[ABR_MEM_ADDR_WIDTH-1:1],1'b1} : '0;
        mem_b_wr_req.rd_wr_en   = t0_mode & ~mem_a_wr_req.addr[0]? RW_IDLE : mem_rw_mode;

        kmem_a_rd_req.addr      = kmem_rd_addr;
        kmem_a_rd_req.rd_wr_en  = kmem_a_rw_mode;

        kmem_b_rd_req.addr      = t0_enable_fsm ? kmem_rd_addr + 1'b1 : kmem_rd_addr;
        kmem_b_rd_req.rd_wr_en  = kmem_b_rw_mode;

    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            s1s2_enable     <= 1'b0;
            t0_enable       <= 1'b0;
        end
        else if (zeroize) begin
            s1s2_enable     <= 1'b0;
            t0_enable       <= 1'b0;
        end
        else begin
            s1s2_enable     <= s1s2_enable_fsm;
            t0_enable       <= t0_enable_fsm;
        end
        
    end

endmodule
