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
// decompose_ctrl.sv
// -----------
// Takes care of memory accesses during decompose function

module decompose_ctrl
    import abr_params_pkg::*;
    import decompose_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire decompose_enable, //Assumes polynomials are stored in contiguous locations and 1 enable will trig all 8 at once
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr, 
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire r0_ready,

        output mem_if_t mem_rd_req,
        output mem_if_t mem_wr_req,
        output logic mod_enable,
        output logic decompose_done
    );

    //Internals
    logic [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr_reg, dest_base_addr_reg;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr_nxt, mem_wr_addr_nxt;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, mem_wr_addr;
    logic incr_rd_addr, incr_wr_addr;
    logic rst_rd_addr, rst_wr_addr;
    logic last_poly_last_addr_rd; //TODO: confirm that decompose take 8 polys. If there's a case with 7 polys, need to change code
    logic last_poly_last_addr_wr;
    logic decompose_busy;

    dcmp_read_state_e read_fsm_state_ps, read_fsm_state_ns;
    dcmp_write_state_e write_fsm_state_ps, write_fsm_state_ns;

    logic arc_DCMP_RD_IDLE_DCMP_RD_MEM;
    logic arc_DCMP_RD_MEM_DCMP_RD_IDLE;

    logic arc_DCMP_WR_IDLE_DCMP_WR_MEM;
    logic arc_DCMP_WR_MEM_DCMP_WR_IDLE;

    //Read addr counter
    always_comb mem_rd_addr_nxt = mem_rd_addr + 'h1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_addr <= 'h0;
            src_base_addr_reg <= 'h0;
        end
        else if (zeroize) begin
            mem_rd_addr <= 'h0;
            src_base_addr_reg <= 'h0;
        end
        else if (rst_rd_addr) begin
            mem_rd_addr <= src_base_addr;
            src_base_addr_reg <= src_base_addr;
        end
        else if (incr_rd_addr) begin
            mem_rd_addr <= last_poly_last_addr_rd ? 'h0 : mem_rd_addr_nxt;
        end
    end

    //Write addr counter
    always_comb mem_wr_addr_nxt = mem_wr_addr + 'h1;
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_wr_addr <= 'h0;
            dest_base_addr_reg <= 'h0;
        end
        else if (zeroize) begin
            mem_wr_addr <= 'h0;
            dest_base_addr_reg <= 'h0;
        end
        else if (rst_wr_addr) begin
            mem_wr_addr <= dest_base_addr;
            dest_base_addr_reg <= dest_base_addr;
        end
        else if (incr_wr_addr) begin
            mem_wr_addr <= last_poly_last_addr_wr ? 'h0 : mem_wr_addr_nxt;
        end
    end

    //Flags
    assign last_poly_last_addr_rd = (mem_rd_addr == src_base_addr_reg  + (MLDSA_K * (MLDSA_N/4))-1);
    assign last_poly_last_addr_wr = (mem_wr_addr == dest_base_addr_reg + (MLDSA_K * (MLDSA_N/4))-1);
    assign decompose_busy = (read_fsm_state_ps != DCMP_RD_IDLE);
    assign decompose_done = (read_fsm_state_ps == DCMP_RD_IDLE) & (write_fsm_state_ps == DCMP_WR_IDLE);

    //Read fsm
    always_comb begin
        arc_DCMP_RD_IDLE_DCMP_RD_MEM = (read_fsm_state_ps == DCMP_RD_IDLE) && decompose_enable;
        arc_DCMP_RD_MEM_DCMP_RD_IDLE = (read_fsm_state_ps == DCMP_RD_MEM) && last_poly_last_addr_rd;
    end
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= DCMP_RD_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= DCMP_RD_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    always_comb begin
        incr_rd_addr = 'b0;
        rst_rd_addr = 'b0;
        mod_enable = 'b0;

        case(read_fsm_state_ps)
            DCMP_RD_IDLE: begin
                read_fsm_state_ns = arc_DCMP_RD_IDLE_DCMP_RD_MEM ? DCMP_RD_MEM : DCMP_RD_IDLE;
                rst_rd_addr = 'b1;
            end
            DCMP_RD_MEM: begin
                read_fsm_state_ns = arc_DCMP_RD_MEM_DCMP_RD_IDLE ? DCMP_RD_IDLE : DCMP_RD_MEM;
                incr_rd_addr = 'b1;
                mod_enable = 'b1;
            end
        endcase
    end

    //Write fsm
    always_comb begin
        //Move to write mem state when reads are ongoing and mod 2gamma2 block has valid outputs
        arc_DCMP_WR_IDLE_DCMP_WR_MEM = (write_fsm_state_ps == DCMP_WR_IDLE) && decompose_busy && r0_ready;
        arc_DCMP_WR_MEM_DCMP_WR_IDLE = (write_fsm_state_ps == DCMP_WR_MEM) && last_poly_last_addr_wr;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            write_fsm_state_ps <= DCMP_WR_IDLE;
        else if (zeroize)
            write_fsm_state_ps <= DCMP_WR_IDLE;
        else
            write_fsm_state_ps <= write_fsm_state_ns;
    end

    always_comb begin
        incr_wr_addr = 'b0;
        rst_wr_addr = 'b0;

        case(write_fsm_state_ps)
            DCMP_WR_IDLE: begin
                write_fsm_state_ns = arc_DCMP_WR_IDLE_DCMP_WR_MEM ? DCMP_WR_MEM : DCMP_WR_IDLE;
                rst_wr_addr = 'b1;
            end
            DCMP_WR_MEM: begin
                write_fsm_state_ns = arc_DCMP_WR_MEM_DCMP_WR_IDLE ? DCMP_WR_IDLE : DCMP_WR_MEM;
                incr_wr_addr = 'b1;
            end
        endcase
    end

    //Assign outputs
    always_comb begin
        mem_rd_req.rd_wr_en = (read_fsm_state_ps == DCMP_RD_MEM) ? RW_READ : RW_IDLE;
        mem_rd_req.addr = mem_rd_addr;

        mem_wr_req.rd_wr_en = (write_fsm_state_ps == DCMP_WR_MEM) ? RW_WRITE : RW_IDLE;
        mem_wr_req.addr = mem_wr_addr;
    end
    

endmodule