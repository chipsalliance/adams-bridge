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
// compress_ctrl.sv
// ---------
// Controls memory accesses and iterates over MLKEM_K = 4 polynomials before generating done

module compress_ctrl
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire cmp_enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire ready,

        output mem_if_t mem_rd_req,
        output mem_if_t mem_wr_req,
        output logic done
    );

    //Internals
    logic [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr_reg, dest_base_addr_reg;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, mem_wr_addr, mem_rd_addr_nxt, mem_wr_addr_nxt;
    logic incr_rd_addr, incr_wr_addr;
    logic rst_rd_addr, rst_wr_addr;
    logic last_poly_last_addr_rd, last_poly_last_addr_wr;
    logic busy;

    cmp_read_state_e read_fsm_state_ps, read_fsm_state_ns;
    cmp_write_state_e write_fsm_state_ps, write_fsm_state_ns;

    logic arc_CMP_RD_IDLE_CMP_RD_MEM;
    logic arc_CMP_RD_MEM_CMD_RD_IDLE;

    logic arc_CMP_WR_IDLE_CMP_WR_MEM;
    logic arc_CMP_WR_MEM_CMP_WR_IDLE;

    //Read addr counter
    always_comb mem_rd_addr_nxt = mem_rd_addr + 'h1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_addr <= '0;
            src_base_addr_reg <= '0;
        end
        else if (zeroize) begin
            mem_rd_addr <= '0;
            src_base_addr_reg <= '0;
        end
        else if (rst_rd_addr) begin
            mem_rd_addr <= src_base_addr;
            src_base_addr_reg <= src_base_addr;
        end
        else if (incr_rd_addr) begin
            mem_rd_addr <= last_poly_last_addr_rd ? src_base_addr : mem_rd_addr_nxt;
        end
    end

    //Write addr counter
    always_comb mem_wr_addr_nxt = mem_wr_addr + 'h1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_wr_addr <= '0;
            dest_base_addr_reg <= '0;
        end
        else if (zeroize) begin
            mem_wr_addr <= '0;
            dest_base_addr_reg <= '0;
        end
        else if (rst_wr_addr) begin
            mem_wr_addr <= dest_base_addr;
            dest_base_addr_reg <= dest_base_addr;
        end
        else if (incr_wr_addr) begin
            mem_wr_addr <= last_poly_last_addr_wr ? dest_base_addr : mem_wr_addr_nxt;
        end
    end

    //Flags
    always_comb begin
        last_poly_last_addr_rd = (mem_rd_addr == (src_base_addr_reg + ((MLKEM_K * (MLKEM_N/4))-1)));
        last_poly_last_addr_wr = (mem_wr_addr == (dest_base_addr_reg + ((MLKEM_K * (MLKEM_N/4))-1)));

        done = (read_fsm_state_ps == CMP_RD_IDLE) & (write_fsm_state_ps == CMP_WR_IDLE);
        busy = (read_fsm_state_ps != CMP_RD_IDLE);
    end

    //Read FSM
    always_comb begin
        arc_CMP_RD_IDLE_CMP_RD_MEM = (read_fsm_state_ps == CMP_RD_IDLE) & cmp_enable;
        arc_CMP_RD_MEM_CMD_RD_IDLE = (read_fsm_state_ps == CMP_RD_MEM) & last_poly_last_addr_rd;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= CMP_RD_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= CMP_RD_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    always_comb begin
        incr_rd_addr = '0;
        rst_rd_addr = '0;

        case(read_fsm_state_ps)
            CMP_RD_IDLE: begin
                read_fsm_state_ns = arc_CMP_RD_IDLE_CMP_RD_MEM ? CMP_RD_MEM : CMP_RD_IDLE;
                rst_rd_addr = 'b1;
            end
            CMP_RD_MEM: begin
                read_fsm_state_ns = arc_CMP_RD_MEM_CMD_RD_IDLE ? CMP_RD_IDLE : CMP_RD_MEM;
                incr_rd_addr = 'b1;
            end
        endcase
    end

    //Write FSM
    always_comb begin
        arc_CMP_WR_IDLE_CMP_WR_MEM = (write_fsm_state_ps == CMP_WR_IDLE) & ready & !done;
        arc_CMP_WR_MEM_CMP_WR_IDLE = (write_fsm_state_ps == CMP_WR_MEM) & last_poly_last_addr_wr;
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            write_fsm_state_ps <= CMP_WR_IDLE;
        else if (zeroize)
            write_fsm_state_ps <= CMP_WR_IDLE;
        else
            write_fsm_state_ps <= write_fsm_state_ns;
    end

    always_comb begin
        incr_wr_addr = '0;
        rst_wr_addr = '0;

        case(write_fsm_state_ps)
            CMP_WR_IDLE: begin
                write_fsm_state_ns = arc_CMP_WR_IDLE_CMP_WR_MEM ? CMP_WR_MEM : CMP_WR_IDLE;
                rst_wr_addr = 'b1;
            end
            CMP_WR_MEM: begin
                write_fsm_state_ns = arc_CMP_WR_MEM_CMP_WR_IDLE ? CMP_WR_IDLE : CMP_WR_MEM;
                incr_wr_addr = 'b1;
            end
        endcase
    end

    //Assign outputs
    always_comb begin
        mem_rd_req.rd_wr_en = (read_fsm_state_ps == CMP_RD_MEM) ? RW_READ : RW_IDLE;
        mem_rd_req.addr     = mem_rd_addr;

        mem_wr_req.rd_wr_en = (write_fsm_state_ps == CMP_WR_MEM) ? RW_WRITE : RW_IDLE;
        mem_wr_req.addr     = mem_wr_addr;
    end

endmodule