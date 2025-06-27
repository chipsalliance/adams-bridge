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
        input wire [2:0] num_poly,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,

        output mem_if_t mem_rd_req,
        output logic mem_rd_data_valid,
        input logic mem_rd_data_hold,
        output logic done
    );

    //Internals
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, mem_rd_addr_nxt;
    logic upd_rd_addr;
    logic ld_rd_addr;
    logic last_poly_last_addr_rd;

    cmp_read_state_e read_fsm_state_ps, read_fsm_state_ns;

    logic arc_CMP_RD_IDLE_CMP_RD_MEM;
    logic arc_CMP_RD_MEM_CMD_RD_IDLE;

    //Read addr counter
    //Go back and read previous address if mem_rd_data_hold is set, else increment by 1
    always_comb mem_rd_addr_nxt = mem_rd_data_hold ? mem_rd_addr : mem_rd_addr + 'h1;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_addr <= '0;
        end
        else if (zeroize) begin
            mem_rd_addr <= '0;
        end
        else if (ld_rd_addr) begin
            mem_rd_addr <= src_base_addr;
        end
        else if (upd_rd_addr) begin
            mem_rd_addr <= mem_rd_addr_nxt;
        end
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_data_valid <= '0;
        end
        else if (zeroize) begin
            mem_rd_data_valid <= '0;
        end
        else begin
            mem_rd_data_valid <= (mem_rd_req.rd_wr_en == RW_READ);
        end
    end

    //Flags
    always_comb begin
        last_poly_last_addr_rd = (mem_rd_addr == (src_base_addr + ((num_poly * (MLKEM_N/4))-1))) & ~mem_rd_data_hold;

        done = read_fsm_state_ps == CMP_RD_IDLE;
        ld_rd_addr = arc_CMP_RD_IDLE_CMP_RD_MEM | arc_CMP_RD_MEM_CMD_RD_IDLE;
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
        upd_rd_addr = '0;

        case(read_fsm_state_ps)
            CMP_RD_IDLE: begin
                read_fsm_state_ns = arc_CMP_RD_IDLE_CMP_RD_MEM ? CMP_RD_MEM : CMP_RD_IDLE;
            end
            CMP_RD_MEM: begin
                read_fsm_state_ns = arc_CMP_RD_MEM_CMD_RD_IDLE ? CMP_RD_IDLE : CMP_RD_MEM;
                upd_rd_addr = 1'b1;
            end
        endcase
    end

    //Assign outputs
    always_comb begin
        mem_rd_req.rd_wr_en = (read_fsm_state_ps == CMP_RD_MEM) ? RW_READ : RW_IDLE;
        mem_rd_req.addr     = mem_rd_addr;
    end

endmodule