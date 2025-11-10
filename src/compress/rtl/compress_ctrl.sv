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
        input compress_mode_t mode,
        input wire [2:0] num_poly,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr,

        output mem_if_t mem_rd_req,
        output logic done
    );

    //Internals
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, mem_rd_addr_nxt;
    logic inc_rd_addr;
    logic ld_rd_addr;
    logic last_poly_last_addr_rd;
    logic [11:0] mem_rd_pace, mem_rd_pace_init;
    cmp_read_state_e read_fsm_state_ps, read_fsm_state_ns;

    logic arc_CMP_RD_IDLE_CMP_RD_MEM;
    logic arc_CMP_RD_MEM_CMD_RD_IDLE;

    // Pace the memory reads to never overflow the buffer
    // Ensures that buffer is always supplied
    // Rotate the pacer each clock we are reading
    always_comb begin
        unique case (mode) inside
            compress1: begin
                mem_rd_pace_init = '1;
            end
            compress5: begin
                mem_rd_pace_init = '1;
            end
            compress11: begin
                mem_rd_pace_init = 12'b001101110111;
            end
            compress12: begin
                mem_rd_pace_init = 12'b011011011011;
            end
            default: begin
                mem_rd_pace_init = '0;
            end
        endcase
    end
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            mem_rd_pace <= '0;
        else if (zeroize)
            mem_rd_pace <= '0;
        else if (ld_rd_addr)
            mem_rd_pace <= mem_rd_pace_init;
        else if ((read_fsm_state_ps == CMP_RD_MEM) && (mode == compress12))
            mem_rd_pace <= {mem_rd_pace[0], mem_rd_pace[11:1]};
        else if ((read_fsm_state_ps == CMP_RD_MEM) && (mode == compress11))
            mem_rd_pace <= {1'b0, mem_rd_pace[0], mem_rd_pace[10:1]};
    end

    //Read addr counter
    //Increment read address
    always_comb mem_rd_addr_nxt = mem_rd_addr + 'h1;

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
        else if (inc_rd_addr) begin
            mem_rd_addr <= mem_rd_addr_nxt;
        end
    end

    //Flags
    always_comb begin
        last_poly_last_addr_rd = (mem_rd_addr == (src_base_addr + ((num_poly * (MLKEM_N/4))-1)));

        done = read_fsm_state_ps == CMP_RD_IDLE;
        ld_rd_addr = arc_CMP_RD_IDLE_CMP_RD_MEM | arc_CMP_RD_MEM_CMD_RD_IDLE;
    end

    //Read FSM
    always_comb begin
        arc_CMP_RD_IDLE_CMP_RD_MEM = (read_fsm_state_ps == CMP_RD_IDLE) & cmp_enable;
        arc_CMP_RD_MEM_CMD_RD_IDLE = (read_fsm_state_ps == CMP_RD_MEM) & mem_rd_pace[0] & last_poly_last_addr_rd;
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
        inc_rd_addr = '0;

        unique case (read_fsm_state_ps) inside
            CMP_RD_IDLE: begin
                read_fsm_state_ns = arc_CMP_RD_IDLE_CMP_RD_MEM ? CMP_RD_MEM : CMP_RD_IDLE;
            end
            CMP_RD_MEM: begin
                read_fsm_state_ns = arc_CMP_RD_MEM_CMD_RD_IDLE ? CMP_RD_IDLE : CMP_RD_MEM;
                inc_rd_addr = mem_rd_pace[0];
            end
        endcase
    end

    //Assign outputs
    always_comb begin
        mem_rd_req.rd_wr_en = (read_fsm_state_ps == CMP_RD_MEM) & mem_rd_pace[0] ? RW_READ : RW_IDLE;
        mem_rd_req.addr     = mem_rd_addr;
    end

endmodule