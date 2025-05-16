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
// norm_check_ctrl.sv
// --------
// Manages memory accesses for check norm module. Two reads are done
// to perform 8 coeff checks per cycle. First port reads 0, 2, 4, etc, while second
// port reads 1, 3, 5, etc
// Assumes that one enable triggers check for all polynomials of chosen vector and 
// assumes all polynomials of the vector are stored in continuous addr space in memory

module norm_check_ctrl
    import abr_params_pkg::*;
    import norm_check_defines_pkg::*;
    #(
        parameter MLDSA_N = 256,
        parameter MLDSA_L = 7,
        parameter MLDSA_K = 8
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire norm_check_enable,
        input chk_norm_mode_t mode,

        input wire [5:0] randomness,

        input wire [ABR_MEM_ADDR_WIDTH-1:0] mem_base_addr,
        output mem_if_t mem_rd_req,
        output logic check_enable,
        output logic norm_check_done
    );

    
    chk_read_state_e read_fsm_state_ps, read_fsm_state_ns;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, locked_based_addr;

    //Flags
    logic incr_rd_addr;
    logic last_poly_last_addr;
    logic norm_check_busy;

    logic [4:0] latched_out_randomness;
    logic latched_in_randomness;
    logic [4:0] increment_addr;
    logic [6:0] neutral_cnt;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            latched_out_randomness  <= 'h0;
            latched_in_randomness   <= 'h0;
            increment_addr          <= 'h0;
            mem_rd_addr             <= 'h0;
            neutral_cnt             <= 'h0;
            locked_based_addr       <= 'h0;
        end
        else if (zeroize) begin
            latched_out_randomness  <= 'h0;
            latched_in_randomness   <= 'h0;
            increment_addr          <= 'h0;
            mem_rd_addr             <= 'h0;
            neutral_cnt             <= 'h0;
            locked_based_addr       <= 'h0;
        end
        else begin
            if (norm_check_enable) begin
                latched_out_randomness  <= randomness[5:1];
                latched_in_randomness   <= randomness[0];
                increment_addr          <= randomness[5:1];
                mem_rd_addr             <= {{(ABR_MEM_ADDR_WIDTH-6){1'b0}}, randomness};
                neutral_cnt             <= 'h0;
                locked_based_addr       <=  mem_base_addr;
            end
            else if (incr_rd_addr) begin
                latched_in_randomness   <= latched_in_randomness;
                latched_out_randomness  <= latched_out_randomness;
                increment_addr          <= increment_addr;
                mem_rd_addr             <= {mem_rd_addr[ABR_MEM_ADDR_WIDTH-1:6], increment_addr, latched_in_randomness};
                neutral_cnt             <= neutral_cnt + 'h1;
            end
            else if (~incr_rd_addr) begin
                latched_in_randomness   <= randomness[0];
                latched_out_randomness  <= latched_out_randomness;
                increment_addr          <= increment_addr + 'h1;
                mem_rd_addr             <= {mem_rd_addr[ABR_MEM_ADDR_WIDTH-1:1], ~latched_in_randomness};
                neutral_cnt             <= neutral_cnt + 'h1;
            end
        end
    end

    //Addr assignment
    always_comb begin
        mem_rd_req.addr = mem_rd_addr+locked_based_addr;

        mem_rd_req.rd_wr_en = ((read_fsm_state_ps == CHK_RD_MEM) | (read_fsm_state_ps == CHK_WAIT)) ? RW_READ : RW_IDLE;
    end

    //Last addr flag
    always_comb last_poly_last_addr = (neutral_cnt == ((MLDSA_N/4))-1);

    //Ctrl flags
    always_comb begin
        norm_check_busy = (read_fsm_state_ps != CHK_IDLE);
    end

    //FSM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= CHK_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= CHK_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    always_comb begin
        read_fsm_state_ns = read_fsm_state_ps;
        incr_rd_addr = 'b0;
        norm_check_done = 0;

        case(read_fsm_state_ps)
            CHK_IDLE: begin
                read_fsm_state_ns = norm_check_enable ? CHK_RD_MEM : CHK_IDLE;
            end
            CHK_RD_MEM: begin
                read_fsm_state_ns = last_poly_last_addr ? CHK_DONE : CHK_WAIT;
                incr_rd_addr = 'b0;
            end
            CHK_WAIT: begin
                read_fsm_state_ns = last_poly_last_addr ? CHK_DONE : CHK_RD_MEM;
                incr_rd_addr = 'b1;
            end
            CHK_DONE: begin
                read_fsm_state_ns = CHK_IDLE;
                norm_check_done = 'b1;
            end
            default begin
                read_fsm_state_ns = CHK_IDLE;
            end
        endcase
    end

    always_comb check_enable = (read_fsm_state_ps == CHK_RD_MEM) | (read_fsm_state_ps == CHK_WAIT);

endmodule