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
//
//======================================================================
//
// ntt_ctrl.sv
// --------
// This block:
// 1. Keeps track of stages of bf2x2 operation in ct, gs, pwo modes
// 2. Controls wr/rd addr of NTT mem
// 3. Controls rd addr of twiddle ROM
//======================================================================

module ntt_ctrl
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE = 23,
    parameter RADIX = 23,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N = 256,
    parameter MLDSA_LOGN = 8,
    parameter MEM_ADDR_WIDTH = 15,
    parameter BF_LATENCY = 10, //5 cycles per butterfly * 2 instances in serial = 10 clks
    parameter NTT_BUF_LATENCY = 4
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,
    input mode_t ntt_mode,
    input wire ntt_enable,
    input wire butterfly_ready,
    input wire buf0_valid,
    input wire sampler_valid,
    input wire accumulate,
    //NTT/INTT base addr
    input ntt_mem_addr_t ntt_mem_base_addr,
    //PWO base addr
    input pwo_mem_addr_t pwo_mem_base_addr,
    input wire shuffle_en,
    input wire   [5:0] random, //4+2 bits

    output logic bf_enable,
    output logic buf_wren,
    output logic buf_rden,
    output logic [1:0] buf_wrptr,
    output logic [1:0] buf_rdptr,
    output logic [6:0] twiddle_addr,

    output logic [MEM_ADDR_WIDTH-1:0] mem_rd_addr,
    output logic [MEM_ADDR_WIDTH-1:0] mem_wr_addr,
    output logic mem_rd_en,
    output logic mem_wr_en,
    output logic buf_wr_rst_count,
    output logic buf_rd_rst_count,

    //PWO outputs
    output logic [MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_a,
    output logic [MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_b,
    output logic [MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_c,
    output logic [MEM_ADDR_WIDTH-1:0] pw_mem_wr_addr_c,
    output logic pw_rden,
    output logic pw_wren,
    output logic busy,
    output logic done
);

//Parameters
localparam NTT_NUM_ROUNDS = 4;
localparam PWO_NUM_ROUNDS = 1;
localparam NTT_READ_ADDR_STEP   = 16;
localparam NTT_WRITE_ADDR_STEP  = 1;
localparam INTT_READ_ADDR_STEP  = 1;
localparam INTT_WRITE_ADDR_STEP = 16;
localparam PWO_READ_ADDR_STEP   = 1;
localparam PWO_WRITE_ADDR_STEP  = 1;
localparam PWM_LATENCY = 5;

localparam [MEM_ADDR_WIDTH-1:0] MEM_LAST_ADDR = 63;
localparam INTT_WRBUF_LATENCY = 13; //includes BF latency + mem latency for shuffled reads to begin
//FSM states
ntt_read_state_t read_fsm_state_ps, read_fsm_state_ns;
ntt_write_state_t write_fsm_state_ps, write_fsm_state_ns;

//BF enable flags
logic bf_enable_fsm, bf_enable_reg, bf_enable_reg_d2;

//Buffer signals
logic buf_wr_rst_count_ntt, buf_rd_rst_count_ntt;
logic buf_wr_rst_count_intt, buf_rd_rst_count_intt;
logic [1:0] buf_count;

//Shuffle buffer signals
logic [3:0] chunk_rand_offset; 
logic [3:0] chunk_count;
logic [1:0] index_rand_offset, index_count, mem_rd_index_ofst;
logic [1:0] buf_rdptr_int;
logic [1:0] buf_rdptr_f;
logic [BF_LATENCY:0][1:0] buf_rdptr_reg;
logic [INTT_WRBUF_LATENCY-1:0][1:0] buf_wrptr_reg;
logic [BF_LATENCY:0][3:0] chunk_count_reg;
logic latch_chunk_rand_offset, latch_index_rand_offset;
logic last_rd_addr, last_wr_addr;
logic mem_wr_en_fsm, mem_wr_en_reg;
logic mem_rd_en_fsm, mem_rd_en_reg;
logic pw_rden_fsm, pw_rden_reg;
logic pw_wren_fsm, pw_wren_reg;

//Mode flags
logic ct_mode, gs_mode, pwo_mode; //point-wise operations mode
logic pwm_mode, pwa_mode, pws_mode; 

//Addr internal wires
logic [MEM_ADDR_WIDTH-1:0] src_base_addr, interim_base_addr, dest_base_addr;
logic [MEM_ADDR_WIDTH-1:0] pw_base_addr_a, pw_base_addr_b, pw_base_addr_c;
logic [MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_a_nxt, pw_mem_rd_addr_b_nxt, pw_mem_rd_addr_c_nxt, pw_mem_wr_addr_c_nxt;
logic incr_mem_rd_addr;
logic incr_mem_wr_addr;
logic rst_rd_addr, rst_wr_addr; //TODO: need both?
logic [MEM_ADDR_WIDTH:0] mem_rd_addr_nxt, mem_wr_addr_nxt; //One extra bit in addr to roll over addr, so we can wraparound in the addr range
logic [MEM_ADDR_WIDTH-1:0] mem_rd_base_addr, mem_wr_base_addr; 
logic [4:0] rd_addr_step, wr_addr_step;
logic rd_addr_wraparound;
logic wr_addr_wraparound;

//PWO wires
logic incr_pw_rd_addr, incr_pw_wr_addr; //TODO: need both?
logic rst_pw_addr;

//Twiddle ROM wires
logic incr_twiddle_addr, incr_twiddle_addr_fsm, incr_twiddle_addr_reg, incr_twiddle_addr_reg_d2;
logic twiddle_mode, rst_twiddle_addr;
logic [6:0] twiddle_rand_offset;
logic [6:0] twiddle_end_addr, twiddle_addr_reg, twiddle_addr_reg_d2, twiddle_addr_reg_d3, twiddle_addr_int, twiddle_offset;

//FSM round signals
logic [$clog2(NTT_NUM_ROUNDS):0] num_rounds;
logic [$clog2(NTT_NUM_ROUNDS):0] rounds_count;
logic incr_rounds;
logic rst_rounds;

//Done, busy flags
logic stage_done;
logic ntt_done;
logic intt_done;
logic pwo_done;
logic ntt_busy;
logic pwo_busy;

//Valid count wires - counts 64 cycles of valid
logic [6:0] wr_valid_count;
logic [6:0] rd_valid_count_int, rd_valid_count;
logic wr_data_valid;
logic rd_data_valid;
logic rst_wr_valid_count, rst_rd_valid_count;

//Read FSM
//Common arcs
logic arc_IDLE_RD_STAGE;
logic arc_RD_EXEC_RD_STAGE;
logic arc_RD_STAGE_IDLE;

//NTT Arcs
logic arc_RD_STAGE_RD_BUF;
logic arc_RD_BUF_RD_EXEC;
logic arc_RD_EXEC_RD_BUF;
logic arc_RD_EXEC_EXEC_WAIT;
logic arc_EXEC_WAIT_RD_STAGE;

//INTT Arcs
logic arc_RD_STAGE_RD_EXEC;
logic arc_RD_STAGE_RD_EXEC_OPT;

//PWO Arc
logic arc_EXEC_WAIT_RD_EXEC;

//Other signals
logic buf_wren_ntt, buf_wren_ntt_reg;
logic buf_wren_intt, buf_wren_intt_reg;
logic buf_rden_ntt, buf_rden_ntt_reg;
logic buf_rden_intt;

//Write FSM
//Common arcs
logic arc_IDLE_WR_STAGE;
logic arc_WR_MEM_WR_STAGE;
logic arc_WR_STAGE_IDLE;

//NTT Arcs
logic arc_WR_STAGE_WR_MEM;

//INTT Arcs
logic arc_WR_STAGE_WR_BUF;
logic arc_WR_BUF_WR_MEM;
logic arc_WR_MEM_WR_BUF;
logic arc_WR_MEM_WR_WAIT;
logic arc_WR_WAIT_WR_STAGE;

//PWO Arcs
logic arc_WR_STAGE_WR_WAIT;
logic arc_WR_WAIT_WR_MEM;
logic arc_WR_STAGE_WR_MEM_OPT;

//------------------------------------------
always_comb begin
    ct_mode = (ntt_mode == ct);
    gs_mode = (ntt_mode == gs);
    pwo_mode = ntt_mode inside {pwm, pwa, pws};
    pwm_mode = (ntt_mode == pwm);
    pwa_mode = (ntt_mode == pwa);
    pws_mode = (ntt_mode == pws);
end

//------------------------------------------
//Rounds counter
//------------------------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        rounds_count <= 'h0;
    else if (zeroize)
        rounds_count <= 'h0;
    else if (rst_rounds)
        rounds_count <= 'h0;
    else if (incr_rounds && (rounds_count < num_rounds))
        rounds_count <= rounds_count + 'h1;
    else if (rounds_count == num_rounds)
        rounds_count <= 'h0;
end
assign num_rounds = (ntt_mode inside {ct, gs}) ? NTT_NUM_ROUNDS : PWO_NUM_ROUNDS;

//------------------------------------------
//Done flags
//------------------------------------------
//Stage is done when round counter is incremented and both fsms are in stage state
assign stage_done = (rounds_count > 'h0) && (read_fsm_state_ps == RD_STAGE) && (write_fsm_state_ps == WR_STAGE);//incr_rounds;
assign ntt_done   = ct_mode && (rounds_count == NTT_NUM_ROUNDS);
assign intt_done  = gs_mode && (rounds_count == NTT_NUM_ROUNDS);
assign pwo_done   = pwo_mode && (rounds_count == PWO_NUM_ROUNDS);
assign done       = ntt_done | intt_done | pwo_done;

//------------------------------------------
//Mem read/write addr counter
//------------------------------------------
//NTT mem addr
always_comb begin
    src_base_addr       = (ct_mode | gs_mode) ? ntt_mem_base_addr.src_base_addr : 'h0;
    interim_base_addr   = (ct_mode | gs_mode) ? ntt_mem_base_addr.interim_base_addr : 'h0;
    dest_base_addr      = (ct_mode | gs_mode) ? ntt_mem_base_addr.dest_base_addr : 'h0;

    pw_base_addr_a      = pwo_mode ? pwo_mem_base_addr.pw_base_addr_a : 'h0;
    pw_base_addr_b      = pwo_mode ? pwo_mem_base_addr.pw_base_addr_b : 'h0;
    pw_base_addr_c      = pwo_mode ? pwo_mem_base_addr.pw_base_addr_c : 'h0;
end
//Wraparound - indicates if we need to start at next addr (Eg. 0, 16, 32, 48, 1, 17, 33, 49, 2, ...)
//Wraparound allows addr to transition from 48 to 1, 49 to 2, etc instead of overflowing
always_comb begin
    mem_rd_base_addr   = (rounds_count == 'h0) ? src_base_addr : rounds_count[0] ? interim_base_addr : dest_base_addr;
    mem_wr_base_addr   = rounds_count[0] ? dest_base_addr : interim_base_addr;

    if (shuffle_en) begin
        mem_rd_addr_nxt    = (gs_mode | pwo_mode) ? (4*chunk_count) + (rd_addr_step*mem_rd_index_ofst) + mem_rd_base_addr : mem_rd_addr + rd_addr_step;
        mem_wr_addr_nxt    = ct_mode ? (MEM_ADDR_WIDTH+1)'((4*chunk_count_reg[0]) + (wr_addr_step*buf_rdptr_reg[0]) + mem_wr_base_addr) : gs_mode ? mem_wr_addr + wr_addr_step : (MEM_ADDR_WIDTH+1)'((4*chunk_count_reg[4]) + (wr_addr_step*buf_rdptr_reg[4]));
    end
    else begin
        mem_rd_addr_nxt = mem_rd_addr + rd_addr_step;
        mem_wr_addr_nxt = mem_wr_addr + wr_addr_step;
    end

    rd_addr_wraparound = mem_rd_addr_nxt > {1'b0,mem_rd_base_addr} + MEM_LAST_ADDR;
    wr_addr_wraparound = mem_wr_addr_nxt > {1'b0,mem_wr_base_addr} + MEM_LAST_ADDR;
end

//Read addr
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        mem_rd_addr <= 'h0;
    end
    else if (zeroize) begin
        mem_rd_addr <= 'h0;
    end
    else if (rst_rd_addr) begin
        if (shuffle_en)
            mem_rd_addr <= ct_mode ? mem_rd_base_addr + chunk_rand_offset : (gs_mode | pwo_mode) ? mem_rd_base_addr + (4*chunk_rand_offset) : mem_rd_base_addr;
        else
            mem_rd_addr <= mem_rd_base_addr;
    end
    else if (incr_mem_rd_addr) begin
        if (shuffle_en)
            mem_rd_addr <= (ct_mode & last_rd_addr) ? mem_rd_base_addr : rd_addr_wraparound ? MEM_ADDR_WIDTH'(mem_rd_addr_nxt - MEM_LAST_ADDR) : mem_rd_addr_nxt[MEM_ADDR_WIDTH-1:0];
        else
            mem_rd_addr <= rd_addr_wraparound ? MEM_ADDR_WIDTH'(mem_rd_addr_nxt - MEM_LAST_ADDR) : mem_rd_addr_nxt[MEM_ADDR_WIDTH-1:0]; 
    end
end

//Write addr
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        mem_wr_addr <= 'h0;
    end
    else if (zeroize) begin
        mem_wr_addr <= 'h0;
    end
    else if (rst_wr_addr) begin
        if (shuffle_en)
            mem_wr_addr <= (ct_mode | pwo_mode) ? mem_wr_base_addr + (4*chunk_rand_offset) : gs_mode ? mem_wr_base_addr + chunk_rand_offset : mem_wr_base_addr;
        else
            mem_wr_addr <= mem_wr_base_addr;  
    end
    else if (incr_mem_wr_addr) begin
        if (shuffle_en)
            mem_wr_addr <= (gs_mode & last_wr_addr) ? mem_wr_base_addr : wr_addr_wraparound ? MEM_ADDR_WIDTH'(mem_wr_addr_nxt - MEM_LAST_ADDR) : mem_wr_addr_nxt[MEM_ADDR_WIDTH-1:0];
        else
            mem_wr_addr <= wr_addr_wraparound ? MEM_ADDR_WIDTH'(mem_wr_addr_nxt - MEM_LAST_ADDR) : mem_wr_addr_nxt[MEM_ADDR_WIDTH-1:0];
    end
end

always_comb begin
    pw_mem_rd_addr_a_nxt = pw_base_addr_a + (4*chunk_count) + (PWO_READ_ADDR_STEP*mem_rd_index_ofst);
    pw_mem_rd_addr_b_nxt = pw_base_addr_b + (4*chunk_count) + (PWO_READ_ADDR_STEP*mem_rd_index_ofst);
    pw_mem_rd_addr_c_nxt = accumulate ? pw_base_addr_c + ((4*chunk_count)+(PWO_READ_ADDR_STEP*mem_rd_index_ofst)) : 'h0; //TODO check timing
    pw_mem_wr_addr_c_nxt = accumulate ? pw_base_addr_c + (4*chunk_count_reg[PWM_LATENCY-2]) + (PWO_WRITE_ADDR_STEP*buf_rdptr_reg[PWM_LATENCY-2])
                                      : (pwa_mode | pws_mode) ? pw_base_addr_c + (4*chunk_count_reg[7]) + (PWO_WRITE_ADDR_STEP*buf_rdptr_reg[7])
                                      : pw_base_addr_c + (4*chunk_count_reg[PWM_LATENCY-1]) + (PWO_WRITE_ADDR_STEP*buf_rdptr_reg[PWM_LATENCY-1]); //2
end

//PWO addr
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        pw_mem_rd_addr_a <= '0;
        pw_mem_rd_addr_b <= '0;
        pw_mem_rd_addr_c <= '0;
        pw_mem_wr_addr_c <= '0;
    end
    else if (zeroize) begin
        pw_mem_rd_addr_a <= '0;
        pw_mem_rd_addr_b <= '0;
        pw_mem_rd_addr_c <= '0;
        pw_mem_wr_addr_c <= '0;
    end
    else if (rst_pw_addr) begin
        pw_mem_rd_addr_a <= shuffle_en ? (4*chunk_rand_offset) + pw_base_addr_a : pw_base_addr_a;
        pw_mem_rd_addr_b <= shuffle_en ? (4*chunk_rand_offset) + pw_base_addr_b : pw_base_addr_b;
        pw_mem_rd_addr_c <= shuffle_en ? (4*chunk_rand_offset) + pw_base_addr_c : pw_base_addr_c;
        pw_mem_wr_addr_c <= shuffle_en ? (4*chunk_rand_offset) + pw_base_addr_c : pw_base_addr_c;
    end
    else begin
        if (incr_pw_rd_addr) begin
            if (shuffle_en) begin
                pw_mem_rd_addr_a <= pw_mem_rd_addr_a_nxt;
                pw_mem_rd_addr_b <= pw_mem_rd_addr_b_nxt;
                pw_mem_rd_addr_c <= accumulate ? pw_mem_rd_addr_c_nxt : 'h0; //addr in sync with a, b. However, the data is flopped 4 cycles inside BF to align with mul result
            end
            else begin
                pw_mem_rd_addr_a <= pw_mem_rd_addr_a + PWO_READ_ADDR_STEP;
                pw_mem_rd_addr_b <= pw_mem_rd_addr_b + PWO_READ_ADDR_STEP;
                pw_mem_rd_addr_c <= accumulate ? pw_mem_rd_addr_c + PWO_READ_ADDR_STEP : 'h0; //addr in sync with a, b. However, the data is flopped 4 cycles inside BF to align with mul result
            end
        end
        if (incr_pw_wr_addr) begin
            pw_mem_wr_addr_c <= shuffle_en ? pw_mem_wr_addr_c_nxt : pw_mem_wr_addr_c + PWO_WRITE_ADDR_STEP;
        end
    end
end


//------------------------------------------
//Twiddle addr logic - TODO: shuffling+masking (adjust latency)
//------------------------------------------
always_comb begin
    unique case(rounds_count)
        'h0: begin
            twiddle_end_addr    = ct_mode ? 'd0 : 'd63;
            twiddle_offset      = 'h0;
            twiddle_rand_offset = ct_mode ? 'h0 : 7'((4*chunk_count_reg[BF_LATENCY]) + buf_wrptr_reg[INTT_WRBUF_LATENCY-1]);
        end
        'h1: begin
            twiddle_end_addr    = ct_mode ? 'd3 : 'd15;
            twiddle_offset      = ct_mode ? 'd1 : 'd64;
            twiddle_rand_offset = ct_mode ? 7'(buf_rdptr_int) : 7'((chunk_count_reg[BF_LATENCY] % 4)*4 + buf_wrptr_reg[INTT_WRBUF_LATENCY-1]);
        end
        'h2: begin
            twiddle_end_addr    = ct_mode ? 'd15 : 'd3;
            twiddle_offset      = ct_mode ? 'd5 : 'd80;
            twiddle_rand_offset = ct_mode ? 7'((chunk_count % 'd4)*'d4 + buf_rdptr_int) : 7'(buf_wrptr_reg[INTT_WRBUF_LATENCY-1]);
        end
        'h3: begin
            twiddle_end_addr    = ct_mode ? 'd63 : 'd0;
            twiddle_offset      = ct_mode ? 'd21 : 'd84;
            twiddle_rand_offset = ct_mode ? 7'((chunk_count % 'd16)*4 + buf_rdptr_int) : 'h0;
        end
        default: begin
            twiddle_end_addr    = 'h0;
            twiddle_offset      = 'h0;
            twiddle_rand_offset = 'h0;
        end
    endcase
end

//Flop the incr and twiddle_addr to align with memory read latency
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        incr_twiddle_addr_reg <= 'b0;
        incr_twiddle_addr_reg_d2 <= 'b0;
    end
    else if (zeroize) begin
        incr_twiddle_addr_reg <= 'b0;
        incr_twiddle_addr_reg_d2 <= 'b0;
    end
    else begin
        incr_twiddle_addr_reg <= incr_twiddle_addr_fsm;
        incr_twiddle_addr_reg_d2 <= incr_twiddle_addr_reg;
    end
end

assign incr_twiddle_addr = ct_mode ? incr_twiddle_addr_fsm : incr_twiddle_addr_reg;


always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        twiddle_addr_reg <= 'h0;
    else if (zeroize)
        twiddle_addr_reg <= 'h0;
    else if (incr_twiddle_addr)
        twiddle_addr_reg <= shuffle_en ? twiddle_rand_offset : (twiddle_addr_reg == twiddle_end_addr) ? 'h0 : twiddle_addr_reg + 'd1;
    else if (rst_twiddle_addr)
        twiddle_addr_reg <= 'h0;
end

assign twiddle_addr_int = (~shuffle_en | ct_mode) ? twiddle_addr_reg + twiddle_offset : twiddle_rand_offset + twiddle_offset;

//------------------------------------------
//Busy logic
//------------------------------------------
assign busy = ntt_busy | pwo_busy;
assign ntt_busy = (read_fsm_state_ps != RD_IDLE) && (write_fsm_state_ps != WR_IDLE) && (ct_mode | gs_mode);
assign pwo_busy = (read_fsm_state_ps != RD_IDLE) && (write_fsm_state_ps != WR_IDLE) && pwo_mode;

//------------------------------------------
//Valid count - to check that all 64 addr have been processed - check writes to mem
//------------------------------------------
always_comb wr_data_valid = gs_mode ? buf0_valid : butterfly_ready; //ct or pwo mode - look for bf_ready
always_comb rd_data_valid = ct_mode ? buf0_valid : gs_mode ? bf_enable_fsm : sampler_valid;

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        wr_valid_count <= 'h0;
    else if (zeroize)
        wr_valid_count <= 'h0;
    else if (rst_wr_valid_count)
        wr_valid_count <= 'h0;
    else if (wr_data_valid)
        wr_valid_count <= gs_mode ? (wr_valid_count > 'h40) ? 'h0 : wr_valid_count + 'h4 
                                    : wr_valid_count + 'h1;
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        rd_valid_count <= 'h0;
    else if (zeroize)
        rd_valid_count <= 'h0;
    else if (rst_rd_valid_count)
        rd_valid_count <= 'h0;
    else if (rd_data_valid)
        rd_valid_count <= ct_mode ? (rd_valid_count > 'h40) ? 'h0 : rd_valid_count + 'h4 
                                    : rd_valid_count + 'h1;
    
end

//------------------------------------------
//Buffer count - start count when buf0_valid is received
//Once counter starts, count until 3 to signify that all 4 buffers
//are valid. Then wait at 0 until next buf0_valid comes in
//------------------------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        buf_count <= 'h0;
    else if (zeroize)
        buf_count <= 'h0;
    else if (buf0_valid)
        buf_count <= buf_count + 1;
    else if (buf_count > 0 && buf_count < 3)
        buf_count <= buf_count + 1;
    else
        buf_count <= 'h0;
end

//------------------------------------------
//Shuffle buffer
//------------------------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        chunk_rand_offset <= 'h0;
        chunk_count <= 'h0;
    end
    else if (zeroize) begin
        chunk_rand_offset <= 'h0;
        chunk_count <= 'h0;
    end
    else if (latch_chunk_rand_offset) begin
        chunk_rand_offset <= random[5:2];
        chunk_count <= random[5:2];
    end
    else if ((ct_mode & (buf_count == 'h3)) | ((gs_mode | (pwo_mode & incr_pw_rd_addr)) & (index_count == 'h3))) begin //update chunk after every 4 cycles - TODO: stop chunk counting when there's no incr_rd_addr in ntt/intt modes
        chunk_count <= (chunk_count == 'hf) ? 'h0 : chunk_count + 'h1;
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        index_rand_offset <= 'h0;
        
    end
    else if (zeroize) begin
        index_rand_offset <= 'h0;
        
    end
    else if (latch_index_rand_offset) begin
        index_rand_offset <= random[1:0];
    end
    
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        buf_rdptr_reg <= 'h0;
        buf_wrptr_reg <= 'h0;
    end
    else if (zeroize) begin
        buf_rdptr_reg <= 'h0;
        buf_wrptr_reg <= 'h0;
    end
    else if (ct_mode & (buf_rden_ntt | butterfly_ready)) begin
        buf_rdptr_reg <= {buf_rdptr_int, buf_rdptr_reg[BF_LATENCY:1]};
    end
    else if (gs_mode & (incr_mem_rd_addr | butterfly_ready)) begin
        buf_wrptr_reg <= {mem_rd_index_ofst, buf_wrptr_reg[INTT_WRBUF_LATENCY-1:1]};
    end
    else if (pwo_mode & (incr_pw_rd_addr | butterfly_ready)) begin
        buf_rdptr_reg <= {mem_rd_index_ofst, buf_rdptr_reg[BF_LATENCY:1]}; //TODO: create new reg with apt name for PWO
    end
    else begin
        buf_rdptr_reg <= 'h0;
        buf_wrptr_reg <= 'h0;
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        buf_rdptr_f <= 'h0;
    end
    else if (zeroize) begin
        buf_rdptr_f <= 'h0;
        end
    else begin
        buf_rdptr_f <= buf_rdptr_int;
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        index_count <= 'h0;
    end
    else if (zeroize) begin
        index_count <= 'h0;
    end
    else if ((gs_mode & (incr_mem_rd_addr)) | (pwo_mode & incr_pw_rd_addr)) begin
        index_count <= index_count + 'h1;
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        chunk_count_reg <= 'h0;
    end
    else if (zeroize) begin
        chunk_count_reg <= 'h0;
    end
    else if (buf_rden_ntt | butterfly_ready | (gs_mode & incr_mem_rd_addr) | (pwo_mode & incr_pw_rd_addr)) begin //TODO: replace gs condition with an fsm generated flag perhaps?
        chunk_count_reg <= {chunk_count, chunk_count_reg[BF_LATENCY:1]};
    end
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        buf_wrptr <= 'h0;
    end
    else if (zeroize) begin
        buf_wrptr <= 'h0;
    end
    else if (buf_wren & (ct_mode | ~shuffle_en)) begin //ct mode - buf writes are in order
        buf_wrptr <= (buf_wrptr == 'h3) ? 'h0 : buf_wrptr + 'h1;
    end
    else if (buf_wren_intt & gs_mode & shuffle_en) begin // gs mode
        buf_wrptr <= buf_wrptr_reg[0];
    end
end

always_comb begin
    last_rd_addr   = (mem_rd_addr == mem_rd_base_addr + MEM_LAST_ADDR);
    last_wr_addr   = (mem_wr_addr == mem_wr_base_addr + MEM_LAST_ADDR);
    buf_rdptr_int  = (shuffle_en & ct_mode) ? index_rand_offset + buf_count : buf_count; //TODO: flop?
    buf_rdptr      = (shuffle_en & ct_mode) ? buf_rdptr_f : buf_count;
    latch_chunk_rand_offset = arc_IDLE_WR_STAGE | arc_WR_MEM_WR_STAGE | arc_WR_WAIT_WR_STAGE;
    latch_index_rand_offset = ct_mode ? (buf_wrptr == 'h3) : (gs_mode | (pwo_mode & incr_pw_rd_addr)) & (arc_RD_STAGE_RD_EXEC | (index_count == 'h3));
    mem_rd_index_ofst = (pwo_mode | gs_mode) ? (index_count + index_rand_offset) : 'h0;
end


//------------------------------------------
//NTT/INTT Read FSM 
//------------------------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        read_fsm_state_ps <= RD_IDLE;
    else if (zeroize)
        read_fsm_state_ps <= RD_IDLE;
    else
        read_fsm_state_ps <= read_fsm_state_ns;
end

//Arc assignments
always_comb begin
    //Start NTT/INTT op when fsm is in IDLE state and there's an enable coming in
    arc_IDLE_RD_STAGE = (read_fsm_state_ps == RD_IDLE) && ntt_enable ; //FSM will not enter IDLE state until entire NTT/INTT is done, so we will not accept any new commands
    //For these two arcs, perf can be possibly optimized:
    //When fsm comes back to stage, reads are done, butterfly is executing the last 10 inputs
    //write fsm needs to write last 10 outputs to memory
    //If we let read fsm to advance to next round, there is a latency of 4 cycles (from buffer) + 10 cycles (from butterfly)
    //before the output is written back to memory. This is best case (no bubbles)
    //In this case, there is time for butterfly to produce output while the writes from previous round finish
    //TODO: review this assumption. For now, assuming we wait until entire round on both read and write side is done

    //Check to make sure all writes from prev round have finished before moving onto next round in read fsm
    arc_RD_STAGE_RD_BUF     = (read_fsm_state_ps == RD_STAGE)  && (write_fsm_state_ps == WR_STAGE) && (ct_mode && !ntt_done); 
    arc_RD_STAGE_RD_EXEC    = (read_fsm_state_ps == RD_STAGE)  && (write_fsm_state_ps == WR_STAGE) && ((gs_mode && !intt_done) || (pwo_mode && (!pwo_done /*|| ntt_enable*/)));

    //Don't wait for writes to complete before transitioning to next round. (See above TODO)
    arc_RD_STAGE_RD_EXEC_OPT= (read_fsm_state_ps == RD_STAGE)  && /*(write_fsm_state_ps == WR_STAGE) &&*/ ((gs_mode && !intt_done) || (pwo_mode && (!pwo_done /*|| ntt_enable*/)));

    //This arc is only for ct mode. When buffer is valid, bf2x2 can be enabled
    arc_RD_BUF_RD_EXEC      = (read_fsm_state_ps == RD_BUF  )  && buf0_valid;

    //This arc is only for ct mode. If there's no buf0_valid, all 4 buffers have been emptied and total valid_count is < 64, go back to buf state and wait for it to fill up
    //Indicates that buf0, 1, 2 3 have finished executing and there's no valid input, so wait for buf to fill up again
    //Since there's an input buffer, valid_count is counted in steps of 4, so it ends at 64
    arc_RD_EXEC_RD_BUF      = (read_fsm_state_ps == RD_EXEC )  && ct_mode && (!buf0_valid && (buf_count == 0)) && (rd_valid_count < 'h40);

    //This arc is only for gs mode. Execution is done when all 63 addr locations have been read. Since there's no input buffer, valid_count ends at 63. 
    arc_RD_EXEC_RD_STAGE    = (read_fsm_state_ps == RD_EXEC )  && ((gs_mode || pwo_mode) && (rd_valid_count == 'h3f));

    //All rounds of NTT or INTT are done. Go to IDLE and wait for next command. In PWO mode, if ntt_enable is given, start next op
    arc_RD_STAGE_IDLE       = (read_fsm_state_ps == RD_STAGE)  && (ntt_done || intt_done || (pwo_done && !ntt_enable));

    //This arc is only for ct mode. Move to EXEC_WAIT state when the last read is done. No more reads to perform, but the buffer needs to be emptied
    arc_RD_EXEC_EXEC_WAIT   = (read_fsm_state_ps == RD_EXEC )  && ((ct_mode && (((buf_count == 'h3) && (rd_valid_count == 'h3c)))) || (pwo_mode && !sampler_valid));

    //This arc is only for pwo mode. Move back to RD_EXEC when sampler_valid is available
    arc_EXEC_WAIT_RD_EXEC   = (read_fsm_state_ps == EXEC_WAIT) && (pwo_mode && sampler_valid && (rd_valid_count < 'h3f));

    //This arc is only for ct mode. When valid_count is 64 and buf_count is 3 (meaning all 4 buffers have been used), move to RD_STAGE indicating that round is done
    arc_EXEC_WAIT_RD_STAGE  = (read_fsm_state_ps == EXEC_WAIT) && (rd_valid_count == 'h40) && (buf_count == 'h3);
end

always_comb begin
    read_fsm_state_ns       = read_fsm_state_ps;
    buf_wren_ntt            = 1'b0;
    buf_rden_ntt            = 1'b0;
    incr_mem_rd_addr        = 1'b0;
    bf_enable_fsm           = 1'b0;
    mem_rd_en_fsm           = 1'b0;
    incr_twiddle_addr_fsm   = 1'b0;
    rd_addr_step            = 'h0;
    rst_rd_addr             = 1'b0;
    rst_rd_valid_count      = 1'b0;
    buf_wr_rst_count_ntt    = 1'b0;
    buf_rd_rst_count_ntt    = 1'b0;
    rst_twiddle_addr        = 1'b0;
    incr_pw_rd_addr         = 1'b0;
    pw_rden_fsm             = 1'b0;
    unique case(read_fsm_state_ps)
        RD_IDLE: begin
            read_fsm_state_ns       = arc_IDLE_RD_STAGE ? RD_STAGE : RD_IDLE;
            rst_rd_addr             = 1'b1;
            rst_rd_valid_count      = 1'b1;
            buf_wr_rst_count_ntt    = 1'b1;
            buf_rd_rst_count_ntt    = 1'b1;
            rst_twiddle_addr        = 1'b1;
        end
        RD_STAGE: begin
            read_fsm_state_ns       = arc_RD_STAGE_RD_BUF       ? RD_BUF : 
                                        arc_RD_STAGE_RD_EXEC    ? RD_EXEC :
                                        arc_RD_STAGE_IDLE       ? RD_IDLE : RD_STAGE;
            rst_rd_addr             = 1'b1;
            rst_rd_valid_count      = 1'b1;
            //reset if in ntt mode, since writes won't use the buffer, it's safe to reset buffer
            buf_wr_rst_count_ntt    = ct_mode;
            buf_rd_rst_count_ntt    = ct_mode;
            rst_twiddle_addr        = !butterfly_ready;
        end
        RD_BUF: begin
            read_fsm_state_ns       = arc_RD_BUF_RD_EXEC ? RD_EXEC : RD_BUF;
            buf_wren_ntt            = 1'b1;
            buf_rden_ntt            = buf0_valid;
            incr_mem_rd_addr        = 1'b1;
            mem_rd_en_fsm           = 1'b1;
            bf_enable_fsm           = buf0_valid; //Enable bf2x2 as soon as buf is valid
            incr_twiddle_addr_fsm   = buf0_valid;
            rd_addr_step            = NTT_READ_ADDR_STEP;
        end
        RD_EXEC: begin
            read_fsm_state_ns       = arc_RD_EXEC_RD_BUF ? RD_BUF :
                                        arc_RD_EXEC_RD_STAGE ? RD_STAGE : 
                                        arc_RD_EXEC_EXEC_WAIT ? EXEC_WAIT : RD_EXEC;
            buf_wren_ntt            = ct_mode;
            buf_rden_ntt            = ct_mode;
            incr_mem_rd_addr        = (ntt_mode inside {ct, gs});
            if (shuffle_en)
                mem_rd_en_fsm       = (ntt_mode inside {ct, gs}) ? (mem_rd_addr <= MEM_LAST_ADDR + mem_rd_base_addr) & ~arc_RD_EXEC_EXEC_WAIT : 1'b0;
            else
                mem_rd_en_fsm       = (ntt_mode inside {ct, gs}) ? (mem_rd_addr <= MEM_LAST_ADDR + mem_rd_base_addr) : 1'b0;
            bf_enable_fsm           = pwo_mode ? sampler_valid : 1'b1;
            incr_twiddle_addr_fsm   = ntt_mode inside {ct, gs};
            rd_addr_step            = ct_mode ? NTT_READ_ADDR_STEP : INTT_READ_ADDR_STEP;
            incr_pw_rd_addr         = sampler_valid & pwo_mode;
            pw_rden_fsm             = sampler_valid & pwo_mode;
        end
        EXEC_WAIT: begin
            read_fsm_state_ns       = arc_EXEC_WAIT_RD_STAGE ? RD_STAGE : arc_EXEC_WAIT_RD_EXEC ? RD_EXEC : EXEC_WAIT;
            buf_wren_ntt            = (buf_count < 3) && !pwo_mode;
            buf_rden_ntt            = !pwo_mode;
            buf_wr_rst_count_ntt    = 1'b1; //There are no more mem reads, so buf writes need to halt
            buf_rd_rst_count_ntt    = 1'b0; //There are still some entries in buf that BF2x2 needs to pick up
            bf_enable_fsm           = pwo_mode ? sampler_valid : (buf_count <= 3);
            incr_twiddle_addr_fsm   = (ct_mode | gs_mode);
            rd_addr_step            = NTT_READ_ADDR_STEP;
            incr_pw_rd_addr         = (pwo_mode & sampler_valid);
            pw_rden_fsm             = (pwo_mode & sampler_valid);
        end
        default: begin
            read_fsm_state_ns       = RD_IDLE;
        end
    endcase
end

//------------------------------------------
//NTT/INTT Write FSM 
//------------------------------------------
always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n)
        write_fsm_state_ps <= WR_IDLE;
    else if (zeroize)
        write_fsm_state_ps <= WR_IDLE;
    else
        write_fsm_state_ps <= write_fsm_state_ns;
end

//Arc assignments
always_comb begin
    //Start NTT/INTT op when fsm is in IDLE state and there's an enable coming in
    arc_IDLE_WR_STAGE       = (write_fsm_state_ps == WR_IDLE)  && ntt_enable ;

    if (shuffle_en) begin
        //This arc is only for ct mode. No buffer in the path, so wait for all addr to be written (0-63) before transitioning to WR_STAGE
        arc_WR_MEM_WR_STAGE     = (write_fsm_state_ps == WR_MEM)   && ((ct_mode) && (wr_valid_count == 'h3f)); //(mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR)); //this arc is for ct mode, 

        //This arc is only for ct mode since there's no output buffer
        arc_WR_STAGE_WR_MEM     = (write_fsm_state_ps == WR_STAGE) && ((ct_mode && !ntt_done) || (pwo_mode && !pwo_done)); // || (pwo_mode && (!pwo_done /*|| ntt_enable*/)));
    end
    else begin 
        arc_WR_MEM_WR_STAGE     = (write_fsm_state_ps == WR_MEM)   && ((ct_mode || pwo_mode) && (wr_valid_count == 'h3f)); //(mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR)); //this arc is for ct mode, 
        arc_WR_STAGE_WR_MEM     = (write_fsm_state_ps == WR_STAGE) && (ct_mode && !ntt_done);
    end

    //All rounds of NTT or INTT are done. Go to IDLE and wait for next command
    arc_WR_STAGE_IDLE       = (write_fsm_state_ps == WR_STAGE) && (ntt_done || intt_done || pwo_done);

    //pwm arc. If in WR_STAGE, read fsm is executing, go back to WR_MEM state to perform current round's writes
    arc_WR_STAGE_WR_MEM_OPT = (write_fsm_state_ps == WR_STAGE) && (read_fsm_state_ps == RD_EXEC) && (pwo_mode && pwo_busy);

    //This arc is only for gs mode
    arc_WR_STAGE_WR_BUF     = (write_fsm_state_ps == WR_STAGE) && gs_mode && !intt_done;

    //pwm arc. If in WR STAGE, transition directly to wait
    arc_WR_STAGE_WR_WAIT    = (write_fsm_state_ps == WR_STAGE) && (pwo_mode && !pwo_done);

    //This arc is only for gs mode. Start writing to memory when buf0_valid is asserted
    arc_WR_BUF_WR_MEM       = (write_fsm_state_ps == WR_BUF)   && (gs_mode && buf0_valid);

    //This arc is only for gs mode. If there's no buf0_valid, all 4 buffers have been emptied and total valid_count is < 64, go back to buf state and wait for it to fill up
    //Indicates that buf0, 1, 2 3 have finished executing and there's no valid input, so wait for buf to fill up again
    //Since there's an output buffer, valid_count is counted in steps of 4, so it ends at 64
    arc_WR_MEM_WR_BUF       = (write_fsm_state_ps == WR_MEM)   && (gs_mode && (!buf0_valid && (buf_count == 0)) && (wr_valid_count < 'h40));

    //Move to WR_WAIT state when the last outputs from bf2x2 have been captured in the buffers. They still need to be shifted out of the buffers and into memory, so keep buf_wren 1 here
    //Assumption - no bubbles in NTT or INTT. If bubbles, need to consider sampler_valid
    //TODO: can WR_WAIT state be removed? fsm can finish all 64 addr in WR_MEM state?
    arc_WR_MEM_WR_WAIT      = shuffle_en ? (write_fsm_state_ps == WR_MEM)   && ((gs_mode &&  (buf0_valid && (wr_valid_count == 'h3c))) || (pwo_mode && butterfly_ready && (wr_valid_count == 'h3f)))
                                        : (write_fsm_state_ps == WR_MEM) && ((gs_mode && (buf0_valid && (wr_valid_count == 'h3c))) || (pwo_mode && !butterfly_ready && (wr_valid_count < 'h3f))); // || (ct_mode && (wr_valid_count == 'h3f)));

    //This arc is only for pwo mode. Move back from wait to write state when there's a valid BFU output
    arc_WR_WAIT_WR_MEM      = (write_fsm_state_ps == WR_WAIT) && (pwo_mode && butterfly_ready);

    //When valid_count is 64 and buf_count is 3 (meaning all 4 buffers have been used), move to WR_STAGE indicating that round is done
    arc_WR_WAIT_WR_STAGE    = shuffle_en ? (write_fsm_state_ps == WR_WAIT)  && ((gs_mode && (buf_count == 'h3)) || ct_mode || pwo_mode)
                                        : (write_fsm_state_ps == WR_WAIT)  && (!pwo_mode && (buf_count == 'h3));
end

always_comb begin
    write_fsm_state_ns  = write_fsm_state_ps;
    buf_wren_intt       = 1'b0;
    buf_rden_intt       = 1'b0;
    incr_mem_wr_addr    = 1'b0;
    mem_wr_en_fsm       = 1'b0;
    wr_addr_step        = 'h0;
    rst_wr_addr         = 1'b0;
    rst_wr_valid_count  = 1'b0;
    buf_wr_rst_count_intt  = 1'b0;
    buf_rd_rst_count_intt  = 1'b0;
    incr_pw_wr_addr     = 1'b0;
    pw_wren_fsm         = 1'b0;
    rst_pw_addr         = 1'b0;
    unique case(write_fsm_state_ps)
        WR_IDLE: begin
            write_fsm_state_ns  = arc_IDLE_WR_STAGE ? WR_STAGE : WR_IDLE;
            rst_wr_addr         = 1'b1;
            rst_wr_valid_count  = 1'b1;
            rst_pw_addr         = 1'b1;
        end
        WR_STAGE: begin
            if (shuffle_en)
                write_fsm_state_ns  = arc_WR_STAGE_WR_MEM   ? WR_MEM : 
                                    arc_WR_STAGE_WR_BUF ? WR_BUF :
                                    // arc_WR_STAGE_WR_WAIT? WR_WAIT :
                                    arc_WR_STAGE_IDLE   ? WR_IDLE : WR_STAGE;
            else
                write_fsm_state_ns  = arc_WR_STAGE_WR_MEM   ? WR_MEM : 
                                    arc_WR_STAGE_WR_BUF ? WR_BUF :
                                    arc_WR_STAGE_WR_WAIT? WR_WAIT :
                                    arc_WR_STAGE_IDLE   ? WR_IDLE : WR_STAGE;
            rst_wr_addr             = 1'b1;
            rst_wr_valid_count      = 1'b1;
            buf_wr_rst_count_intt   = gs_mode;
            buf_rd_rst_count_intt   = gs_mode;
            rst_pw_addr             = pwo_mode;
        end
        WR_BUF: begin
            write_fsm_state_ns  = arc_WR_BUF_WR_MEM ? WR_MEM : WR_BUF;
            buf_wren_intt       = butterfly_ready;
            buf_rden_intt       = buf0_valid;
            incr_mem_wr_addr    = buf0_valid;
            mem_wr_en_fsm       = buf0_valid;
            wr_addr_step        = INTT_WRITE_ADDR_STEP;
        end
        WR_MEM: begin
            write_fsm_state_ns  = arc_WR_MEM_WR_BUF ? WR_BUF :
                                    arc_WR_MEM_WR_STAGE ? WR_STAGE : 
                                    arc_WR_MEM_WR_WAIT ? WR_WAIT : WR_MEM;
            buf_wren_intt       = gs_mode ;
            buf_rden_intt       = gs_mode ;
            incr_mem_wr_addr    = ct_mode ? butterfly_ready : gs_mode ? 1'b1 : 1'b0;
            mem_wr_en_fsm       = ct_mode ? butterfly_ready : gs_mode ? 1'b1 : 1'b0;
            wr_addr_step        = ct_mode ? NTT_WRITE_ADDR_STEP : INTT_WRITE_ADDR_STEP;
            incr_pw_wr_addr     = pwo_mode & butterfly_ready;
            pw_wren_fsm         = pwo_mode & butterfly_ready;
        end
        WR_WAIT: begin
            if (shuffle_en) begin
                write_fsm_state_ns  = arc_WR_WAIT_WR_STAGE ? WR_STAGE : WR_WAIT;
                wr_addr_step        = gs_mode ? INTT_WRITE_ADDR_STEP : NTT_WRITE_ADDR_STEP;
            end
            else begin
                write_fsm_state_ns  = arc_WR_WAIT_WR_STAGE ? WR_STAGE : arc_WR_WAIT_WR_MEM ? WR_MEM : WR_WAIT;
                wr_addr_step        = INTT_WRITE_ADDR_STEP;
            end
            buf_wren_intt       = shuffle_en ? 'b0 : (buf_count <= 'h3);
            buf_rden_intt       = shuffle_en ? gs_mode : 'b1;
            incr_mem_wr_addr    = (ct_mode | gs_mode);
            mem_wr_en_fsm       = shuffle_en ? gs_mode : (ct_mode | gs_mode);
            
            incr_pw_wr_addr     = shuffle_en ? pwo_mode & arc_WR_WAIT_WR_STAGE : arc_WR_WAIT_WR_MEM;
            pw_wren_fsm         = shuffle_en ? 'b0 : arc_WR_WAIT_WR_MEM;
        end
        default: begin
            write_fsm_state_ns  = WR_IDLE;
        end
    endcase
end

always_comb begin
    rst_rounds       = (read_fsm_state_ps == RD_IDLE) && (write_fsm_state_ps == WR_IDLE);
    incr_rounds      = arc_WR_MEM_WR_STAGE | arc_WR_WAIT_WR_STAGE; //TODO: revisit for high-perf mode (if we go with above opt)
    if (shuffle_en) begin
        buf_wren         = pwo_mode ? 1'b0 : buf_wren_ntt_reg | buf_wren_intt_reg;
        buf_rden         = pwo_mode ? 1'b0 : ct_mode ? buf_rden_ntt_reg : buf_rden_intt;
        bf_enable        = (gs_mode || pwo_mode) ? bf_enable_reg_d2 : bf_enable_reg; //bf_enable_fsm; //In gs mode, memory is directly feeding bf2x2, so we need to enable it one cycle later
        mem_wr_en        = gs_mode ? mem_wr_en_fsm : mem_wr_en_reg;
        mem_rd_en        = (gs_mode | pwo_mode) ? mem_rd_en_reg : mem_rd_en_fsm;
        twiddle_addr     = gs_mode ? twiddle_addr_reg_d3 : twiddle_addr_int;
        pw_rden          = pw_rden_reg;
        pw_wren          = pwm_mode ? pw_wren_reg : pw_wren_reg;
    end
    else begin
        buf_wren = pwo_mode ? 1'b0 : buf_wren_ntt_reg | buf_wren_intt;
        buf_rden = pwo_mode ? 1'b0 : buf_rden_ntt | buf_rden_intt;
        bf_enable = (gs_mode | pwo_mode) ? bf_enable_reg : bf_enable_fsm; //In gs mode, memory is directly feeding bf2x2, so we need to enable it one cycle later
        mem_wr_en = mem_wr_en_fsm;
        mem_rd_en = mem_rd_en_fsm;
        twiddle_addr = twiddle_addr_int;
        pw_rden  = pw_rden_fsm;
        pw_wren = pw_wren_fsm;
    end
    buf_wr_rst_count = pwo_mode ? 1'b1 : buf_wr_rst_count_ntt | buf_wr_rst_count_intt;
    buf_rd_rst_count = pwo_mode ? 1'b1 : buf_rd_rst_count_ntt | buf_rd_rst_count_intt;
    
    
end

always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
        buf_wren_ntt_reg <= 'b0;
        buf_wren_intt_reg <= 'b0;
        buf_rden_ntt_reg <= 'b0;
        bf_enable_reg <= 'b0;
        bf_enable_reg_d2 <= 'b0;
        mem_wr_en_reg <= 'b0;
        mem_rd_en_reg <= 'b0;
        twiddle_addr_reg_d2 <= 'h0;
        twiddle_addr_reg_d3 <= 'h0;
        pw_rden_reg <= '0;
        pw_wren_reg <= '0;
    end
    else if (zeroize) begin
        buf_wren_ntt_reg <= 'b0;
        buf_wren_intt_reg <= 'b0;
        buf_rden_ntt_reg <= 'b0;
        bf_enable_reg <= 'b0;
        bf_enable_reg_d2 <= 'b0;
        mem_wr_en_reg <= 'b0;
        mem_rd_en_reg <= 'b0;
        twiddle_addr_reg_d2 <= 'h0;
        twiddle_addr_reg_d3 <= 'h0;
        pw_rden_reg <= '0;
        pw_wren_reg <= '0;
    end
    else begin
        buf_wren_ntt_reg <= buf_wren_ntt;
        buf_wren_intt_reg <= buf_wren_intt;
        buf_rden_ntt_reg <= buf_rden_ntt;
        bf_enable_reg <= bf_enable_fsm;
        bf_enable_reg_d2 <= bf_enable_reg;
        mem_wr_en_reg <= mem_wr_en_fsm;
        mem_rd_en_reg <= mem_rd_en_fsm;
        twiddle_addr_reg_d2 <= twiddle_addr_int;
        twiddle_addr_reg_d3 <= twiddle_addr_reg_d2;
        pw_rden_reg <= pw_rden_fsm;
        pw_wren_reg <= pw_wren_fsm;
    end
end



//TODO: add assertions for:
//1. buf_wren_ntt and buf_wren_intt should be mutex

endmodule
