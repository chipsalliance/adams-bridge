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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_ntt_ctrl_pwo_additional_properties

    import ntt_defines_pkg::*;

#(
    parameter REG_SIZE         = 23,
    parameter RADIX            = 23,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = 8,
    parameter MEM_ADDR_WIDTH   = 15,
    parameter LATENCY = 1
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input mode_t                     pi_ntt_mode,
    input                            pi_ntt_enable,
    input                            pi_butterfly_ready,
    input                            pi_buf0_valid,
    input                            pi_sampler_valid,
    input                            pi_accumulate,
    input ntt_mem_addr_t             pi_ntt_mem_base_addr,
    input pwo_mem_addr_t             pi_pwo_mem_base_addr,
    input                            pi_shuffle_en,
    input [5:0]                      pi_random,
    input logic                      po_bf_enable,
    input logic [2:0]                po_opcode,
    input logic                      po_buf_wren,
    input logic                      po_buf_rden,
    input logic [1:0]                po_buf_wrptr,
    input logic [1:0]                po_buf_rdptr,
    input logic [6:0]                po_twiddle_addr,
    input logic [14:0] po_mem_rd_addr,
    input logic [14:0] po_mem_wr_addr,
    input logic                      po_mem_rd_en,
    input logic                      po_mem_wr_en,
    input logic                      po_buf_wr_rst_count,
    input logic                      po_buf_rd_rst_count,
    input logic [14:0] po_pw_mem_rd_addr_a,
    input logic [14:0] po_pw_mem_rd_addr_b,
    input logic [14:0] po_pw_mem_rd_addr_c,
    input logic [14:0] po_pw_mem_wr_addr_c,
    input logic                      po_pw_rden,
    input logic                      po_pw_wren,
    input logic                      po_pw_rden_dest_mem,
    input logic                      po_busy,
    input logic                      po_done
    //$#//
);

    //#$localparams
    localparam NTT_NUM_ROUNDS = 4;
    localparam PWO_NUM_ROUNDS = 1;
    localparam NTT_READ_ADDR_STEP = 16;
    localparam NTT_WRITE_ADDR_STEP = 1;
    localparam INTT_READ_ADDR_STEP = 1;
    localparam INTT_WRITE_ADDR_STEP = 16;
    localparam PWO_READ_ADDR_STEP = 1;
    localparam PWO_WRITE_ADDR_STEP = 1;
    localparam MEM_LAST_ADDR = 63;
    //$#//
/////////////////////////////////////////////
    default clocking default_clk @(posedge pi_clk); endclocking


    property assert_bf_enable_p;
        po_bf_enable == (pi_shuffle_en ? ntt_ctrl.bf_enable_reg[LATENCY] : ntt_ctrl.bf_enable_reg[LATENCY-1]);
    endproperty
    assert_bf_enable_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_bf_enable_p);


    property assert_twiddle_addr_p;
        po_twiddle_addr == (pi_shuffle_en
            ? (ntt_ctrl.pairwm_mode ? ntt_ctrl.twiddle_addr_reg[LATENCY+1] : ntt_ctrl.twiddle_addr_reg[0])
            : (ntt_ctrl.pairwm_mode ? ntt_ctrl.twiddle_addr_reg[LATENCY-1] : ntt_ctrl.twiddle_addr_reg[0]));
    endproperty
    assert_twiddle_addr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_twiddle_addr_p);


    property assert_pw_rden_p;
        po_pw_rden == (pi_shuffle_en
            ? ntt_ctrl.pw_rden_reg
            : (pi_sampler_valid && (ntt_ctrl.read_fsm_state_ps == RD_EXEC || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)));
    endproperty
    assert_pw_rden_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_pw_rden_p);

    property assert_pw_rden_dest_mem_p;
        po_pw_rden_dest_mem == (pi_accumulate
            ? (pi_shuffle_en
                ? ntt_ctrl.pw_rden_reg
                : (pi_sampler_valid && (ntt_ctrl.read_fsm_state_ps == RD_EXEC || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)))
            : 1'b0);
    endproperty
    assert_pw_rden_dest_mem_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_pw_rden_dest_mem_p);
    property assert_pw_wren_p;
        po_pw_wren == (pi_shuffle_en
            ? ntt_ctrl.pw_wren_reg
            : (pi_butterfly_ready && (ntt_ctrl.write_fsm_state_ps == WR_MEM || ntt_ctrl.write_fsm_state_ps == WR_WAIT)));
    endproperty
    assert_pw_wren_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_pw_wren_p);


    property assert_busy_p;
        po_busy == (ntt_ctrl.read_fsm_state_ps != RD_IDLE && ntt_ctrl.write_fsm_state_ps != WR_IDLE);
    endproperty
    assert_busy_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_busy_p);


    property assert_rst_rounds_p;
        ntt_ctrl.rst_rounds == (ntt_ctrl.read_fsm_state_ps == RD_IDLE && ntt_ctrl.write_fsm_state_ps == WR_IDLE);
    endproperty
    assert_rst_rounds_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_rst_rounds_p);


    property assert_buf_wren_p;
        po_buf_wren == 1'b0;
    endproperty
    assert_buf_wren_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_wren_p);

    property assert_buf_rden_p;
        po_buf_rden == 1'b0;
    endproperty
    assert_buf_rden_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_rden_p);

    property assert_buf_wrptr_p;
        po_buf_wrptr == 2'd0;
    endproperty
    assert_buf_wrptr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_wrptr_p);

    property assert_buf_rdptr_p;
        po_buf_rdptr == 2'd0;
    endproperty
    assert_buf_rdptr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_rdptr_p);

    property assert_mem_rd_en_p;
        po_mem_rd_en == 1'b0;
    endproperty
    assert_mem_rd_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_mem_rd_en_p);

    property assert_mem_wr_en_p;
        po_mem_wr_en == 1'b0;
    endproperty
    assert_mem_wr_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_mem_wr_en_p);

    property assert_buf_wr_rst_count_p;
        po_buf_wr_rst_count == 1'b1;
    endproperty
    assert_buf_wr_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_wr_rst_count_p);

    property assert_buf_rd_rst_count_p;
        po_buf_rd_rst_count == 1'b1;
    endproperty
    assert_buf_rd_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) assert_buf_rd_rst_count_p);


endmodule




bind ntt_ctrl fv_ntt_ctrl_pwo_additional_properties #(.LATENCY(SRAM_LATENCY))additional_inst (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_ntt_mode (ntt_mode),
    .pi_ntt_enable (ntt_enable),
    .pi_butterfly_ready (butterfly_ready),
    .pi_buf0_valid (buf0_valid),
    .pi_sampler_valid (sampler_valid),
    .pi_accumulate (accumulate),
    .pi_ntt_mem_base_addr (ntt_mem_base_addr),
    .pi_pwo_mem_base_addr (pwo_mem_base_addr),
    .pi_shuffle_en (shuffle_en),
    .pi_random (random),
    .po_bf_enable (bf_enable),
    .po_opcode (opcode),
    .po_buf_wren (buf_wren),
    .po_buf_rden (buf_rden),
    .po_buf_wrptr (buf_wrptr),
    .po_buf_rdptr (buf_rdptr),
    .po_twiddle_addr (twiddle_addr),
    .po_mem_rd_addr (mem_rd_addr),
    .po_mem_wr_addr (mem_wr_addr),
    .po_mem_rd_en (mem_rd_en),
    .po_mem_wr_en (mem_wr_en),
    .po_buf_wr_rst_count (buf_wr_rst_count),
    .po_buf_rd_rst_count (buf_rd_rst_count),
    .po_pw_mem_rd_addr_a (pw_mem_rd_addr_a),
    .po_pw_mem_rd_addr_b (pw_mem_rd_addr_b),
    .po_pw_mem_rd_addr_c (pw_mem_rd_addr_c),
    .po_pw_mem_wr_addr_c (pw_mem_wr_addr_c),
    .po_pw_rden (pw_rden),
    .po_pw_wren (pw_wren),
    .po_pw_rden_dest_mem(pw_rden_dest_mem),
    .po_busy (busy),
    .po_done (done)
);
