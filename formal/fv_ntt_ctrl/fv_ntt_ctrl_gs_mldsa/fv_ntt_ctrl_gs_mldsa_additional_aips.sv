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

module fv_ntt_ctrl_gs_mldsa_additional_aips
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
) (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input mode_t                            pi_ntt_mode,
    input                                   pi_ntt_enable,
    input                                   pi_butterfly_ready,
    input                                   pi_buf0_valid,
    input                                   pi_sampler_valid,
    input                                   pi_accumulate,
    input ntt_mem_addr_t                    pi_ntt_mem_base_addr,
    input pwo_mem_addr_t                    pi_pwo_mem_base_addr,
    input                                   pi_shuffle_en,
    input [5:0]                             pi_random,
    input logic                             pi_mem_rd_data_valid,
    input logic                             po_bf_enable,
    input logic [2:0]                       po_opcode,
    input logic                             po_buf_wren,
    input logic                             po_buf_rden,
    input logic [1:0]                       po_buf_wrptr,
    input logic [1:0]                       po_buf_rdptr,
    input logic [6:0]                       po_twiddle_addr,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_mem_rd_addr,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_mem_wr_addr,
    input logic                             po_mem_rd_en,
    input logic                             po_mem_wr_en,
    input logic                             po_buf_wr_rst_count,
    input logic                             po_buf_rd_rst_count,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_pw_mem_rd_addr_a,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_pw_mem_rd_addr_b,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_pw_mem_rd_addr_c,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_pw_mem_wr_addr_c,
    input logic                             po_pw_rden,
    input logic                             po_pw_wren,
    input logic                             po_busy,
    input logic                             po_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    // Keep in sync manually if SRAM_LATENCY is ever elaborated at a value other than the default (1).
    localparam SRAM_LATENCY = 1;

    localparam NTT_NUM_ROUNDS = 4;

    // Verifies the combinational behavior of the `bf_enable`. Signal `bf_enable_reg` is already indirectly verified in the SystemC model. This property ensures that the combinational behavior of the output depending on `shuffle_en` is actually followed.
    logic fv_bf_enable;
    assign fv_bf_enable = pi_shuffle_en ? ntt_ctrl.bf_enable_reg[SRAM_LATENCY] : ntt_ctrl.bf_enable_reg[SRAM_LATENCY-1];
    property bf_enable_p;
        ##0 po_bf_enable == fv_bf_enable
    ;endproperty
    assert_bf_enable_a: assert property (disable iff (!pi_reset_n || pi_zeroize) bf_enable_p);

    // Verifies the other entries of `bf_enable_reg` (`bf_enable_reg[0]` is modeled via SystemC)
    property bf_enable_reg_p;
        ##1 ntt_ctrl.bf_enable_reg[SRAM_LATENCY+1:1] == $past(ntt_ctrl.bf_enable_reg[SRAM_LATENCY:0])
    ;endproperty
    assert_bf_enable_reg_a: assert property (disable iff (!pi_reset_n || pi_zeroize) bf_enable_reg_p);

    // Verifies `buf_wr_rst_count` behavior
    property buf_wr_rst_count_p;
        ##0 po_buf_wr_rst_count == ((ntt_ctrl.read_fsm_state_ps == RD_IDLE) || (ntt_ctrl.read_fsm_state_ps == EXEC_WAIT) || (ntt_ctrl.write_fsm_state_ps == WR_STAGE))
    ;endproperty
    assert_buf_wr_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wr_rst_count_p);

    // Verifies `buf_rd_rst_count` behavior
    property buf_rd_rst_count_p;
        ##0 po_buf_rd_rst_count == ((ntt_ctrl.read_fsm_state_ps == RD_IDLE) || (ntt_ctrl.write_fsm_state_ps == WR_STAGE))
    ;endproperty
    assert_buf_rd_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rd_rst_count_p);

    // Verifies `buf_wren`: buffer writes depend on the write FSM state and `butterfly_ready`/`buf_count`, or the registered `buf_wren_intt_reg` when shuffling.
    property buf_wren_p;
        ##0 po_buf_wren == (pi_shuffle_en
            ? ntt_ctrl.buf_wren_intt_reg
            : ((ntt_ctrl.write_fsm_state_ps == WR_BUF && pi_butterfly_ready)
                || (ntt_ctrl.write_fsm_state_ps == WR_MEM)
                || (ntt_ctrl.write_fsm_state_ps == WR_WAIT && ntt_ctrl.buf_count <= 3)))
    ;endproperty
    assert_buf_wren_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wren_p);

    // Verifies that `buf_wren_intt_reg` is the non-shuffled `buf_wren` delayed one cycle
    property buf_wren_intt_reg_p;
        ##1 ntt_ctrl.buf_wren_intt_reg == $past((ntt_ctrl.write_fsm_state_ps == WR_BUF && pi_butterfly_ready)
            || (ntt_ctrl.write_fsm_state_ps == WR_MEM)
            || (ntt_ctrl.write_fsm_state_ps == WR_WAIT && !pi_shuffle_en && ntt_ctrl.buf_count <= 3))
    ;endproperty
    assert_buf_wren_intt_reg_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wren_intt_reg_p);

    // Buffer writes are in order when not shuffling. `buf_wrptr` is already modeled via SystemC.
    property buf_wr_ptr_check_p;
        ##0 (po_buf_wren && !pi_shuffle_en)
    |->
        ##1 po_buf_wrptr == 2'($past(po_buf_wrptr, 1) + 1)
    ;endproperty
    assert_buf_wr_ptr_check_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wr_ptr_check_p);

    // Verifies `buf_rden` behavior
    property buf_rd_en_p;
        ##0 po_buf_rden == ((ntt_ctrl.write_fsm_state_ps == WR_BUF && pi_buf0_valid)
            || (ntt_ctrl.write_fsm_state_ps == WR_MEM)
            || (ntt_ctrl.write_fsm_state_ps == WR_WAIT))
    ;endproperty
    assert_buf_rd_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rd_en_p);

    // GS mode buffer reads follow `buf_count`. `buf_rdptr` is already modeled via SystemC.
    property buf_rdptr_p;
        ##0 po_buf_rdptr == ntt_ctrl.buf_count
    ;endproperty
    assert_buf_rdptr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rdptr_p);

    // Verifies the combinational behavior of `twiddle_addr`. `twiddle_addr_int` is the actual register verified in the SystemC model, while `fv_twiddle_addr_reg0` is the combinational function this property verifies directly when not shuffling; `twiddle_addr_reg[2]` is used instead when shuffling. This also relies on the correctness of `rounds_count`, which is fine because it has been modeled via SystemC.
    logic [7:0][6:0] fv_twiddle_offsets;
    assign fv_twiddle_offsets = '{
        0: 7'd0,
        1: 7'd64,
        2: 7'd80,
        3: 7'd84,
        4: 7'd0,
        5: 7'd0,
        6: 7'd0,
        7: 7'd0
    };

    logic [6:0] fv_twiddle_addr_reg0;
    assign fv_twiddle_addr_reg0 = ntt_ctrl.twiddle_addr_int + fv_twiddle_offsets[ntt_ctrl.rounds_count];
    property twiddle_addr_p;
        ##0 po_twiddle_addr == (pi_shuffle_en ? ntt_ctrl.twiddle_addr_reg[2] : fv_twiddle_addr_reg0)
    ;endproperty
    assert_twiddle_addr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) twiddle_addr_p);

    // Verifies `mem_rd_base_addr` behavior. `rounds_count` has been modeled via SystemC.
    property mem_rd_base_addr_p;
        ##0 ntt_ctrl.mem_rd_base_addr == ((ntt_ctrl.rounds_count == '0) ? pi_ntt_mem_base_addr.src_base_addr : ntt_ctrl.rounds_count[0] ? pi_ntt_mem_base_addr.interim_base_addr : pi_ntt_mem_base_addr.dest_base_addr)
    ;endproperty
    assert_mem_rd_base_addr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_rd_base_addr_p);

    // Verifies `mem_wr_base_addr` behavior. `rounds_count` has been modeled via SystemC.
    property mem_wr_base_addr_p;
        ##0 ntt_ctrl.mem_wr_base_addr == (ntt_ctrl.rounds_count[0] ? pi_ntt_mem_base_addr.dest_base_addr : pi_ntt_mem_base_addr.interim_base_addr)
    ;endproperty
    assert_mem_wr_base_addr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_wr_base_addr_p);

    // Verifies the behavior of the `mem_rd_en` output. `mem_rd_en_reg` (modeled via SystemC) is used when shuffling.
    property mem_rd_en_p;
        ##0 po_mem_rd_en == (pi_shuffle_en
            ? ntt_ctrl.mem_rd_en_reg
            : (ntt_ctrl.read_fsm_state_ps == RD_EXEC && po_mem_rd_addr <= ntt_ctrl.mem_rd_base_addr + 63))
    ;endproperty
    assert_mem_rd_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_rd_en_p);

    // Verifies `mem_wr_en` behavior
    property mem_wr_en_p;
        ##0 po_mem_wr_en == ((ntt_ctrl.write_fsm_state_ps == WR_BUF && pi_buf0_valid)
            || (ntt_ctrl.write_fsm_state_ps == WR_MEM)
            || (ntt_ctrl.write_fsm_state_ps == WR_WAIT))
    ;endproperty
    assert_mem_wr_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_wr_en_p);

    // Safety: reads from and writes to the same address are not allowed
    property not_same_address_p;
        ##0 (ntt_ctrl.mem_rd_en && ntt_ctrl.mem_wr_en)
    |->
        ##0 (ntt_ctrl.mem_rd_addr != ntt_ctrl.mem_wr_addr)
    ;endproperty
    assert_not_same_address_a: assert property (disable iff (!pi_reset_n || pi_zeroize) not_same_address_p);

    // Verifies `busy` behavior
    property busy_p;
        ##0 po_busy == ((ntt_ctrl.read_fsm_state_ps != RD_IDLE) && (ntt_ctrl.write_fsm_state_ps != WR_IDLE))
    ;endproperty
    assert_busy_a: assert property(disable iff (!pi_reset_n || pi_zeroize) busy_p);

    // Verifies `intt_done` behavior. `rounds_count` has been modeled via SystemC.
    property intt_done_p;
        ##0 ntt_ctrl.intt_done == (ntt_ctrl.rounds_count == NTT_NUM_ROUNDS)
    ;endproperty
    assert_intt_done_a: assert property (disable iff (!pi_reset_n || pi_zeroize) intt_done_p);

    // Reconstructs the RD_STAGE -> RD_EXEC, IDLE -> WR_STAGE, and WR_WAIT -> WR_STAGE arcs. Used below by `latch_index_rand_offset_p` and `latch_chunk_rand_offset_p`.
    logic fv_arc_idle_wr_stage;
    logic fv_arc_rd_stage_rd_exec;
    logic fv_arc_wr_wait_wr_stage;
    assign fv_arc_idle_wr_stage = (ntt_ctrl.write_fsm_state_ps == WR_IDLE) && pi_ntt_enable;
    assign fv_arc_rd_stage_rd_exec = (ntt_ctrl.read_fsm_state_ps == RD_STAGE) && (ntt_ctrl.write_fsm_state_ps == WR_STAGE) && !ntt_ctrl.intt_done;
    assign fv_arc_wr_wait_wr_stage = (ntt_ctrl.write_fsm_state_ps == WR_WAIT) && (ntt_ctrl.buf_count == (COEFF_PER_CLK-1));

    // Latch `index_rand_offset` on the RD_STAGE -> RD_EXEC arc or every 4th index
    property latch_index_rand_offset_p;
        ##0 ntt_ctrl.latch_index_rand_offset == (fv_arc_rd_stage_rd_exec || ntt_ctrl.index_count == 3)
    ;endproperty
    assert_latch_index_rand_offset_a: assert property (disable iff (!pi_reset_n || pi_zeroize) latch_index_rand_offset_p);

    // Latches `chunk_rand_offset` before each round. GS mode rounds end through WR_WAIT -> WR_STAGE; `arc_IDLE_WR_STAGE` ensures it for the very first round.
    property latch_chunk_rand_offset_p;
        ##0 ntt_ctrl.latch_chunk_rand_offset == (fv_arc_idle_wr_stage || fv_arc_wr_wait_wr_stage)
    ;endproperty
    assert_latch_chunk_rand_offset_a: assert property (disable iff (!pi_reset_n || pi_zeroize) latch_chunk_rand_offset_p);

    // Verifies `rst_rounds` behavior
    property rst_rounds_p;
        ##0 ntt_ctrl.rst_rounds == ((ntt_ctrl.read_fsm_state_ps == RD_IDLE) && (ntt_ctrl.write_fsm_state_ps == WR_IDLE))
    ;endproperty
    assert_rst_rounds_a: assert property (disable iff (!pi_reset_n || pi_zeroize) rst_rounds_p);

endmodule

bind ntt_ctrl fv_ntt_ctrl_gs_mldsa_additional_aips gs_mldsa_additional_aip_inst (
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
    .pi_mem_rd_data_valid (mem_rd_data_valid),
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
    .po_busy (busy),
    .po_done (done)
);
