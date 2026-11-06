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




module fv_ntt_ctrl_ct_mlkem_additional_aips
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    import fv_ntt_ctrl_ct_mlkem_functions::*;
#(
    parameter REG_SIZE         = 23,
    parameter RADIX            = 23,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = 8,
    parameter MEM_ADDR_WIDTH   = 15
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
    input logic                      pi_mem_rd_data_valid,
    input logic                      po_bf_enable,
    input logic [2:0]                po_opcode,
    input logic                      po_buf_wren,
    input logic                      po_buf_rden,
    input logic [1:0]                po_buf_wrptr,
    input logic [1:0]                po_buf_rdptr,
    input logic [6:0]                po_twiddle_addr,
    input logic [MEM_ADDR_WIDTH-1:0] po_mem_rd_addr,
    input logic [MEM_ADDR_WIDTH-1:0] po_mem_wr_addr,
    input logic                      po_mem_rd_en,
    input logic                      po_mem_wr_en,
    input logic                      po_buf_wr_rst_count,
    input logic                      po_buf_rd_rst_count,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_a,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_b,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_c,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_wr_addr_c,
    input logic                      po_pw_rden,
    input logic                      po_pw_wren,
    input logic                      po_ntt_passthrough,
    input logic                      po_intt_passthrough,
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

    default clocking default_clk @(posedge pi_clk); endclocking

    // Keep in sync manually if SRAM_LATENCY is ever elaborated at a value other than the default (1).
    localparam SRAM_LATENCY = 1;

    // Verifies the behavior of `ntt_passthrough` in ML-KEM. `rounds_count` is modeled via SystemC.
    property ntt_passthrough_p;
        ##0 po_ntt_passthrough == (ntt_ctrl.rounds_count == (NTT_NUM_ROUNDS-1))
    ;endproperty
    assert_ntt_passthrough_a: assert property (disable iff (!pi_reset_n || pi_zeroize) ntt_passthrough_p);

    // `intt_passthrough` is GS-only
    property intt_passthrough_p;
        ##0 po_intt_passthrough == 1'b0
    ;endproperty
    assert_intt_passthrough_a: assert property (disable iff (!pi_reset_n || pi_zeroize) intt_passthrough_p);

    // Verifies the combinational behavior of the `bf_enable`. Signal `bf_enable_reg[0]` is `bf_enable_fsm` delayed one cycle and is already verified in the SystemC model. This property ensures that the combinational behavior of the output depending on `shuffle_en` is actually followed.
    logic fv_bf_enable;
    assign fv_bf_enable = pi_shuffle_en ? ntt_ctrl.bf_enable_reg[0] : ntt_ctrl.bf_enable_fsm;
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
        ##0 po_buf_wr_rst_count == (ntt_ctrl.read_fsm_state_ps == RD_IDLE || ntt_ctrl.read_fsm_state_ps == RD_STAGE || ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)
    ;endproperty
    assert_buf_wr_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wr_rst_count_p);

    // Verifies `buf_rd_rst_count` behavior
    property buf_rd_rst_count_p;
        ##0 po_buf_rd_rst_count == (ntt_ctrl.read_fsm_state_ps == RD_IDLE || ntt_ctrl.read_fsm_state_ps == RD_STAGE)
    ;endproperty
    assert_buf_rd_rst_count_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rd_rst_count_p);

    // Verifies `buf_wren`: buffer writes depend on the state and data valid
    property buf_wren_p;
        ##0 po_buf_wren == (
            ntt_ctrl.read_fsm_state_ps == EXEC_WAIT
            || (ntt_ctrl.read_fsm_state_ps == RD_BUF || ntt_ctrl.read_fsm_state_ps == RD_EXEC) && pi_mem_rd_data_valid
        )
    ;endproperty
    assert_buf_wren_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wren_p);

    // Buffer writes are in order
    property buf_wr_ptr_check_p;
        ##0 po_buf_wren
    |->
        ##1 po_buf_wrptr == 2'($past(po_buf_wrptr, 1) + 1)
    ;endproperty
    assert_buf_wr_ptr_check_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wr_ptr_check_p);

    // `buf_wrptr` holds steady when not writing
    property buf_wr_ptr_hold_p;
        ##0 !po_buf_wren
    |->
        ##1 $stable(po_buf_wrptr)
    ;endproperty
    assert_buf_wr_ptr_hold_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_wr_ptr_hold_p);

    // Similar to `assert_bf_enable_a`, this verifies the combinational behavior of the `buf_rden`. `buf_rden_ntt_reg` is `buf_rden_ntt` delayed, which has been modeled via SystemC.
    logic fv_buf_rden;
    assign fv_buf_rden = pi_shuffle_en ? ntt_ctrl.buf_rden_ntt_reg : ntt_ctrl.buf_rden_ntt;
    property buf_rd_en_p;
        ##1 po_buf_rden == fv_buf_rden
    ;endproperty
    assert_buf_rd_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rd_en_p);

    // Verifies the behavior of `buf_rdptr`. It follows `buf_rdptr_f` (modeled via SystemC) when shuffling; `buf_count` (modeled via SystemC) otherwise.
    logic [2:0] fv_buf_rdptr;
    assign fv_buf_rdptr = pi_shuffle_en ? ntt_ctrl.buf_rdptr_f : ntt_ctrl.buf_count;
    property buf_rdptr_p;
        ##0 po_buf_rdptr == fv_buf_rdptr
    ;endproperty
    assert_buf_rdptr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) buf_rdptr_p);

    // Verifies the combinational behavior of `twiddle_addr`. `twiddle_addr_int` is the actual register verified in the SystemC model, while `twiddle_addr_reg[0]` is the combinational function `twiddle_addr_int + twiddle_offset(rounds_count)` that this property verifies directly. This also relies on the correctness of `rounds_count`, which is fine because it has been modeled via SystemC.
    logic [6:0] fv_twiddle_addr_reg0;
    assign fv_twiddle_addr_reg0 = ntt_ctrl.twiddle_addr_int + twiddle_offset(ntt_ctrl.rounds_count);
    property twiddle_addr_p;
        ##0 po_twiddle_addr == fv_twiddle_addr_reg0
    ;endproperty
    assert_twiddle_addr_a: assert property (disable iff (!pi_reset_n || pi_zeroize) twiddle_addr_p);

    // Verifies the other entries of `twiddle_addr_reg` (`twiddle_addr_reg[0]` is modeled in this file)
    property twiddle_addr_reg_p;
        ##1 ntt_ctrl.twiddle_addr_reg[SRAM_LATENCY+1:1] == $past(ntt_ctrl.twiddle_addr_reg[SRAM_LATENCY:0])
    ;endproperty
    assert_twiddle_addr_reg_a: assert property (disable iff (!pi_reset_n || pi_zeroize) twiddle_addr_reg_p);

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

    // Verifies the behavior of the `mem_rd_en` output. `mem_read_req_port` (bound to `mem_rd_en_reg`) is already indirectly modeling `mem_rd_en_fsm`.
    property mem_rd_en_p;
        ##0 po_mem_rd_en == ntt_ctrl.mem_rd_en_fsm
    ;endproperty
    assert_mem_rd_en_a: assert property(disable iff (!pi_reset_n || pi_zeroize) mem_rd_en_p);

    // Verifies the behavior of the `mem_wr_en` output. `mem_write_req_port` (bound to `mem_wr_en_reg`) models both `mem_wr_en_reg` and `mem_wr_en_fsm` (indirectly).
    logic fv_mem_wr_en;
    assign fv_mem_wr_en = pi_shuffle_en ? ntt_ctrl.mem_wr_en_reg : ntt_ctrl.mem_wr_en_fsm;
    property mem_wr_en_p;
        ##0 po_mem_wr_en == fv_mem_wr_en
    ;endproperty
    assert_mem_wr_en_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_wr_en_p);

    // This property is a legacy re-derivation of `mem_rd_en`, but independent of the SystemC model. Even though it is redundant, it is kept for robustness.
    logic fv_mem_rd_en_1;
    logic fv_mem_rd_en_2;
    assign fv_mem_rd_en_1 =
        ((po_mem_rd_addr <= 63 + ntt_ctrl.mem_rd_base_addr) && !((ntt_ctrl.buf_count == 3) && (ntt_ctrl.rd_valid_count == 60))) ? 1 : 0;
    assign fv_mem_rd_en_2 =
        ((ntt_ctrl.read_fsm_state_ps == RD_STAGE) || ((ntt_ctrl.read_fsm_state_ps == EXEC_WAIT) || (ntt_ctrl.read_fsm_state_ps == RD_IDLE))) ?
            0
            : ((ntt_ctrl.read_fsm_state_ps == RD_BUF) || (ntt_ctrl.read_fsm_state_ps == RD_EXEC)) && fv_mem_rd_en_1;
    property mem_rd_en_exec_p;
        ##0 po_mem_rd_en == fv_mem_rd_en_2
    ;endproperty
    assert_mem_rd_en_exec_a: assert property (disable iff (!pi_reset_n || pi_zeroize) mem_rd_en_exec_p);

    // Safety: reads from and writes to the same address are not allowed
    property not_same_address_p;
        ##0 ntt_ctrl.mem_rd_en && ntt_ctrl.mem_wr_en
    |->
        ##0 ntt_ctrl.mem_rd_addr != ntt_ctrl.mem_wr_addr
    ;endproperty
    assert_not_same_address_a: assert property (disable iff (!pi_reset_n || pi_zeroize) not_same_address_p);

    // Verifies `busy` behavior
    property busy_p;
        ##0 po_busy == (ntt_ctrl.read_fsm_state_ps != RD_IDLE && ntt_ctrl.write_fsm_state_ps != WR_IDLE)
    ;endproperty
    assert_busy_a: assert property(disable iff (!pi_reset_n || pi_zeroize) busy_p);

    // Verifies `done` behavior. `rounds_count` has been modeled via SystemC.
    property ntt_done_p;
        ##0 ntt_ctrl.ntt_done == (ntt_ctrl.rounds_count == NTT_NUM_ROUNDS)
    ;endproperty
    assert_ntt_done_a: assert property (disable iff (!pi_reset_n || pi_zeroize) ntt_done_p);

    // Latch `index_rand_offset` on every 4th buffer write
    property latch_index_rand_offset_p;
        ##0 ntt_ctrl.latch_index_rand_offset == (po_buf_wrptr == 3)
    ;endproperty
    assert_latch_index_rand_offset_a: assert property (disable iff (!pi_reset_n || pi_zeroize) latch_index_rand_offset_p);

    // Latches `chunk_rand_offset` before each round. CT mode rounds end through WR_MEM -> WR_STAGE; `arc_IDLE_WR_STAGE` ensures it for the very first round. Reconstructs both arcs from the RTL conditions.
    logic fv_arc_idle_wr_stage;
    logic fv_arc_wr_mem_wr_stage;
    assign fv_arc_idle_wr_stage = (ntt_ctrl.write_fsm_state_ps == WR_IDLE) && pi_ntt_enable;
    assign fv_arc_wr_mem_wr_stage = (ntt_ctrl.write_fsm_state_ps == WR_MEM) && (ntt_ctrl.wr_valid_count == ((MLDSA_N/COEFF_PER_CLK)-1));
    property latch_chunk_rand_offset_p;
        ##0 ntt_ctrl.latch_chunk_rand_offset == (fv_arc_idle_wr_stage || fv_arc_wr_mem_wr_stage)
    ;endproperty
    assert_latch_chunk_rand_offset_a: assert property (disable iff (!pi_reset_n || pi_zeroize) latch_chunk_rand_offset_p);

    // Verifies `rst_rounds` behavior
    property rst_rounds_p;
        ##0 ntt_ctrl.rst_rounds == (ntt_ctrl.read_fsm_state_ps == RD_IDLE && ntt_ctrl.write_fsm_state_ps == WR_IDLE)
    ;endproperty
    assert_rst_rounds_a: assert property (disable iff (!pi_reset_n || pi_zeroize) rst_rounds_p);

endmodule

bind ntt_ctrl fv_ntt_ctrl_ct_mlkem_additional_aips ct_mlkem_additional_aip_inst (
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
    .po_ntt_passthrough (ntt_passthrough),
    .po_intt_passthrough (intt_passthrough),
    .po_busy (busy),
    .po_done (done)
);
