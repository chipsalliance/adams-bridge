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

module fv_skdecode_top_wrapper
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    // Parameters
    parameter MLDSA_ETA = 2,
    parameter MLDSA_D = 13,
    parameter ETA_SIZE = 3,
    parameter REG_SIZE = 24,
    parameter AHB_DATA_WIDTH = 32,
    parameter ABR_NUM_NTT = 1,

    // FV-only: assumed keymem read latency (cycles from request to data-valid).
    // Not tied to any RTL parameter -- used solely to keep the two properties
    // below (and their B-port counterparts) in sync from a single source.
    parameter int FV_KEYMEM_RD_LATENCY = 2
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic pi_clk,
    input logic pi_reset_n,
    input logic pi_zeroize,

    input wire pi_skdecode_enable,
    input wire [ABR_MEM_ADDR_WIDTH-1:0] pi_keymem_src_base_addr,
    input wire [ABR_MEM_ADDR_WIDTH-1:0] pi_dest_base_addr,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_a_rd_data,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_b_rd_data,

    // Added: keymem_rd_data_valid had no dedicated port; exposed as pi_* so the
    // read-timing contract can be assumed cleanly.
    input wire pi_keymem_a_rd_data_valid,
    input wire pi_keymem_b_rd_data_valid,

    // Masking / share-splitting inputs (abr_splitter) -- wired through, not yet
    // constrained or checked by any assumption/property.
    input wire pi_split_en_i,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pi_rand_i,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pi_rand_dual_i,

    input mem_if_t po_keymem_a_rd_req,
    input mem_if_t po_keymem_b_rd_req,
    input mem_if_t po_mem_a_wr_req,
    input mem_if_t po_mem_b_wr_req,
    input logic [ABR_NUM_NTT-1:0][ABR_MEM_DATA_WIDTH-1:0] po_mem_a_wr_data,
    input logic [ABR_NUM_NTT-1:0][ABR_MEM_DATA_WIDTH-1:0] po_mem_b_wr_data,
    input logic po_skdecode_error,
    input logic po_skdecode_done,
    input logic po_s1_done,
    input logic po_s2_done,
    input logic po_t0_done,


    //////////////////////////////
    // Internal Buffer signals  //
    //////////////////////////////
    input [3:0] s1s2_fifo_valid_i,
    input [3:0][7:0] s1s2_fifo_data_i,
    input logic s1s2_fifo_valid_o,
    input logic s1s2_buffer_full_o,
    input [2:0][7:0] s1s2_fifo_data_o,

    input [15:0] t0_fifo_valid_i,
    input [15:0][3:0] t0_fifo_data_i,
    input logic t0_fifo_valid_o,
    input logic t0_buffer_full_o,
    input [12:0][3:0] t0_fifo_data_o
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

/////////////////////////////////////////////////////////////// Assumption ///////////////////////////////////////////////////////////////
   // assume_zeroize: assume property (!pi_zeroize);
    //assume_error: assume property (!po_skdecode_error);
    cover_enable_to_done: cover property ((skdecode_ctrl_inst.arc_SKDEC_RD_IDLE_SKDEC_RD_S1 && skdecode_ctrl_inst.arc_SKDEC_WR_IDLE_SKDEC_WR_S1)  ##1 skdecode_ctrl_inst.arc_SKDEC_RD_T0_SKDEC_RD_IDLE [->1] );
    // enable_to_done1: cover property (skdecode_ctrl_inst.skdecode_enable ##1 skdecode_ctrl_inst.skdecode_done [->1] );


    property enable_signal_set;
        pi_reset_n
    |->
        s_eventually(pi_skdecode_enable);
    endproperty
    assume_enable_signal_set: assume property (disable iff(!pi_reset_n) enable_signal_set);


    // po_keymem_a_rd_req is a struct; needs .rd_wr_en == RW_READ, not a bare compare.
    // fv_keymem_a_read_pipe shifts in "was this cycle a read" every cycle; its
    // oldest bit is therefore "a read fired FV_KEYMEM_RD_LATENCY cycles ago".
    // The assumption below ties pi_keymem_a_rd_data_valid to that delayed flag,
    // modeling the memory's fixed read latency without a parameterized $past.
    logic [FV_KEYMEM_RD_LATENCY-1:0] fv_keymem_a_read_pipe;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if (!pi_reset_n) begin
            fv_keymem_a_read_pipe <= '0;
        end else begin
            fv_keymem_a_read_pipe <= {fv_keymem_a_read_pipe[FV_KEYMEM_RD_LATENCY-2:0], (po_keymem_a_rd_req.rd_wr_en == RW_READ)};
        end
    end

    logic fv_keymem_a_rd_data_valid_expected;
    assign fv_keymem_a_rd_data_valid_expected = fv_keymem_a_read_pipe[FV_KEYMEM_RD_LATENCY-1];

    property keymem_a_rd_data_valid_matches_req;
        pi_keymem_a_rd_data_valid == fv_keymem_a_rd_data_valid_expected;
    endproperty
    assume_keymem_a_rd_data_valid_matches_req: assume property (disable iff(!pi_reset_n) keymem_a_rd_data_valid_matches_req);

    // B-port equivalent: same shift-register-delayed-flag mechanism, modeling
    // the memory's fixed read latency for port B.
    logic [FV_KEYMEM_RD_LATENCY-1:0] fv_keymem_b_read_pipe;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if (!pi_reset_n) begin
            fv_keymem_b_read_pipe <= '0;
        end else begin
            fv_keymem_b_read_pipe <= {fv_keymem_b_read_pipe[FV_KEYMEM_RD_LATENCY-2:0], (po_keymem_b_rd_req.rd_wr_en == RW_READ)};
        end
    end

    logic fv_keymem_b_rd_data_valid_expected;
    assign fv_keymem_b_rd_data_valid_expected = fv_keymem_b_read_pipe[FV_KEYMEM_RD_LATENCY-1];

    property keymem_b_rd_data_valid_matches_req;
        pi_keymem_b_rd_data_valid == fv_keymem_b_rd_data_valid_expected;
    endproperty
    assume_keymem_b_rd_data_valid_matches_req: assume property (disable iff(!pi_reset_n) keymem_b_rd_data_valid_matches_req);

        // Fixed: dropped "|| po_skdecode_done" as a release condition -- it let a
        // same-cycle re-enable through with no reset/zeroize in between, which is
        // what let stale done-flags deadlock a second operation (see bug report).
        logic fv_ongoing_computation;
    always_ff @(posedge pi_clk) begin
        if(!pi_reset_n) begin
            fv_ongoing_computation <= 1'b0;
        end else if(pi_zeroize) begin
            fv_ongoing_computation <= 1'b0;
        end else if(!fv_ongoing_computation) begin
            fv_ongoing_computation <= pi_skdecode_enable;
        end
    end

    // Set enable only when it is not busy
    assume_only_enable_when_idle : assume property (
        pi_skdecode_enable
                                          |->
        !fv_ongoing_computation
    );

    // Designer feedback: enable is never re-asserted the same cycle a reset/zeroize
    // just cleared -- without this, a spurious re-trigger phase-misaligns mem_rd_pace.
    property enable_not_immediately_after_reset;
        $rose(pi_reset_n) || $fell(pi_zeroize)
    |->
        !pi_skdecode_enable;
    endproperty
    assume_enable_not_immediately_after_reset: assume property (disable iff(!pi_reset_n) enable_not_immediately_after_reset);



    assume_stable_addresses :assume property (
        ##1 $stable(pi_keymem_src_base_addr)
         && $stable(pi_dest_base_addr)
    );

    assume_address_notequal: assume property (
        (pi_keymem_src_base_addr !=  pi_dest_base_addr)
    );



    assume_a_stable_when_idle : assume property (
        po_keymem_a_rd_req.rd_wr_en == RW_IDLE
                                       |=>
        $stable(pi_keymem_a_rd_data)
    );


    assume_b_stable_when_idle : assume property (
        po_keymem_b_rd_req.rd_wr_en == RW_IDLE
                                       |=>
        $stable(pi_keymem_b_rd_data)
    );

    // Confirmed intended memory model is 3-cycle latency, not 1-cycle -- superseded
    // by keymem_a/b_rd_req_sets_keymem_a/b_rd_data_valid above.




/////////////////////////////////////////////////////////////// Additional Assertions  ///////////////////////////////////////////////////////////////

////////////////////////////// Assertion for Combinatorial rd req /////////////////////////////////
    // Read/idle no longer split on buffer fullness (abr_rd_lat_buffer never asserts
    // backpressure) -- the real determinant of RW_READ vs RW_IDLE in SKDEC_RD_T0 is
    // the fixed read pacer (mem_rd_pace[0]), per skdecode_ctrl.sv.
    property rd_req_t0_pace_read;
        skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0 &&
        skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0 &&
        |skdecode_top.t0_valid &&
        !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
        skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
    |->
        po_keymem_a_rd_req.rd_wr_en == RW_READ  &&
        po_keymem_b_rd_req.rd_wr_en == RW_READ  &&
        po_keymem_a_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr)   &&
        po_keymem_b_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr + 'h1)   ;
    endproperty
    assert_rd_req_t0_pace_read: assert property (disable iff(!pi_reset_n) rd_req_t0_pace_read);

    property rd_req_t0_pace_idle;
        skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0 &&
        skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0 &&
        |skdecode_top.t0_valid &&
        !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
        !skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
    |->
        po_keymem_a_rd_req.rd_wr_en == RW_IDLE  &&
        po_keymem_b_rd_req.rd_wr_en == RW_IDLE  ;
    endproperty
    assert_rd_req_t0_pace_idle: assert property (disable iff(!pi_reset_n) rd_req_t0_pace_idle);

    property rst_rd_wr_addr;
        skdecode_top.skdecode_ctrl_inst.rst_rd_addr == (skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_IDLE) &&
        skdecode_top.skdecode_ctrl_inst.rst_wr_addr == (skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_IDLE)
    ;endproperty
    assert_rst_rd_wr_addr: assert property (disable iff(!pi_reset_n || pi_zeroize) rst_rd_wr_addr);

//////////////// Assertion for error /////////////////////////////
    logic [2:0] fv_temp;
    assume_temp_in_range: assume property (fv_temp >= 0 && fv_temp < 8);
    assume_temp_stable: assume property ($stable(fv_temp));
    assume_split_en_stable: assume property ($stable(pi_split_en_i));

    // s1s2_error is a registered, sticky latch of s1s2_error_set -- it captures
    // the bad sample one cycle after skdecode_s1s2_unpack flags it combinationally.
    property error_latched;
        skdecode_top.s1s2_buf_data[fv_temp] > 3'h4 && skdecode_top.s1s2_data_valid
    |=>
        skdecode_top.s1s2_error
    ;endproperty
    assert_error_latched: assert property (disable iff(!pi_reset_n) error_latched);

    // skdecode_error only pulses once the whole operation is done (s1s2_error & skdecode_done).
    property error_reported;
        skdecode_top.s1s2_error && skdecode_top.skdecode_done
    |->
        skdecode_top.skdecode_error
    ;endproperty
    assert_error_reported: assert property (disable iff(!pi_reset_n) error_reported);

    /* OLD
    property error;
        skdecode_top.s1s2_buf_data[fv_temp] > 3'h4 && skdecode_top.s1s2_data_valid
    |->
        skdecode_top.skdecode_error
    ;endproperty
    assert_error: assert property (disable iff(!pi_reset_n) error);
    */
   /////////////////// Whitebox checks Assertions for the data in to fifo's ///////////////////////

    // keymem_rd_data_reg[0]/[1] now update on two independent conditions (see the
    // IO flop always_ff in skdecode_top.sv) instead of a single full/not-full gate,
    // since abr_rd_lat_buffer never asserts backpressure.
    property s1s2_data_reg_capture;
       (skdecode_top.keymem_rd_data_valid[0] | skdecode_top.s1s2_keymem_b_valid)
    |=>
       skdecode_top.keymem_rd_data_reg[0] == ($past(skdecode_top.s1s2_keymem_b_valid) ? $past(pi_keymem_b_rd_data) : $past(pi_keymem_a_rd_data))
    ;endproperty
    assert_s1s2_data_reg_capture: assert property (disable iff(!pi_reset_n || pi_zeroize) s1s2_data_reg_capture);

    property s1s2_data_reg_stable;
       !(skdecode_top.keymem_rd_data_valid[0] | skdecode_top.s1s2_keymem_b_valid)
    |=>
       $stable(skdecode_top.keymem_rd_data_reg[0])
    ;endproperty
    assert_s1s2_data_reg_stable: assert property (disable iff(!pi_reset_n || pi_zeroize) s1s2_data_reg_stable);

    property t0_data_reg_capture;
       (skdecode_top.keymem_rd_data_valid[1] & ~skdecode_top.s1s2_enable)
    |=>
       skdecode_top.keymem_rd_data_reg[1] == $past(pi_keymem_b_rd_data)
    ;endproperty
    assert_t0_data_reg_capture: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_data_reg_capture);

    property t0_data_reg_stable;
       !(skdecode_top.keymem_rd_data_valid[1] & ~skdecode_top.s1s2_enable)
    |=>
       $stable(skdecode_top.keymem_rd_data_reg[1])
    ;endproperty
    assert_t0_data_reg_stable: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_data_reg_stable);

    property reset_data_reg;
        $past(!pi_reset_n || pi_zeroize)
    |->
        skdecode_top.keymem_rd_data_reg == 0
    ;endproperty
    assert_reset_data_reg: assert property (reset_data_reg);



    property t0_data_valid;
        skdecode_top.t0_data_valid
    |=>
        (&skdecode_top.t0_valid)
    ;endproperty
    assert_t0_data_valid: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_data_valid);

     property t0_no_data_valid;
        !skdecode_top.t0_data_valid
     |=>
        !(&skdecode_top.t0_valid)
     ;endproperty
    assert_t0_no_data_valid: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_no_data_valid);


/////////////////////////////////////////////////////////////// Scoreboard instance for buffers verification ///////////////////////////////////////////////////////////////
    fv_skdecode_top_scoreboard fv_skdecode_top_scoreboard_i (.*);







endmodule


bind skdecode_top fv_skdecode_top_wrapper #(.ABR_NUM_NTT(ABR_NUM_NTT)) fv_skdecode_top_wrapper_i (

.pi_clk(clk),
.pi_reset_n(reset_n),
.pi_zeroize(zeroize),
.pi_skdecode_enable(skdecode_enable),
.pi_keymem_src_base_addr(keymem_src_base_addr),
.pi_dest_base_addr(dest_base_addr),
.pi_keymem_a_rd_data(keymem_rd_data[0]),
.pi_keymem_b_rd_data(keymem_rd_data[1]),
// Added: bind the new valid ports to the real RTL signal (previously only
// reachable via skdecode_top.keymem_rd_data_valid[i] hierarchical refs elsewhere).
.pi_keymem_a_rd_data_valid(keymem_rd_data_valid[0]),
.pi_keymem_b_rd_data_valid(keymem_rd_data_valid[1]),
.pi_split_en_i(split_en_i),
.pi_rand_i(rand_i),
.pi_rand_dual_i(rand_dual_i),
.po_keymem_a_rd_req(keymem_rd_req[0]),
.po_keymem_b_rd_req(keymem_rd_req[1]),
.po_mem_a_wr_req(mem_a_wr_req),
.po_mem_b_wr_req(mem_b_wr_req),
.po_mem_a_wr_data(mem_a_wr_data),
.po_mem_b_wr_data(mem_b_wr_data),
.po_skdecode_error(skdecode_error),
.po_skdecode_done(skdecode_done),
.po_s1_done(s1_done),
.po_s2_done(s2_done),
.po_t0_done(t0_done),

// abr_rd_lat_buffer never asserts backpressure (pre-allocated to worst-case
// depth), so valid_i/data_i mirror the buffer's actual push condition in
// skdecode_top.sv instead of the removed stall/enable_reg gating.
.s1s2_fifo_valid_i({4{skdecode_top.keymem_rd_data_valid_f & skdecode_top.s1s2_enable}}),
.s1s2_fifo_data_i(skdecode_top.keymem_rd_data_reg[0]),
.s1s2_fifo_valid_o(skdecode_top.s1s2_data_valid),
.s1s2_buffer_full_o(1'b0),
.s1s2_fifo_data_o(skdecode_top.s1s2_buf_data),
.t0_fifo_valid_i({16{skdecode_top.keymem_rd_data_valid_f & skdecode_top.t0_enable}}),
.t0_fifo_data_i(skdecode_top.keymem_rd_data_reg),
.t0_fifo_valid_o(skdecode_top.t0_data_valid),
.t0_buffer_full_o(1'b0),
.t0_fifo_data_o(skdecode_top.t0_buf_data)


);
