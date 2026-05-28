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
    import mldsa_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    // Parameters
    parameter MLDSA_ETA = 2,
    parameter MLDSA_D = 13,
    parameter ETA_SIZE = 3,
    parameter REG_SIZE = 24,
    parameter AHB_DATA_WIDTH = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic pi_clk,
    input logic pi_reset_n,
    input logic pi_zeroize,

    input wire pi_skdecode_enable,
    input wire [MLDSA_MEM_ADDR_WIDTH-1:0] pi_keymem_src_base_addr,
    input wire [MLDSA_MEM_ADDR_WIDTH-1:0] pi_dest_base_addr,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_a_rd_data,
    input wire [AHB_DATA_WIDTH-1:0] pi_keymem_b_rd_data,

    input mem_if_t po_keymem_a_rd_req,
    input mem_if_t po_keymem_b_rd_req,
    input mem_if_t po_mem_a_wr_req,
    input mem_if_t po_mem_b_wr_req,
    input logic [3:0][REG_SIZE-1:0] po_mem_a_wr_data,
    input logic [3:0][REG_SIZE-1:0] po_mem_b_wr_data,
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
    // assume_error: assume property (!po_skdecode_error);
    enable_to_done: cover property ((skdecode_ctrl_inst.arc_SKDEC_RD_IDLE_SKDEC_RD_S1 && skdecode_ctrl_inst.arc_SKDEC_WR_IDLE_SKDEC_WR_S1)  ##1 skdecode_ctrl_inst.arc_SKDEC_RD_STAGE_SKDEC_RD_IDLE [->1] );
    // enable_to_done1: cover property (skdecode_ctrl_inst.skdecode_enable ##1 skdecode_ctrl_inst.skdecode_done [->1] );
    

    property enable_signal_set;
        pi_reset_n
    |->
        s_eventually(pi_skdecode_enable);
    endproperty
    //assume_enable_signal_set: assume property (disable iff(!pi_reset_n) enable_signal_set);



        logic fv_ongoing_computation;
    always_ff @(posedge pi_clk) begin
        if(!pi_reset_n) begin
            fv_ongoing_computation <= 1'b0;
        end else if(!fv_ongoing_computation || po_skdecode_done) begin
            fv_ongoing_computation <= pi_skdecode_enable;
        end
    end

    // Set enable only when it is not busy
    assume_only_enable_when_idle : assume property (
        pi_skdecode_enable
    |->
        !fv_ongoing_computation || po_skdecode_done
    );



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

   


/////////////////////////////////////////////////////////////// Additional Assertions  ///////////////////////////////////////////////////////////////

////////////////////////////// Assertion for Combinatorial rd req /////////////////////////////////
    property rd_req_t0_idle;
        skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0 && 
        skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0 &&
        |skdecode_top.t0_valid &&
        (10'd1 + skdecode_top.skdecode_ctrl_inst.skdecode_count) < 10'd512 &&
        skdecode_top.t0_buf_full 
    |->
        po_keymem_a_rd_req.rd_wr_en == RW_IDLE  &&
        po_keymem_b_rd_req.rd_wr_en == RW_IDLE  &&
        po_keymem_a_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr)   &&
        po_keymem_b_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr + 'h1)   ;
    endproperty
    assert_rd_req_t0_idle: assert property (disable iff(!pi_reset_n) rd_req_t0_idle);

    property rd_req_t0_read;
        skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0 && 
        skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_T0 &&
        |skdecode_top.t0_valid &&
        (10'd1 + skdecode_top.skdecode_ctrl_inst.skdecode_count) < 10'd512 &&
        !skdecode_top.t0_buf_full 
    |->
        po_keymem_a_rd_req.rd_wr_en == RW_READ  &&
        po_keymem_b_rd_req.rd_wr_en == RW_READ  &&
        po_keymem_a_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr)   &&
        po_keymem_b_rd_req.addr  == 14'(skdecode_top.skdecode_ctrl_inst.kmem_rd_addr + 'h1)   ;
    endproperty
    assert_rd_req_t0_read: assert property (disable iff(!pi_reset_n) rd_req_t0_read);

    property rst_rd_wr_addr;
        skdecode_top.skdecode_ctrl_inst.rst_rd_addr == (skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_IDLE) &&
        skdecode_top.skdecode_ctrl_inst.rst_wr_addr == (skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_IDLE)
    ;endproperty
    assert_rst_rd_wr_addr: assert property (disable iff(!pi_reset_n || pi_zeroize) rst_rd_wr_addr);

//////////////// Assertion for error /////////////////////////////
    logic [3:0] temp;
    assume_temp_in_range: assume property (temp >= 0 && temp < 8);
    property error;
        skdecode_top.s1s2_buf_data[temp] > 3'h4 && skdecode_top.s1s2_data_valid
    |->
        skdecode_top.skdecode_error
    ;endproperty
    assert_error: assert property (disable iff(!pi_reset_n) error);

   /////////////////// Whitebox checks Assertions for the data in to fifo's ///////////////////////

    property s1s2_t0_fifo_data_in;
       !skdecode_top.t0_buf_full &&
       !skdecode_top.s1s2_buf_full
       |=>
       skdecode_top.keymem_a_rd_data_reg == ($past(skdecode_top.s1s2_keymem_b_valid) ? $past(pi_keymem_b_rd_data): $past(pi_keymem_a_rd_data)) &&
       skdecode_top.keymem_b_rd_data_reg == $past(pi_keymem_b_rd_data)
    ;endproperty
    assert_s1s2_t0_fifo_data_in: assert property (disable iff(!pi_reset_n || pi_zeroize) s1s2_t0_fifo_data_in);

    property s1s2_t0_fifo_data_in_stable;
       skdecode_top.t0_buf_full ||
       skdecode_top.s1s2_buf_full
       |=>
       $stable(skdecode_top.keymem_a_rd_data_reg) &&
       $stable(skdecode_top.keymem_b_rd_data_reg)
    ;endproperty
    assert_s1s2_t0_fifo_data_in_stable: assert property (disable iff(!pi_reset_n || pi_zeroize) s1s2_t0_fifo_data_in_stable);

    property reset_data_reg;
        !pi_reset_n || pi_zeroize
        |=>
        skdecode_top.keymem_a_rd_data_reg == 0 &&
        skdecode_top.keymem_b_rd_data_reg == 0
    ;endproperty
    assert_reset_data_reg: assert property (reset_data_reg);


    property buffer_full_onehot;
        $onehot0({skdecode_top.s1s2_buf_full,skdecode_top.t0_buf_full})
    ;endproperty
    assert_buffer_full_onehot: assert property (disable iff(!pi_reset_n || pi_zeroize) buffer_full_onehot);

    logic [5:0] fv_t0_buffer_count_in;
    logic [5:0] fv_t0_buffer_count_out;

    property t0_buf_full;
        (fv_t0_buffer_count_out) > 26 // based on the buffer depth subtracted the difference between incoming and outgoing
        |->
        skdecode_top.t0_buf_full    
    ;endproperty    
    assert_t0_buf_full: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_buf_full);

     property t0_buf_pop;
        skdecode_top.t0_data_valid   == ((fv_t0_buffer_count_out) >= 13)  // based on the buffer rd
    ;endproperty    
    assert_t0_buf_pop: assert property (disable iff(!pi_reset_n || pi_zeroize) t0_buf_pop);

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


lubis_incr_decr_counter_m #(
    .COUNTER_WIDTH      (6),
    .NUM_INC_SRCS       (1 ),
    .NUM_DEC_SRCS       (1 ),
    .MAX_VALUE          (28 ),
    .MIN_VALUE          (    ),
    .INCR_VAL_WIDTH (6),
    .DECR_VAL_WIDTH (6)/*
    .ASSERT_CLAMP_MAX   (0            ),
    .ASSERT_CLAMP_MIN   (0            ),
    .ASSERT_NO_UNDERFLOW(1            ),
    .ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_t0_in
(
    .clk     (pi_clk                            ),
    .rst     (~pi_reset_n || pi_zeroize         ),
    .soft_rst(1'b0                   ),
    .incr_en ((|t0_fifo_valid_i) && !(fv_t0_buffer_count_out >26)   ),  
    .decr_en (t0_fifo_valid_o              ),
    .incr_val($countones(t0_fifo_valid_i)            ),
    .decr_val( 13                                  ),
    .count   (  fv_t0_buffer_count_out                  ),
    .count_next(fv_t0_buffer_count_in              )
);


//lubis_incr_decr_counter_m #(
//    .COUNTER_WIDTH      (6),
//    .NUM_INC_SRCS       (1 ),
//    .NUM_DEC_SRCS       (0 ),
//    .MAX_VALUE          (28 ),
//    .MIN_VALUE          (    ),
//    .INCR_VAL_WIDTH (6),
//    .DECR_VAL_WIDTH (6)/*
//    .ASSERT_CLAMP_MAX   (0            ),
//    .ASSERT_CLAMP_MIN   (0            ),
//    .ASSERT_NO_UNDERFLOW(1            ),
//    .ASSERT_NO_OVERFLOW (1            )*/
//) lubis_incr_decr_counter_t0_out
//(
//    .clk     (pi_clk                            ),
//    .rst     (~pi_reset_n || pi_zeroize         ),
//    .soft_rst(1'b0                   ),
//    .incr_en ((t0_fifo_valid_o)  ),  
//    .decr_en ('0               ),
//    .incr_val(13           ),
//    .decr_val('0                             ),
//    .count   (                    ),
//    .count_next(fv_t0_buffer_count_out              )
//);
/////////////////////////////////////////////////////////////// Scoreboard instance for buffers verification ///////////////////////////////////////////////////////////////
    fv_skdecode_top_scoreboard skdecode_top_scoreboard_i (.*);







endmodule


bind skdecode_top fv_skdecode_top_wrapper fv_skdecode_top_wrapper_i (

.pi_clk(clk),
.pi_reset_n(reset_n),
.pi_zeroize(zeroize),
.pi_skdecode_enable(skdecode_enable),
.pi_keymem_src_base_addr(keymem_src_base_addr),
.pi_dest_base_addr(dest_base_addr),
.pi_keymem_a_rd_data(keymem_a_rd_data),
.pi_keymem_b_rd_data(keymem_b_rd_data),
.po_keymem_a_rd_req(keymem_a_rd_req),
.po_keymem_b_rd_req(keymem_b_rd_req),
.po_mem_a_wr_req(mem_a_wr_req),
.po_mem_b_wr_req(mem_b_wr_req),
.po_mem_a_wr_data(mem_a_wr_data),
.po_mem_b_wr_data(mem_b_wr_data),
.po_skdecode_error(skdecode_error),
.po_skdecode_done(skdecode_done),
.po_s1_done(s1_done),
.po_s2_done(s2_done),
.po_t0_done(t0_done),

.s1s2_fifo_valid_i(skdecode_top.s1s2_buf_stall_reg/*(s1s2_buf_full | ~s1s2_enable)*/ ? 4'h0 : {4{skdecode_top.s1s2_enable_reg}}),
.s1s2_fifo_data_i(skdecode_top.keymem_a_rd_data_reg),
.s1s2_fifo_valid_o(skdecode_top.s1s2_data_valid),
.s1s2_buffer_full_o(skdecode_top.s1s2_buf_full),
.s1s2_fifo_data_o(skdecode_top.s1s2_buf_data),
.t0_fifo_valid_i((skdecode_top.t0_buf_full | ~skdecode_top.t0_enable) ? 16'h0 : {16{skdecode_top.t0_enable_reg}}),
.t0_fifo_data_i({skdecode_top.keymem_b_rd_data_reg, skdecode_top.keymem_a_rd_data_reg}),
.t0_fifo_valid_o(skdecode_top.t0_data_valid),
.t0_buffer_full_o(skdecode_top.t0_buf_full),
.t0_fifo_data_o(skdecode_top.t0_buf_data)


);
