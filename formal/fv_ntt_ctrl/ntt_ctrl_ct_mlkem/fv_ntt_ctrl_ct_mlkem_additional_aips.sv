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




module fv_ntt_ctrl_ct_mode_additional_property
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
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
    input logic                      po_bf_enable,
    input logic [2:0]                po_opcode,
    input logic                      po_masking_en_ctrl,
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

    logic buf_enable;
    
    assign buf_enable = pi_shuffle_en ? ntt_ctrl.bf_enable_reg : ntt_ctrl.bf_enable_fsm;
    property buf_enable_p;
      po_bf_enable == buf_enable;
    endproperty
    assert_bf_enable_a: assert property (disable iff(!pi_reset_n || pi_zeroize) buf_enable_p);

   property assert_buf_wr_en_p;
        po_buf_wren == ntt_ctrl.buf_wren_ntt_reg;
   endproperty
   assert_buf_wr_en_a: assert property (disable iff(!pi_reset_n || pi_zeroize)assert_buf_wr_en_p);

   property  buf_wr_ptr_check_p;
          (po_buf_wren) |-> ##1 po_buf_wrptr ==  (po_buf_wrptr == 3) ?  (po_buf_wrptr == 0) : ($past(po_buf_wrptr,1) + 1);
   endproperty
   assert_buf_wr_ptr_check_p: assert property (disable iff(!pi_reset_n || pi_zeroize) buf_wr_ptr_check_p); 

   logic [6:0] twiddle_addr_int;
   assign twiddle_addr_int = ntt_ctrl.twiddle_addr_reg + twiddle_offset(ntt_ctrl.rounds_count);
   property twiddle_addr_p;
     po_twiddle_addr == twiddle_addr_int;
   endproperty
   assert_twiddle_addr_a : assert property (disable iff(!pi_reset_n || pi_zeroize) twiddle_addr_p); 

   logic buf_rden ;
   assign  buf_rden = pi_shuffle_en? (ntt_ctrl.buf_rden_ntt_reg) :ntt_ctrl.buf_rden_ntt;
   property assert_buf_rd_en_p;
     ##1 po_buf_rden == buf_rden;
   endproperty
   assert_buf_rd_en_a: assert property (disable iff(!pi_reset_n || pi_zeroize)assert_buf_rd_en_p);
     
   property assert_buf_wr_rst_count_p;
     po_buf_wr_rst_count == ((ntt_ctrl.read_fsm_state_ps == RD_IDLE) || (ntt_ctrl.read_fsm_state_ps == RD_STAGE) || (ntt_ctrl.read_fsm_state_ps == EXEC_WAIT));
   endproperty
   assert_buf_wr_rst_count_a : assert property (disable iff(!pi_reset_n || pi_zeroize) assert_buf_wr_rst_count_p);
     
   property assert_buf_rd_rst_count_p;
    po_buf_rd_rst_count == ((ntt_ctrl.read_fsm_state_ps == RD_IDLE) || (ntt_ctrl.read_fsm_state_ps == RD_STAGE) );
   endproperty
   assert_buf_rd_rst_count_a : assert property (disable iff(!pi_reset_n || pi_zeroize) assert_buf_wr_rst_count_p);

     
   logic [2:0] buf_rdptr;
   assign buf_rdptr = (pi_shuffle_en) ? ntt_ctrl.buf_rdptr_f : ntt_ctrl.buf_count;
   property assert_buf_rdptr_p;
     po_buf_rdptr == buf_rdptr;    
   endproperty
   assert_buf_rdptr_a : assert property (disable iff(!pi_reset_n || pi_zeroize) assert_buf_rdptr_p);

  logic mem_rd_en_1;
  logic mem_rd_en_2;

  assign mem_rd_en_1 = (((po_mem_rd_addr <= 63 + ntt_ctrl.mem_rd_base_addr) && !((ntt_ctrl.buf_count == 3) && (ntt_ctrl.rd_valid_count == 60)) ) ? 1 : 0);
                    
  assign mem_rd_en_2 = ((ntt_ctrl.read_fsm_state_ps == RD_STAGE) || ((ntt_ctrl.read_fsm_state_ps == EXEC_WAIT)|| (ntt_ctrl.read_fsm_state_ps == RD_IDLE)))? 0 
  : ((ntt_ctrl.read_fsm_state_ps == RD_BUF) || (ntt_ctrl.read_fsm_state_ps == RD_EXEC) )&& mem_rd_en_1;

  property mem_rd_en_exec_p;
    po_mem_rd_en == mem_rd_en_2;
  endproperty
  assert_mem_rd_en_exec_a: assert property (disable iff(!pi_reset_n || pi_zeroize) mem_rd_en_exec_p);

  

  property assert_busy_a;
    po_busy ==  ((ntt_ctrl.read_fsm_state_ps != RD_IDLE) && (ntt_ctrl.write_fsm_state_ps != WR_IDLE));
  endproperty
  assert_busy_p:assert property(disable iff(!pi_reset_n || pi_zeroize)assert_busy_a);

  logic mem_rd_en;
  assign mem_rd_en = pi_shuffle_en? ntt_ctrl.mem_rd_en_reg:ntt_ctrl.mem_rd_en_fsm;
  property mem_rd_en_a;
     po_mem_rd_en == ntt_ctrl.mem_rd_en_fsm; 
  endproperty  
  assert_mem_rd_en_p: assert property(disable iff(!pi_reset_n || pi_zeroize) mem_rd_en_a);
   

  logic mem_wr_en;
  assign mem_wr_en = pi_shuffle_en? ntt_ctrl.mem_wr_en_reg:ntt_ctrl.mem_wr_en_fsm;
  property mem_wr_en_a;  
     po_mem_wr_en == mem_wr_en;
  endproperty  
  assert_mem_wr_en_p : assert property (disable iff(!pi_reset_n || pi_zeroize)mem_wr_en_a);
  
  
  property not_same_address_p; 
    (ntt_ctrl.mem_rd_en && ntt_ctrl.mem_wr_en ) |-> (ntt_ctrl.mem_rd_addr != ntt_ctrl.mem_wr_addr);
  endproperty  
  assert_not_same_address_a : assert property (disable iff(!pi_reset_n || pi_zeroize)not_same_address_p);
  
  property ntt_done_p;
    ntt_ctrl.ntt_done == (ntt_ctrl.rounds_count == 4);
  endproperty
  ntt_done_a:  assert property (disable iff(!pi_reset_n || pi_zeroize)ntt_done_p);

  property latch_index_rand_offset_p;
     ntt_ctrl.latch_index_rand_offset == (po_buf_wrptr == 3);
  endproperty
  latch_index_rand_offset_a:  assert property (disable iff(!pi_reset_n || pi_zeroize)latch_index_rand_offset_p);


  property latch_chunk_rand_offset_p;
    ntt_ctrl.latch_chunk_rand_offset == (ntt_ctrl.arc_IDLE_WR_STAGE || ntt_ctrl.arc_WR_MEM_WR_STAGE);
  endproperty
  assert_latch_chunk_rand_offset_a:assert property (disable iff(!pi_reset_n || pi_zeroize)latch_chunk_rand_offset_p);


endmodule

bind ntt_ctrl fv_ntt_ctrl_ct_mode_additional_property ct_mode_additional_aip_inst(
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
    .po_masking_en_ctrl (masking_en_ctrl),
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