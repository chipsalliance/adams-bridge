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
`include "mldsa_config_defines.svh"


module fv_mldsa_ctrl_stream_msg 
    import mldsa_reg_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_sampler_pkg::*;
    import mldsa_ctrl_pkg::*;
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    // Parameters
    parameter ADAMSBRIDGE_CNTRL_RDY_DELAY     = 1,
    parameter ADAMSBRIDGE_BUSY_CNTR = 2,
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 64,
    parameter CLIENT_DATA_WIDTH = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic pi_clk,
    input logic pi_rst_b,
    input logic po_zeroize,

    input mldsa_reg__in_t   po_abr_reg_hwif_in_o,
    input  mldsa_reg__out_t pi_abr_reg_hwif_out_i,

    //sampler interface
    input mldsa_sampler_mode_e          po_sampler_mode_o,
    input logic                       po_sha3_start_o,
    input logic                       po_msg_start_o,
    input logic                       po_msg_valid_o,
    input logic                       pi_msg_rdy_i,
    input logic [MsgStrbW-1:0]        po_msg_strobe_o,
    input logic [MsgWidth-1:0]        po_msg_data_o[Sha3Share],
    input logic                       po_sampler_start_o,

    input logic                        pi_sampler_busy_i,
    input logic                        pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0] pi_sampler_state_data_i [Sha3Share],

    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_dest_base_addr_o,

    //ntt interfaces
    input logic [1:0]                        po_ntt_enable_o,
    input mldsa_ntt_mode_e [1:0]               po_ntt_mode_o,
    input logic [1:0]                        po_ntt_masking_en_o,
    input logic [1:0]                        po_ntt_shuffling_en_o,
    input ntt_mem_addr_t [1:0]               po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t [1:0]               po_pwo_mem_base_addr_o,
    input logic [1:0]                        pi_ntt_busy_i,

    //aux interfaces
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_src0_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_src1_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] po_aux_dest_base_addr_o,

    input logic                         po_power2round_enable_o,
    input mem_if_t [1:0]                pi_pwr2rnd_keymem_if_i,
    input logic [1:0] [DATA_WIDTH-1:0]  pi_pwr2rnd_wr_data_i,
    input logic                         pi_pk_t1_wren_i,
    input logic [7:0][9:0]              pi_pk_t1_wrdata_i, // TODO: change to parameter
    input logic [7:0]                   pi_pk_t1_wr_addr_i, // TODO: change to parameter
    input logic                         pi_power2round_done_i,

    input logic po_decompose_enable_o,
    input logic po_decompose_mode_o,
    input logic pi_decompose_done_i,

    input logic                  po_skencode_enable_o,
    input mem_if_t               pi_skencode_keymem_if_i,
    input logic [DATA_WIDTH-1:0] pi_skencode_wr_data_i,
    input logic                  pi_skencode_done_i,

    input logic                       po_skdecode_enable_o,
    input mem_if_t [1:0]              pi_skdecode_keymem_if_i,
    input logic [1:0][DATA_WIDTH-1:0] po_skdecode_rd_data_o,
    input logic                       pi_skdecode_done_i,
    input logic                       pi_skdecode_error_i,

    input logic                      po_makehint_enable_o,
    input logic                      pi_makehint_invalid_i,
    input logic                      pi_makehint_done_i,
    input logic                      pi_makehint_reg_wren_i,
    input logic [3:0][7:0]           pi_makehint_reg_wrdata_i,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] pi_makehint_reg_wr_addr_i,

    input logic                          po_normcheck_enable_o,
    input logic [1:0]                    po_normcheck_mode_o,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0] po_normcheck_src_addr_o,
    input logic                          pi_normcheck_invalid_i,
    input logic                          pi_normcheck_done_i,

    input logic                  po_sigencode_enable_o,
    input mem_if_t               pi_sigencode_wr_req_i,
    input logic [1:0][3:0][19:0] pi_sigencode_wr_data_i,
    input logic                  pi_sigencode_done_i,

    input logic                       po_pkdecode_enable_o,
    input logic [7:0]                 pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0] po_pkdecode_rd_data_o,
    input logic                       pi_pkdecode_done_i,


    input logic                                        po_sigdecode_h_enable_o, 
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] po_signature_h_o,
    input logic                                        pi_sigdecode_h_invalid_i,
    input logic                                        pi_sigdecode_h_done_i,

    input logic                  po_sigdecode_z_enable_o, 
    input mem_if_t               pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0] po_sigdecode_z_rd_data_o,
    input logic                  pi_sigdecode_z_done_i,

    input logic po_lfsr_enable_o,
    input logic [1:0][LFSR_W-1:0] po_lfsr_seed_o,
    input logic                                       po_sk_bank0_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank0_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                      po_sk_bank0_mem_if_wdata_i,
    input logic                                       po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank0_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                      pi_sk_bank0_mem_if_rdata_o,
    input logic                                       po_sk_bank1_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank1_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                      po_sk_bank1_mem_if_wdata_i,
    input logic                                       po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]              po_sk_bank1_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                      pi_sk_bank1_mem_if_rdata_o,

    input logic                                       po_sig_z_mem_if_we_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                po_sig_z_mem_if_waddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                po_sig_z_mem_if_wdata_i,
    input logic [SIG_Z_MEM_DATA_W/8-1:0]              po_sig_z_mem_if_wstrobe_i,
    input logic                                       po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                po_sig_z_mem_if_raddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                pi_sig_z_mem_if_rdata_o,
    input logic                                       po_pk_mem_if_we_i,
    input logic [PK_ADDR_W-1:0]                       po_pk_mem_if_waddr_i,
    input logic [PK_MEM_DATA_W-1:0]                   po_pk_mem_if_wdata_i,
    input logic [PK_MEM_DATA_W/8-1:0]                 po_pk_mem_if_wstrobe_i,
    input logic                                       po_pk_mem_if_re_i,
    input logic [PK_ADDR_W-1:0]                       po_pk_mem_if_raddr_i,
    input logic [PK_MEM_DATA_W-1:0]                   pi_pk_mem_if_rdata_o,

    input mem_if_t                                    zeroize_mem_o,

    `ifdef CALIPTRA
    // KV interface
    input kv_read_t kv_read,
    input kv_rd_resp_t kv_rd_resp,
    //PCR Signing
    input pcr_signing_t pcr_signing_data,
    `endif

    input logic pi_debugUnlock_or_scan_mode_switch,
    input logic po_busy_o,

    //Interrupts
    input logic po_error_intr,
    input logic po_notif_intr
);


    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

    // Auxiliary logic to keep track of the packet in the per byte

    // This proof is vacuous since the the DUT there is never a possibility where the rdy is unaligned with valid since the DUT needs two 32 bit valid packets two frame one full 
    // packet which is possible in two clk cycles a minimum and the ready is only deasserted for 1 clk cycle at max.
    property backpressure_keccak_to_primary_P;
        !pi_msg_rdy_i && po_msg_valid_o && fv_streaming_ongoing
        |=>
        $stable(po_msg_data_o) &&
        $stable(po_msg_valid_o)
    ;endproperty
    assert_backpressure_keccak_to_primary_P: assert property (disable iff(!pi_rst_b || po_zeroize) backpressure_keccak_to_primary_P);
   
   cover_msg_buffer_full: cover property (disable iff(!pi_rst_b || po_zeroize) (&mldsa_ctrl.stream_msg_buffer_strobe)[->20] );


    logic [$clog2(MsgWidth)-1:0]                    fv_sym_data;
    logic [MsgWidth-1:0]                            fv_msg_out;
    logic [MsgWidth-1:0]                            fv_msg_buffer_data,fv_msg_buffer_data_reg;
    logic [2*MsgWidth-1:0]                          fv_msg_buffer_data_extended,fv_msg_buffer_data_extended_reg;
    logic [MsgStrbW-1:0]                            fv_msg_buffer_strobe,fv_msg_buffer_strobe_reg;
    logic [2*MsgStrbW-1:0]                          fv_msg_buffer_strobe_extended,fv_msg_buffer_strobe_extended_reg;
    logic [CTX_SIZE_W-1:0]                          fv_stream_ctx_size;
    logic [CTX_NUM_DWORDS-1:0][DATA_WIDTH-1:0]      fv_ctx_reg;
    logic                                           fv_stream_push_scoreboard;
    logic                                           fv_msg_last,fv_msg_last_reg;
    logic                                           fv_msg_last_ctx,fv_msg_last_ctx_reg,fv_msg_last_ctx_reg_d1,fv_msg_last_ctx_reg_d2,fv_msg_last_ctx_reg_d3;
    logic                                           fv_stream_push_buf;
    logic                                           fv_streaming_ongoing;
    logic                                           fv_msg_flush_reg,fv_msg_flush;
    logic [CTX_SIZE_W:0]                            fv_stream_push_buf_cnt;
    logic                                           fv_input_msg_valid;

    // Symbolic variable for chossing one byte among the 8 bytes for the verification
    assume_sym_stable_for_msg_data: assume property (##1 $stable(fv_sym_data) && (fv_sym_data<8) );

    // Formal suite signal to store the ctx size.
    assign fv_stream_ctx_size = pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value;

    // Formal suite signal to store the ctx data incoming.
    always_comb begin: fv_ctx_reg_logic
        for (int dword = 0; dword < CTX_NUM_DWORDS; dword++) begin
            fv_ctx_reg[dword] = pi_abr_reg_hwif_out_i.MLDSA_CTX[dword].CTX.value;
        end
    end

    // Auxiliary logic to build the packet that needs to be pushed to the scoreboard and 
    // the ctrl signal to push.
    // At first the packet forms starting with the ctx size, then ctx data if the size is not 0
    // continue till the size is met and then later the data from the incoming message, is accumulated.
    // The strobe is also built in the same way, first the ctx size and then the ctx data and then the incoming message.
    // The data incoming is always 32 bits but the output data is 64 bits, so an accumulator is used to store
    // and push to scoreboard whenever there is valid 64 bits in the accumulator.
     always_comb begin : fv_msg_preparation_logic
        fv_msg_buffer_data              = fv_msg_buffer_data_reg;
        fv_msg_buffer_strobe            = fv_msg_buffer_strobe_reg;
        fv_msg_flush                    = '0;
        fv_msg_buffer_data_extended     = fv_msg_buffer_data_extended_reg;
        fv_msg_buffer_strobe_extended   = fv_msg_buffer_strobe_extended_reg;
        fv_stream_push_scoreboard       = '0 ;
        fv_msg_last                     = '0;
        fv_msg_last_ctx                 = '0;
        fv_stream_push_buf              = '0;
        fv_streaming_ongoing            = '0;
        if (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD  && (mldsa_ctrl.sampler_src == MLDSA_MSG_ID) &&  pi_abr_reg_hwif_out_i.MLDSA_CTRL.STREAM_MSG.value) begin
            fv_streaming_ongoing = 1'b1;
            if(fv_stream_push_buf_cnt == 0) begin  // the very first packet 3 bytes contain ctx_size info
                fv_stream_push_buf              = 1;
                fv_msg_buffer_data_extended     =  {16'h0,fv_stream_ctx_size, 8'h00};
                fv_msg_buffer_strobe_extended   = 8'h03;
            end
            else if ((fv_stream_push_buf_cnt >= 1) && (fv_stream_push_buf_cnt <= fv_stream_ctx_size[CTX_SIZE_W-1:$clog2(STREAM_MSG_STROBE_W)]+1)&& !fv_msg_last_ctx_reg) begin // ctx data is being fed until the ctx size worth data is send to keccak
                fv_msg_last_ctx     = (fv_stream_push_buf_cnt == fv_stream_ctx_size[CTX_SIZE_W-1:$clog2(STREAM_MSG_STROBE_W)]+1); // Additional 1 because first packet 3 bytes is being counted
                fv_stream_push_buf  = !fv_msg_last_ctx;
               if(fv_msg_last_ctx) begin
                    fv_msg_buffer_strobe_extended   = (4'(~(STREAM_MSG_STROBE_W'('1)<<(fv_stream_ctx_size[$clog2(STREAM_MSG_STROBE_W)-1:0])))<<$countones(fv_msg_buffer_strobe_extended_reg))| fv_msg_buffer_strobe_extended_reg;
                    fv_msg_buffer_data_extended     =(( (fv_ctx_reg[fv_stream_push_buf_cnt-1]<<(2*MsgWidth-(fv_stream_ctx_size[$clog2(STREAM_MSG_STROBE_W)-1:0])*8))>>(2*MsgWidth-(fv_stream_ctx_size[$clog2(STREAM_MSG_STROBE_W)-1:0])*8))<<$countones(fv_msg_buffer_strobe_extended_reg)*8)|fv_msg_buffer_data_extended_reg;
                end
                else begin
                    fv_msg_buffer_strobe_extended   = 4'hf<<$countones(fv_msg_buffer_strobe_extended_reg)|fv_msg_buffer_strobe_extended_reg;
                    fv_msg_buffer_data_extended     = (fv_ctx_reg[fv_stream_push_buf_cnt-1]<<$countones(fv_msg_buffer_strobe_extended_reg)*8)|fv_msg_buffer_data_extended_reg;
                end
                fv_stream_push_scoreboard = ($countones(fv_msg_buffer_strobe_extended[7:0])==8);
                fv_msg_buffer_data        = fv_msg_buffer_data_extended[MsgWidth-1:0];
                fv_msg_buffer_strobe      = fv_msg_buffer_strobe_extended[MsgStrbW-1:0];
               
            end
            else if (fv_msg_last_ctx_reg_d2) begin // two cycle wait since waiting for the DUT ready to accept the msg valid
                fv_msg_last = (fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value!='1);
                if(fv_input_msg_valid) begin
                            fv_msg_buffer_strobe_extended    = (pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value<<$countones(fv_msg_buffer_strobe_extended_reg))|fv_msg_buffer_strobe_extended_reg;
                            fv_msg_buffer_data_extended      = (DATA_WIDTH'((pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.value <<(DATA_WIDTH-$countones(pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value)*8)>>(DATA_WIDTH-$countones(pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value)*8) ))
                                                            <<$countones(fv_msg_buffer_strobe_extended_reg)*8)|fv_msg_buffer_data_extended_reg;  
                end
                else begin
                        fv_msg_buffer_strobe_extended   = fv_msg_buffer_strobe_extended_reg;
                        fv_msg_buffer_data_extended     = fv_msg_buffer_data_extended_reg;
                end
                if(!fv_msg_last) begin
                    fv_stream_push_scoreboard = $countones(fv_msg_buffer_strobe_extended[7:0])==8;
                end
                else begin
                   if($countones(fv_msg_buffer_strobe_extended)>8) begin
                       fv_stream_push_scoreboard = 1'b1;
                       fv_msg_flush              = 1'b1;
                   end
                   else begin
                        fv_stream_push_scoreboard = (|fv_msg_buffer_strobe_extended);
                        fv_msg_flush              = 1'b0;
                   end
                end
                fv_msg_buffer_data      = fv_msg_buffer_data_extended[MsgWidth-1:0];
                fv_msg_buffer_strobe    = fv_msg_buffer_strobe_extended[MsgStrbW-1:0];
                
            end
            else begin
                fv_stream_push_scoreboard   = 1'b0;
                fv_stream_push_buf          = 1'b0;
            end

            if(fv_msg_flush_reg) begin
                fv_stream_push_scoreboard   = 1'b1;
                fv_msg_buffer_data          = fv_msg_buffer_data_extended_reg[MsgWidth-1:0];
                fv_msg_buffer_strobe        = fv_msg_buffer_strobe_extended_reg[MsgStrbW-1:0];
            end
            

        end
        
     end
cover_msg_odd_partial_odd_ctx: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && fv_msg_last_ctx_reg_d2 && (pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value[0] == 1)
                                   ##0 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value == 4'b0111
                                   ##10 1'b1);
                                             
cover_msg_even_partial_odd_ctx: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && fv_msg_last_ctx_reg_d2 && (pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value[0] == 1)
                                   ##0 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1 
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value == 4'b0111
                                   ##10 1'b1);
cover_msg_odd_partial_even_ctx: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && fv_msg_last_ctx_reg_d2 && (pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value[0] == 0)
                                   ##0 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value == 4'b0111
                                   ##10 1'b1);
cover_msg_even_partial_even_ctx: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && fv_msg_last_ctx_reg_d2 && (pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value[0] == 0)
                                   ##0 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value =='1 
                                   ##2 fv_input_msg_valid && pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value == 4'b0111
                                   ##10 1'b1);

cover_ctx_size_0: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && (pi_abr_reg_hwif_out_i.MLDSA_CTX_CONFIG.CTX_SIZE.value == 0)
                                   ##1 mldsa_ctrl.msg_done[->1] );

cover_partial_strobe_0: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing && fv_input_msg_valid && fv_msg_last_ctx_reg_d2 && (pi_abr_reg_hwif_out_i.MLDSA_MSG_STROBE.STROBE.value == 0)
                                   ##1 mldsa_ctrl.msg_done[->1] );


cover_multiple_full_msg_streams: cover property(disable iff(!pi_rst_b || po_zeroize)
                                fv_streaming_ongoing &&
                                !pi_msg_rdy_i[->4]);                                   
// not possible since it is expected to have the rdy always                                   
cover_msg_flush_rdy_deassert: cover property (disable iff(!pi_rst_b || po_zeroize) 
                                   fv_streaming_ongoing  && mldsa_ctrl.stream_msg_fsm_ps == MLDSA_MSG_FLUSH
                                   ##1 !pi_msg_rdy_i && po_msg_valid_o
                                   ##5 1'b1 ); // ToDo: Add an assert

property check_msg_flush_always_rdy;
    @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
    mldsa_ctrl.stream_msg_fsm_ps == MLDSA_MSG_FLUSH
    && po_msg_valid_o
    |-> 
    pi_msg_rdy_i 
    ;endproperty
assert_check_msg_flush_always_rdy: assert property (check_msg_flush_always_rdy);

property check_msg_done_state_no_valid_msg;
    @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
    mldsa_ctrl.stream_msg_fsm_ps == MLDSA_MSG_DONE
    |-> 
    !po_msg_valid_o
    ;endproperty
assert_check_msg_done_state_no_valid_msg: assert property (check_msg_done_state_no_valid_msg);
 // not possible since the msg should be left and then make a transition to done state                                             
cover_done_state_no_valid_msg: cover property(disable iff(!pi_rst_b || po_zeroize)
                                mldsa_ctrl.stream_msg_fsm_ps == MLDSA_MSG_DONE &&
                                po_msg_valid_o);



// There is never a possiblity that there is a packet with strobe 0 since the ctx first packet constains size 3 bytes, so either we have a partial packet at end or full packet at end.
cover_no_strobe_with_valid_out: cover property(disable iff(!pi_rst_b || po_zeroize)
                                fv_streaming_ongoing &&
                                po_msg_valid_o && po_msg_strobe_o == '0);
//In DUT there is no prossibility when in streaming mode then there is no strobe, since ctx_size needs to be sent so atleast 2 bytes are always valid.
check_no_strobe_with_valid_out: assert property(disable iff(!pi_rst_b || po_zeroize)
                                fv_streaming_ongoing &&
                                po_msg_valid_o |-> po_msg_strobe_o != '0);
     always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_stream_reg
        if(!pi_rst_b || po_zeroize || !fv_streaming_ongoing) begin
            fv_msg_buffer_data_reg              <= '0;
            fv_msg_last_ctx_reg                 <= '0;
            fv_msg_last_ctx_reg_d1              <= '0;
            fv_msg_last_ctx_reg_d2              <= '0;
            fv_msg_last_ctx_reg_d3              <= '0;
            fv_msg_buffer_data_extended_reg     <= '0;
            fv_msg_buffer_strobe_reg            <= '0;
            fv_msg_buffer_strobe_extended_reg   <= '0;
            fv_msg_flush_reg                    <= '0;
            fv_msg_last_reg                     <= '0;
            fv_input_msg_valid                  <= '0;
        end
        else begin
            fv_input_msg_valid          <= pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.swmod;
            fv_msg_buffer_data_reg      <= fv_msg_buffer_data;
            fv_msg_buffer_strobe_reg    <= fv_msg_buffer_strobe;
            fv_msg_last_ctx_reg_d3      <= fv_msg_last_ctx_reg_d2;
            fv_msg_flush_reg            <= fv_msg_flush;

            if(fv_msg_last)begin
                fv_msg_last_reg <= fv_msg_last;
            end

            if(fv_msg_last_ctx && !fv_msg_last_ctx_reg) begin
                fv_msg_last_ctx_reg     <= fv_msg_last_ctx;
                fv_msg_last_ctx_reg_d1  <= fv_msg_last_ctx_reg;
                fv_msg_last_ctx_reg_d2  <= fv_msg_last_ctx_reg_d1;
            end
            else if(fv_msg_last || fv_msg_last_reg) begin
                fv_msg_last_ctx_reg_d1 <= !(fv_msg_last|| fv_msg_last_reg);
                fv_msg_last_ctx_reg_d2 <= !(fv_msg_last|| fv_msg_last_reg);
            end
            else begin
                fv_msg_last_ctx_reg_d1 <= fv_msg_last_ctx_reg;
                fv_msg_last_ctx_reg_d2 <= fv_msg_last_ctx_reg_d1;
            end

            if(fv_stream_push_scoreboard) begin
                fv_msg_buffer_data_extended_reg     <= (fv_msg_buffer_data_extended>>MsgWidth);
                fv_msg_buffer_strobe_extended_reg   <= (fv_msg_buffer_strobe_extended>>MsgStrbW);
            end
            else begin
                fv_msg_buffer_data_extended_reg     <= fv_msg_buffer_data_extended;
                fv_msg_buffer_strobe_extended_reg   <= fv_msg_buffer_strobe_extended;
            end
        end
     end
  
    
    
     

    // Counter to track the ctx cnt.
    lubis_incr_decr_counter_m #(
        .INCR_VAL_WIDTH(1),
        .COUNTER_WIDTH (CTX_SIZE_W+1),
        .NUM_INC_SRCS  (1)       
    ) fv_stream_msg_buf_cntr
        (
            .clk           (pi_clk      ),
            .rst           (!pi_rst_b ),
            .soft_rst      (po_zeroize || !fv_streaming_ongoing),
            .incr_en       (fv_stream_push_buf),
            .decr_en       (1'b0      ),
            .incr_val      (1'b1),
            .decr_val      ('0        ),
            .count         (fv_stream_push_buf_cnt),
            .count_next    (/* open */)
        );


    assign fv_msg_out = po_msg_data_o[0];
     lubis_scoreboard_m #(
      .WIDTH                (8                                ), 
      .DEPTH                (2                                ) // A depth of 2 is sufficient since the desin can hold max two valids
     ) fv_stream_msg_data_scoreboard( 
      .clk                  (pi_clk                                                  ),     
      .rst                  (!pi_rst_b   || po_zeroize                               ),
      .soft_rst             (1'b0                                                    ),
      .full                 (1'b0                                                    ),    
      .empty                (1'b0                                                    ),   
      .data_in              ( fv_msg_buffer_data[fv_sym_data*8+:8]                   ), // expected data per byte, choosing the byte symbolically
      .data_out             (    fv_msg_out[fv_sym_data*8+:8]                        ),  // Actual data o/p from the dut choosing the exact byte
      .push                 ( fv_stream_push_scoreboard                              ), // When ever the accumulated data has 64 bytes of valid content a push is triggered
      .pop                  ( pi_msg_rdy_i && po_msg_valid_o && fv_streaming_ongoing ), // DUT out when there is a valid and rdy and if it is streaming mode
      .num_elements         (               /* open */                     ),
      .sampled_out          (               /* open */                     ),
      .sym_data             (               /* open */                     ),
      .sampled_in           (                                              ),
      .must_read            (                                              )
    ); 

    lubis_scoreboard_m #(
      .WIDTH                (1                                ), 
      .DEPTH                (2                                ), 
      .BYPASS               (0                                )
    ) fv_stream_msg_strobe_scoreboard( 
      .clk                  (pi_clk                                                  ),     
      .rst                  (!pi_rst_b  || po_zeroize                                ),
      .soft_rst             (1'b0                                                    ),
      .full                 (1'b0                                                    ),    
      .empty                (1'b0                                                    ),   
      .data_in              ( fv_msg_buffer_strobe[fv_sym_data]                      ), 
      .data_out             (  po_msg_strobe_o[fv_sym_data]                          ), 
      .push                 ( fv_stream_push_scoreboard                              ), 
      .pop                  ( pi_msg_rdy_i && po_msg_valid_o && fv_streaming_ongoing ),
      .num_elements         (               /* open */                     ),
      .sampled_out          (               /* open */                     ),
      .sym_data             (               /* open */                     ),
      .sampled_in           (                                              ),
      .must_read            (                                              )
    ); 

    lubis_scoreboard_m #(
      .WIDTH                (1                                ), 
      .DEPTH                (1                                ), 
      .BYPASS               (0                                )
    ) fv_stream_msg_last_scoreboard( 
      .clk                  (pi_clk                                            ),     
      .rst                  (!pi_rst_b    || po_zeroize                        ),
      .soft_rst             (1'b0                                              ),
      .full                 (1'b0                                              ),    
      .empty                (1'b0                                              ),   
      .data_in              ( fv_msg_last                                      ), 
      .data_out             (  mldsa_ctrl.msg_done                             ), 
      .push                 ( fv_msg_last                                      ), 
      .pop                  ( fv_streaming_ongoing && mldsa_ctrl.msg_done  ),
      .num_elements         (               /* open */                     ),
      .sampled_out          (               /* open */                     ),
      .sym_data             (               /* open */                     ),
      .sampled_in           (                                              ),
      .must_read            (                                              )
    ); 

 lubis_scoreboard_m #(
      .WIDTH                (1                                ), 
      .DEPTH                (2                                ), 
      .BYPASS               (0                                )
 ) fv_stream_msg_push_pop_scoreboard( 
      .clk                  (pi_clk                                                  ),     
      .rst                  (!pi_rst_b   || po_zeroize                               ),
      .soft_rst             (1'b0                                                    ),
      .full                 (1'b0                                                    ),    
      .empty                (1'b0                                                    ),   
      .data_in              ( 1'b1                                                   ), 
      .data_out             ( pi_msg_rdy_i && po_msg_valid_o && fv_streaming_ongoing ), 
      .push                 ( fv_stream_push_scoreboard                              ), 
      .pop                  ( pi_msg_rdy_i && po_msg_valid_o && fv_streaming_ongoing ),
      .num_elements         (               /* open */                     ),
      .sampled_out          (               /* open */                     ),
      .sym_data             (               /* open */                     ),
      .sampled_in           (                                              ),
      .must_read            (                                              )
    ); 

    //If there is a push from the FV env then tthere should be a valid/pop from DUT in the next 2-3 cycles
    // If the message is a ctx message then the pop should happen in 3 cycles
    // If the message is a normal message then the pop should happen in 2 cycles since msg valid is flopped
    property stream_msg_buffer_if_push_then_pop;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_stream_push_scoreboard 
        |-> 
        ##[2:3] pi_msg_rdy_i && po_msg_valid_o
        ;endproperty
    assert_stream_msg_buffer_if_push_then_pop: assert property (stream_msg_buffer_if_push_then_pop);

    property stream_msg_buffer_if_push_then_pop_ctx;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_stream_push_scoreboard &&
        !fv_msg_last_ctx_reg_d2 && !fv_msg_flush_reg // defines it is a ctx message
        |-> 
        ##3 pi_msg_rdy_i && po_msg_valid_o
        ;endproperty
    assert_stream_msg_buffer_if_push_then_pop_ctx: assert property (stream_msg_buffer_if_push_then_pop_ctx);

     property stream_msg_buffer_if_push_then_pop_msg;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_stream_push_scoreboard &&
        (fv_msg_last_ctx_reg_d2 || fv_msg_flush_reg) // defines it is a normal message
        |-> 
        ##2 pi_msg_rdy_i && po_msg_valid_o
        ;endproperty
    assert_stream_msg_buffer_if_push_then_pop_msg: assert property (stream_msg_buffer_if_push_then_pop_msg);

    property stream_msg_buffer_if_no_push_then_no_pop;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        !fv_stream_push_scoreboard &&
        (fv_msg_last_ctx_reg_d2 || fv_msg_flush_reg) // defines it is a normal message
        |-> 
        ##2 !po_msg_valid_o
        ;endproperty
    assert_stream_msg_buffer_if_no_push_then_no_pop: assert property (stream_msg_buffer_if_no_push_then_no_pop);

    property stream_msg_buffer_if_no_push_then_no_pop_ctx;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        !fv_stream_push_scoreboard &&
        fv_streaming_ongoing &&     // need to be in streaming mode since in normal mode scroeboard push and last, flush are zero anyways
        !fv_msg_last_ctx_reg_d2 && !fv_msg_flush_reg // defines it is a ctx message
        ##1 !fv_msg_last_ctx_reg_d2 
        |-> 
        ##2 !po_msg_valid_o
    ;endproperty
    assert_stream_msg_buffer_if_no_push_then_no_pop_ctx: assert property (stream_msg_buffer_if_no_push_then_no_pop_ctx);

    property stream_msg_last_then_msg_done_strobe_0;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_msg_last &&
        fv_msg_buffer_strobe_extended == '0
        |-> 
        ##2 mldsa_ctrl.msg_done 
        ;endproperty
    assert_stream_msg_last_then_msg_done_strobe_0: assert property (stream_msg_last_then_msg_done_strobe_0);

     property stream_msg_last_then_msg_done_strobe_great_8;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_msg_last &&
        $countones(fv_msg_buffer_strobe_extended)> 8
        |-> 
        ##4 mldsa_ctrl.msg_done // additional cycle i.e 4 because in msg flush we check if strobe is zero and then leave causing extra delay
        ;endproperty
    assert_stream_msg_last_then_msg_done_strobe_great_8: assert property (stream_msg_last_then_msg_done_strobe_great_8);

    property stream_msg_last_then_msg_done_strobe_less_8;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        fv_msg_last &&
        $countones(fv_msg_buffer_strobe_extended) < 8 &&
        fv_msg_buffer_strobe_extended != '0
        |-> 
        ##3 mldsa_ctrl.msg_done 
        ;endproperty
    assert_stream_msg_last_then_msg_done_strobe_less_8: assert property (stream_msg_last_then_msg_done_strobe_less_8);

    // A streaming mode is effective only if the H_MU compute is necessary in signing and verifying
    property streaming_mode_state_from_wait;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT) &&
        ((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+1) ||
        (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1))
         |=> 
        (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && mldsa_ctrl.sampler_src == MLDSA_MSG_ID);
    endproperty
    assert_streaming_mode_state_from_wait: assert property (streaming_mode_state_from_wait);

    //  If it is not H_MU compute then the streaming mode is not effective
     property non_streaming_mode_state_from_wait;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT) &&
        !((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+1) ||
        (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1))
        ##1 (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)
         |-> 
         mldsa_ctrl.sampler_src != MLDSA_MSG_ID;
    endproperty
    assert_non_streaming_mode_state_from_wait: assert property (non_streaming_mode_state_from_wait);

   
    // Once streaming mode msg is loaded then should make a transition to FUNC_START
    property streaming_mode_from_msg_load_to_func_start;
        @(posedge pi_clk) disable iff(!pi_rst_b || po_zeroize)
        mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && 
        mldsa_ctrl.sampler_src == MLDSA_MSG_ID && 
        pi_abr_reg_hwif_out_i.MLDSA_CTRL.STREAM_MSG.value && 
        mldsa_ctrl.stream_msg_done
        |=> 
        (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START);
    endproperty
    assert_streaming_mode_from_msg_load_to_func_start: assert property (streaming_mode_from_msg_load_to_func_start);

   cover_no_valid_when_no_rdy: cover property (disable iff(!pi_rst_b || po_zeroize) (mldsa_ctrl.prim_ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && mldsa_ctrl.sampler_src == MLDSA_MSG_ID && !pi_msg_rdy_i && po_msg_valid_o));
endmodule
  