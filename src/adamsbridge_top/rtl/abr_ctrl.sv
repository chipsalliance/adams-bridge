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

//High level controller block for executing
//Adams Bridge functions
//  Keygen
//  Signing

`include "config_defines.svh"

module abr_ctrl
  import adamsbridge_reg_pkg::*;
  import sha3_pkg::*;
  import sampler_pkg::*;
  import abr_seq_pkg::*;
  import abr_params_pkg::*;
  import ntt_defines_pkg::*;
  #(
  )
  (
  input logic clk,
  input logic rst_b,
  output logic zeroize,

  output adamsbridge_reg__in_t abr_reg_hwif_in_o,
  input  adamsbridge_reg__out_t abr_reg_hwif_out_i,

  //sampler interface
  output abr_sampler_mode_e          sampler_mode_o,
  output logic                       sha3_start_o,
  output logic                       msg_start_o,
  output logic                       msg_valid_o,
  input  logic                       msg_rdy_i,
  output logic [MsgStrbW-1:0]        msg_strobe_o,
  output logic [MsgWidth-1:0]        msg_data_o[Sha3Share],
  output logic                       sampler_start_o,

  input  logic                       sampler_busy_i,
  input logic                        sampler_state_dv_i,
  input logic [sha3_pkg::StateW-1:0] sampler_state_data_i [Sha3Share],

  output logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr_o,

  //ntt interface
  output logic                        ntt_enable_o,
  output abr_ntt_mode_e               ntt_mode_o,
  output ntt_mem_addr_t               ntt_mem_base_addr_o,
  output pwo_mem_addr_t               pwo_mem_base_addr_o,
  input logic                         ntt_busy_i
  );

  logic [1:0] cmd_reg;

  logic adamsbridge_ready;

  logic keygen_process;
  logic signing_process;
  logic verifying_process;
  logic dilithium_valid_reg;

  //assign appropriate data to msg interface
  logic [ABR_OPR_WIDTH-1:0]  sampler_src;
  logic [15:0]               sampler_src_offset;
  logic [15:0]               sampler_iter;
  
  logic [SEED_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] seed_reg;
  logic [3:0][63:0] roh_reg;
  logic [7:0][63:0] roh_p_reg;
  logic [3:0][63:0] K_reg;

  logic seq_en;
  logic [abr_seq_pkg::ABR_PROG_ADDR_W-1 : 0] prog_cntr, prog_cntr_nxt;
  abr_seq_pkg::abr_seq_instr_t instr;

  logic msg_done;
  logic [MsgStrbW-1:0] last_msg_strobe;
  logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] msg_cnt;
  logic vld_cycle;

  logic error_flag_edge;
  logic subcomponent_busy;

  abr_ctrl_fsm_state_e ctrl_fsm_ps, ctrl_fsm_ns;

  adamsbridge_reg__in_t abr_reg_hwif_in;
  adamsbridge_reg__out_t abr_reg_hwif_out;

  assign abr_reg_hwif_in_o = abr_reg_hwif_in;
  assign abr_reg_hwif_out = abr_reg_hwif_out_i;

  always_comb adamsbridge_ready = (prog_cntr == DILITHIUM_RESET);

//HWIF to reg block
  always_comb abr_reg_hwif_in.reset_b = rst_b;
  always_comb abr_reg_hwif_in.hard_reset_b = rst_b; //FIXME interface needs a hard reset signal?
  always_comb abr_reg_hwif_in.adamsbridge_ready = adamsbridge_ready;
  always_comb cmd_reg = abr_reg_hwif_out.ADAMSBRIDGE_CTRL.CTRL.value;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_CTRL.CTRL.hwclr = |cmd_reg;
  
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_NAME[0].NAME.next = '0;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_NAME[1].NAME.next = '0;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_VERSION[0].VERSION.next = '0;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_VERSION[1].VERSION.next = '0;
  
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.READY.next = '1;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.VALID.next = dilithium_valid_reg;
  
  always_comb abr_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = '0;
  always_comb abr_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = '0;
  
  always_comb zeroize = abr_reg_hwif_out.ADAMSBRIDGE_CTRL.ZEROIZE.value;
  
  always_comb begin // adamsbridge reg writing
    for (int dword=0; dword < 1216; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN[dword].PRIVKEY_IN.hwclr = zeroize;
    end 
  
    for (int dword=0; dword < 1216; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT[dword].PRIVKEY_OUT.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 648; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_PUBKEY[dword].PUBKEY.hwclr = zeroize;
    end
  
    for (int dword=0; dword < SEED_NUM_DWORDS; dword++)begin
        seed_reg[dword] = abr_reg_hwif_out.ADAMSBRIDGE_SEED[SEED_NUM_DWORDS-1-dword].SEED.value;
        abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_SEED[dword].SEED.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 16; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 1149; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.we = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].SIGNATURE.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 8; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_SIGN_RND[dword].SIGN_RND.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 16; dword++)begin 
        abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.we = '0;       
        abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.next = '0;
        abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.hwclr = zeroize;
    end
  
    for (int dword=0; dword < 16; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_IV[dword].IV.hwclr = zeroize;
    end
  end
  
  always_comb begin : sampler_src_mux
    unique case (sampler_src) inside
      ABR_SEED_ID:  msg_data_o[0] = {seed_reg[{sampler_src_offset[1:0],1'b1}],seed_reg[{sampler_src_offset[1:0],1'b0}]};
      ABR_ROH_ID:   msg_data_o[0] = msg_done ? {48'b0,sampler_iter} : roh_reg[sampler_src_offset[1:0]];
      ABR_ROH_P_ID: msg_data_o[0] = msg_done ? {48'b0,sampler_iter} : roh_p_reg[sampler_src_offset[2:0]];
      default:      msg_data_o[0] = '0;
    endcase
  end
  
  //If we're storing state directly into registers, do that here
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      {K_reg, roh_p_reg, roh_reg} <= 0;
    end
    else if (zeroize) begin
      {K_reg, roh_p_reg, roh_reg} <= 0;
    end
    else if (sampler_state_dv_i) begin
      if (instr.operand3 == ABR_DEST_K_ROH_REG_ID) begin
        {K_reg, roh_p_reg, roh_reg} <= sampler_state_data_i[0][1023:0];
      end
    end
  end

  //FIXME need to optimize sequencer
  //Should be able to implement opcode to load next keccak data while sampler or ntt is running
  //requires a granularity of busy that is context aware of the current and next steps or
  //need a way to advance to the next step and understand when it can proceed and when it can't
  always_comb subcomponent_busy = (ctrl_fsm_ns != ABR_CTRL_IDLE) |
                                  sampler_busy_i |
                                  ntt_busy_i;
  always_comb error_flag_edge = 0;
  always_comb seq_en = 1;

  always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
      prog_cntr <= DILITHIUM_RESET;
    end
    else if(zeroize) begin
      prog_cntr <= DILITHIUM_RESET;
    end
    else begin
      if (error_flag_edge) begin
        prog_cntr <= DILITHIUM_ERROR;
      end
      else begin
        prog_cntr <= prog_cntr_nxt;
      end
    end
  end

  always_comb begin
    keygen_process      = 0;
    signing_process     = 0;
    verifying_process   = 0;
    dilithium_valid_reg = 0;
    prog_cntr_nxt = DILITHIUM_RESET;
    unique case (prog_cntr) inside
      DILITHIUM_RESET : begin 
        // Waiting for new valid command 
        unique case (cmd_reg) inside
          ABR_KEYGEN : begin  // keygen
            prog_cntr_nxt = DILITHIUM_KG_S;
            keygen_process = 1;
          end   
          ABR_SIGN : begin  // signing
            prog_cntr_nxt = DILITHIUM_ERROR; //FIXME
            signing_process = 1;
          end                                   
          ABR_VERIFY : begin  // verifying
            prog_cntr_nxt = DILITHIUM_ERROR; //fixme
            verifying_process = 1;
          end
          default : begin
            prog_cntr_nxt = DILITHIUM_RESET;
          end
        endcase
      end                
      DILITHIUM_KG_E : begin // end of keygen
        prog_cntr_nxt = DILITHIUM_RESET;
        dilithium_valid_reg = 1;
      end
      default : begin
        if (subcomponent_busy) begin //Stalled until sub-component is done
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
    endcase
  end

abr_seq abr_seq_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize),

  .en_i(seq_en),
  .addr_i(prog_cntr_nxt),
  .data_o(instr)
);

always_comb sampler_mode_o = instr.opcode.sampler_mode;
always_comb sampler_src_offset = {4'b0, msg_cnt}; //fixme

always_comb ntt_mode_o = instr.opcode.ntt_mode;
//FIXME one interface here?
always_comb ntt_mem_base_addr_o = '{src_base_addr:instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                    interim_base_addr:instr.operand2[ABR_MEM_ADDR_WIDTH-1:0],
                                    dest_base_addr:instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

always_comb pwo_mem_base_addr_o = '{pw_base_addr_b:instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src
                                    pw_base_addr_a:instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src or sampler src
                                    pw_base_addr_c:instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

//determine the number of bytes in the last message
//operand 2 contains the length of the message being fed to sha3
//shift a zero intot he strobe for each byte, and invert to get the valid bytes
always_comb last_msg_strobe = ~(MsgStrbW'('1) << instr.length[$clog2(MsgStrbW):0]);
 
always_comb vld_cycle = msg_valid_o & msg_rdy_i;

//Done when msg count is equal to length
//length is in bytes - compare against MSB from strobe width gets us the length in msg interface chunks
always_comb msg_done = msg_cnt >= instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)];

always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    msg_cnt <= 0;
  end
  else if (zeroize) begin
    msg_cnt <= 0;
  end
  else begin
    msg_cnt <= msg_done  ? 'd0 :
               vld_cycle ? msg_cnt + 'd1 : msg_cnt;
  end
end

//State logic
always_comb begin : ctrl_fsm_out_combo
    ctrl_fsm_ns = ctrl_fsm_ps;
    sha3_start_o = 0;
    msg_start_o = 0;
    msg_valid_o = 0;
    msg_strobe_o = 0;
    sampler_start_o = 0;
    sampler_src = 0;
    sampler_iter = 0;
    dest_base_addr_o = 0;
    ntt_enable_o = 0;

    unique case (ctrl_fsm_ps)
      ABR_CTRL_IDLE: begin
        //sampler enable go through sampler flow
        if (instr.opcode.sampler_en)
          ctrl_fsm_ns = ABR_CTRL_SHA3_START;
        else if (instr.opcode.ntt_en)
          ctrl_fsm_ns = ABR_CTRL_NTT_START;
      end
      ABR_CTRL_SHA3_START: begin
        ctrl_fsm_ns = ABR_CTRL_MSG_START;
        //drive start
        sha3_start_o = 1;
      end
      ABR_CTRL_MSG_START: begin
        ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
        msg_start_o = 1;
      end
      ABR_CTRL_MSG_LOAD: begin
        msg_valid_o = 1;
        sampler_src = instr.operand1;
        sampler_iter = instr.iter;
        if (msg_done) begin
          ctrl_fsm_ns = ABR_CTRL_SAMPLER_START;
          msg_strobe_o = last_msg_strobe;
        end else begin
          msg_strobe_o = '1;
        end
      end
      ABR_CTRL_SAMPLER_START: begin
        if (instr.opcode.ntt_en) ctrl_fsm_ns = ABR_CTRL_NTT_START;
        else ctrl_fsm_ns = ABR_CTRL_DONE;
        dest_base_addr_o = instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];
        sampler_start_o = 1;
      end
      ABR_CTRL_NTT_START: begin
        ctrl_fsm_ns = ABR_CTRL_DONE;
        ntt_enable_o = 1;
      end
      ABR_CTRL_DONE: begin
        if (~sampler_busy_i & ~ntt_busy_i) begin
          ctrl_fsm_ns = ABR_CTRL_IDLE;
        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : ctrl_fsm_flops
  if (!rst_b) begin
      ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else if (zeroize) begin
      ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else begin
      ctrl_fsm_ps <= ctrl_fsm_ns;
  end
end  

  `ABR_ASSERT_KNOWN(ERR_CTRL_FSM_X, {ctrl_fsm_ps}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_NTT_MEM_X, {ntt_mem_base_addr_o}, clk, !rst_b) 
  `ABR_ASSERT_KNOWN(ERR_PWO_MEM_X, {pwo_mem_base_addr_o}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_REG_HWIF_X, {abr_reg_hwif_in_o}, clk, !rst_b)

endmodule