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
  import abr_ctrl_pkg::*;
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

  //ntt interfaces
  output logic [1:0]                        ntt_enable_o,
  output abr_ntt_mode_e [1:0]               ntt_mode_o,
  output ntt_mem_addr_t [1:0]               ntt_mem_base_addr_o,
  output pwo_mem_addr_t [1:0]               pwo_mem_base_addr_o,
  input logic [1:0]                         ntt_busy_i,

  //aux interfaces
  output logic [1:0][ABR_MEM_ADDR_WIDTH-1:0] aux_src_base_addr_o,
  output logic [1:0][ABR_MEM_ADDR_WIDTH-1:0] aux_dest_base_addr_o,
  output logic decompose_start_o,
  input logic decompose_done_i,

  output logic skencode_enable_o,
  input mem_if_t skencode_keymem_if_i,
  input logic [DATA_WIDTH-1:0] skencode_wr_data_i,
  input logic skencode_done_i,

  output logic skdecode_enable_o,
  input mem_if_t [1:0] skdecode_keymem_if_i,
  output logic [1:0][DATA_WIDTH-1:0] skdecode_rd_data_o,
  input logic skdecode_done_i,

  output logic makehint_enable_o,
  input logic makehint_invalid_i,
  input logic makehint_done_i,
  input logic makehint_reg_wren_i,
  input logic [3:0][7:0] makehint_reg_wrdata_i,
  input logic [MEM_ADDR_WIDTH-1:0] makehint_reg_wr_addr_i,

  output logic normcheck_enable_o,
  output logic [1:0] normcheck_mode_o,
  input logic normcheck_invalid_i,
  input logic normcheck_done_i,

  output logic sigencode_enable_o,
  input mem_if_t sigencode_wr_req_i,
  input logic [1:0][3:0][19:0] sigencode_wr_data_i,
  input logic sigencode_done_i

  );

  logic [2:0] cmd_reg;

  logic adamsbridge_ready;

  logic keygen_process, keygen_process_nxt;
  logic signing_process, signing_process_nxt;
  logic verifying_process, verifying_process_nxt;
  logic keygen_signing_process, keygen_signing_process_nxt;
  logic dilithium_valid_reg;
  logic keygen_done;
  logic signature_done;
  logic verify_done;

  //assign appropriate data to msg interface
  logic [ABR_OPR_WIDTH-1:0]  sampler_src;
  logic [15:0]               sampler_src_offset;
  logic [15:0]               sampler_iter;
  
  logic [SEED_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] seed_reg;
  logic [MSG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] msg_reg;
  logic [SIGN_RND_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] sign_rnd_reg;
  logic [3:0][63:0] roh_reg;
  logic [7:0][63:0] roh_p_reg;
  logic [3:0][63:0] K_reg;
  logic [7:0][63:0] mu_reg;
  logic [15:0] kappa_reg;
  logic update_kappa;

  logic seq_en;
  logic [ABR_PROG_ADDR_W-1 : 0] prog_cntr, prog_cntr_nxt;
  abr_seq_instr_t instr;
  logic [ABR_PROG_ADDR_W-1 : 0] sign_prog_cntr, sign_prog_cntr_nxt;
  abr_seq_instr_t sign_instr;

  logic msg_done;
  logic [MsgStrbW-1:0] last_msg_strobe;
  logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] msg_cnt;
  logic vld_cycle;

  logic error_flag_edge;
  logic subcomponent_busy;
  logic sign_subcomponent_busy;

  abr_ctrl_fsm_state_e ctrl_fsm_ps, ctrl_fsm_ns;
  abr_ctrl_fsm_state_e sign_ctrl_fsm_ps, sign_ctrl_fsm_ns;

  adamsbridge_reg__in_t abr_reg_hwif_in;
  adamsbridge_reg__out_t abr_reg_hwif_out;

  abr_privkey_u privatekey_in;
  abr_signature_u signature_reg;

  //sync points for dual sequencers
  logic y_valid, set_y_valid, clear_y_valid;
  logic w0_valid, set_w0_valid, clear_w0_valid;
  logic c_valid, set_c_valid, clear_c_valid;
  logic signature_valid, set_signature_valid, clear_signature_valid;
  
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
  
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.READY.next = adamsbridge_ready;
  always_comb abr_reg_hwif_in.ADAMSBRIDGE_STATUS.VALID.next = dilithium_valid_reg;
  
  always_comb abr_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = '0;
  always_comb abr_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = '0;
  
  always_comb zeroize = abr_reg_hwif_out.ADAMSBRIDGE_CTRL.ZEROIZE.value;
  
  always_comb begin // adamsbridge reg writing
 
    for (int dword=0; dword < PUBKEY_NUM_DWORDS; dword++)begin
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
  
    for (int dword=0; dword < MSG_NUM_DWORDS; dword++)begin
      msg_reg[dword] = abr_reg_hwif_out.ADAMSBRIDGE_MSG[MSG_NUM_DWORDS-1-dword].MSG.value;
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.we = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_MSG[dword].MSG.hwclr = zeroize;
    end
  
    for (int dword=0; dword < SIGNATURE_NUM_DWORDS; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].rd_ack = abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req & ~abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req_is_wr; //FIXME protect with signature done
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].wr_ack = abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req & abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req_is_wr; //FIXME protect with busy
        abr_reg_hwif_in.ADAMSBRIDGE_SIGNATURE[dword].rd_data = signature_reg.raw[dword]; 
    end
  
    for (int dword=0; dword < SIGN_RND_NUM_DWORDS; dword++)begin
      sign_rnd_reg[dword] = abr_reg_hwif_out.ADAMSBRIDGE_SIGN_RND[SIGN_RND_NUM_DWORDS-1-dword].SIGN_RND.value;
      abr_reg_hwif_in.ADAMSBRIDGE_SIGN_RND[dword].SIGN_RND.hwclr = zeroize;
    end
  
    for (int dword=0; dword < VERIFY_RES_NUM_DWORDS; dword++)begin 
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.we = '0;       
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.next = '0;
      abr_reg_hwif_in.ADAMSBRIDGE_VERIFY_RES[dword].VERIFY_RES.hwclr = zeroize;
    end
  
    for (int dword=0; dword < IV_NUM_DWORDS; dword++)begin
        abr_reg_hwif_in.ADAMSBRIDGE_IV[dword].IV.hwclr = zeroize;
    end
  end
  
  logic [1:0][10:0] skdecode_rdaddr;
  logic [1:0] skdecode_rden;

  always_comb begin
    for (int port = 0; port < 2; port++) begin
      skdecode_rdaddr[port] = skdecode_keymem_if_i[port].addr[10:0];
      skdecode_rden[port] = skdecode_keymem_if_i[port].rd_wr_en == RW_READ;
    end
  end

  abr_ram_regout
  #(
    .DEPTH(PRIVKEY_NUM_DWORDS),
    .DATA_WIDTH(DATA_WIDTH),
    .NUM_RD_PORTS(2)
  ) abr_sk_in_mem
  (
    .clk_i(clk),
    .zeroize_i(zeroize),
    .we_i(abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN.wr_ack),
    .waddr_i(abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.addr[12:2]),
    .wdata_i(abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.wr_data),
    .re_i(skdecode_rden),
    .raddr_i(skdecode_rdaddr),
    .rdata_o(skdecode_rd_data_o),
    .reg_o(privatekey_in)
  );

  assign abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN.wr_ack = abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.req & abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.req_is_wr;
  //no reads to PRIVKEY_IN allowed - just ack it
  assign abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN.rd_ack = abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.req & ~abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_IN.req_is_wr;
  assign abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_IN.rd_data = '0;

  logic [DATA_WIDTH-1:0] privkey_out_rdata;

  abr_ram_regout
  #(
    .DEPTH(PRIVKEY_NUM_DWORDS),
    .DATA_WIDTH(DATA_WIDTH)
  ) abr_sk_out_mem
  (
    .clk_i(clk),
    .zeroize_i(zeroize),
    .we_i((skencode_keymem_if_i.rd_wr_en == RW_WRITE)),
    .waddr_i(skencode_keymem_if_i.addr[10:0]),
    .wdata_i(skencode_wr_data_i),
    .re_i(abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req & ~abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req_is_wr),
    .raddr_i(abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.addr[12:2]),
    .rdata_o(privkey_out_rdata),
    .reg_o()
  );

  //No write to PRIVKEY_OUT allowed - just ack it
  assign abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT.wr_ack = abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req & abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req_is_wr;

  //Signature
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      signature_reg <= '0;
    end else if (zeroize | clear_signature_valid) begin
      signature_reg <= '0;
    end else begin
      for (int dword = 0; dword < SIGNATURE_NUM_DWORDS; dword++) begin
        if (abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req & abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].req_is_wr) begin
          signature_reg.raw[dword] <= abr_reg_hwif_out.ADAMSBRIDGE_SIGNATURE[dword].wr_data;
        end
      end
      //HW write c
      if (sampler_state_dv_i) begin
        if (instr.operand3 == ABR_DEST_SIG_C_REG_ID) begin
          signature_reg.enc.c <= sampler_state_data_i[0][511:0];
        end
      end
      //HW write z
      for (int chunk = 0; chunk < 224; chunk++) begin
        if ((sigencode_wr_req_i.rd_wr_en == RW_WRITE) & (sigencode_wr_req_i.addr[8:1] == chunk)) begin

          signature_reg.enc.z[chunk*5 +: 5] <= sigencode_wr_data_i;
        end
      end
      //HW write h
      for (int dword = 0; dword < SIGNATURE_H_NUM_DWORDS; dword++) begin
        if (makehint_reg_wren_i & (makehint_reg_wr_addr_i == dword)) begin
          signature_reg.enc.h[dword] <= signature_reg.enc.h[dword] | makehint_reg_wrdata_i;
        end
      end
    end
  end

  //ack the read request one clock later
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT.rd_ack <= 0;
    end
    else begin
      abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT.rd_ack <= abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req & ~abr_reg_hwif_out.ADAMSBRIDGE_PRIVKEY_OUT.req_is_wr;
    end
  end

  always_comb abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT.rd_data = abr_reg_hwif_in.ADAMSBRIDGE_PRIVKEY_OUT.rd_ack ? privkey_out_rdata : 0;

  always_comb begin : sampler_src_mux
    unique case (sampler_src) inside
      ABR_SEED_ID:        msg_data_o[0] = {seed_reg[{sampler_src_offset[1:0],1'b1}],seed_reg[{sampler_src_offset[1:0],1'b0}]};
      ABR_ROH_ID:         msg_data_o[0] = msg_done ? {48'b0,sampler_iter} : roh_reg[sampler_src_offset[1:0]];
      ABR_ROH_P_ID:       msg_data_o[0] = msg_done ? {48'b0,sampler_iter} : roh_p_reg[sampler_src_offset[2:0]];
      ABR_TR_ID:          msg_data_o[0] = signing_process ? privatekey_in.enc.tr[sampler_src_offset[2:0]] : '0; //FIXME keygen+signing
      ABR_MSG_ID:         msg_data_o[0] = {msg_reg[{sampler_src_offset[2:0],1'b1}],msg_reg[{sampler_src_offset[2:0],1'b0}]};
      ABR_K_ID:           msg_data_o[0] = K_reg[sampler_src_offset[1:0]];
      ABR_MU_ID:          msg_data_o[0] = mu_reg[sampler_src_offset[2:0]];
      ABR_SIGN_RND_ID:    msg_data_o[0] = {sign_rnd_reg[{sampler_src_offset[1:0],1'b1}],sign_rnd_reg[{sampler_src_offset[1:0],1'b0}]};
      ABR_ROH_P_KAPPA_ID: msg_data_o[0] = msg_done ? {48'b0,(kappa_reg + sampler_iter[2:0])} : roh_p_reg[sampler_src_offset[2:0]];
      ABR_SIG_C_REG_ID:   msg_data_o[0] = {signature_reg.enc.c[{sampler_src_offset[2:0],1'b1}], signature_reg.enc.c[{sampler_src_offset[2:0],1'b0}]};
      default:            msg_data_o[0] = '0;
    endcase
  end
  
  //If we're storing state directly into registers, do that here
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      {K_reg, roh_p_reg, roh_reg} <= 0;
      mu_reg <= 0;
    end
    else if (zeroize) begin
      {K_reg, roh_p_reg, roh_reg} <= 0;
      mu_reg <= 0;
    end
    else if (sampler_state_dv_i) begin
      if (instr.operand3 == ABR_DEST_K_ROH_REG_ID) begin
        {K_reg, roh_p_reg, roh_reg} <= sampler_state_data_i[0][1023:0];
      end
      else if (instr.operand3 == ABR_DEST_MU_REG_ID) begin
        mu_reg <= sampler_state_data_i[0][511:0];
      end
      else if (instr.operand3 == ABR_DEST_ROH_P_REG_ID) begin
        roh_p_reg <= sampler_state_data_i[0][511:0];
      end
    end
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      kappa_reg <= '0;
    end
    else if (zeroize) begin
      kappa_reg <= '0;
    end
    else if (update_kappa) begin
      kappa_reg <= kappa_reg + 7;
    end
  end
  
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      dilithium_valid_reg <= '0;
      y_valid <= '0;
      w0_valid <= '0;
      c_valid <= '0;
      signature_valid <= 0;
      keygen_process <= 0;
      signing_process <= 0;
      verifying_process <= 0;
      keygen_signing_process <= 0;
    end
    else if (zeroize) begin
      dilithium_valid_reg <= '0;
      y_valid <= '0;
      w0_valid <= '0;
      c_valid <= '0;
      signature_valid <= 0;
      signature_valid <= 0;
      keygen_process <= 0;
      signing_process <= 0;
      verifying_process <= 0;
      keygen_signing_process <= 0;
    end
    else begin
      dilithium_valid_reg <= dilithium_valid_reg | 
                             (keygen_process & keygen_done) |
                             (signing_process & signature_done);
      y_valid <= set_y_valid ? 1 :
                 clear_y_valid ? 0 :
                 y_valid;
      w0_valid <= set_w0_valid ? 1 :
                  clear_w0_valid ? 0 :
                  w0_valid;
      c_valid <= set_c_valid ? 1 :
                 clear_c_valid ? 0 :
                 c_valid;
      signature_valid <= set_signature_valid ? 1 :
                         clear_signature_valid ? 0 :
                         signature_valid;
      keygen_process <= keygen_process | keygen_process_nxt;
      signing_process <= signing_process | signing_process_nxt;
      verifying_process <= verifying_process | verifying_process_nxt;
      keygen_signing_process <= keygen_signing_process | keygen_signing_process_nxt;
    end
  end
  
  always_comb clear_signature_valid = ((makehint_done_i & makehint_invalid_i) | (normcheck_done_i & normcheck_invalid_i));

//Primary sequencer for keygen, signing, and verify

  //FIXME need to optimize sequencer
  //Should be able to implement opcode to load next keccak data while sampler or ntt is running
  //requires a granularity of busy that is context aware of the current and next steps or
  //need a way to advance to the next step and understand when it can proceed and when it can't
  always_comb subcomponent_busy = !(ctrl_fsm_ns inside {ABR_CTRL_IDLE, ABR_CTRL_MSG_WAIT}) |
                                  sampler_busy_i |
                                  ntt_busy_i[0];
  always_comb error_flag_edge = 0;
  always_comb seq_en = 1;
  //program counter
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
  //Subroutine decode
  always_comb begin
    keygen_process_nxt = 0;
    signing_process_nxt = 0;
    verifying_process_nxt = 0;
    keygen_signing_process_nxt = 0;
    keygen_done = 0;
    set_y_valid = 0;
    set_w0_valid = 0;
    set_c_valid = 0;
    update_kappa = 0;
    prog_cntr_nxt = DILITHIUM_RESET;

    unique case (prog_cntr) inside
      DILITHIUM_RESET : begin 
        // Waiting for new valid command 
        unique case (cmd_reg) inside
          ABR_KEYGEN : begin  // keygen
            prog_cntr_nxt = DILITHIUM_KG_S;
            keygen_process_nxt = 1;
          end   
          ABR_SIGN : begin  // signing
            prog_cntr_nxt = DILITHIUM_SIGN_S;
            signing_process_nxt  = 1;
          end                                   
          ABR_VERIFY : begin  // verifying
            prog_cntr_nxt = DILITHIUM_ERROR; //fixme
            verifying_process_nxt  = 1;
          end                          
          ABR_KEYGEN_SIGN : begin  // KEYGEN + SIGNING 
            prog_cntr_nxt = DILITHIUM_KG_S;
            keygen_signing_process_nxt  = 1;
          end
          default : begin
            prog_cntr_nxt = DILITHIUM_RESET;
          end
        endcase
      end        
      DILITHIUM_KG_JUMP_SIGN : begin
        //Jump to signing process
        if (keygen_signing_process) begin
          prog_cntr_nxt = DILITHIUM_SIGN_S;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      DILITHIUM_KG_E : begin // end of keygen
        prog_cntr_nxt = DILITHIUM_RESET;
        keygen_done = 1;
      end
      //START of Y access - check if Y is still valid
      DILITHIUM_SIGN_CHECK_Y_CLR : begin
        if (y_valid | w0_valid) begin //Stalled until Y can be overwritten //FIXME reads are colliding
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of Y access - SET Y valid
      DILITHIUM_SIGN_SET_Y : begin
        set_y_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      //START of W0 access - check if W0 is still valid
      DILITHIUM_SIGN_CHECK_W0_CLR : begin
        if (w0_valid) begin //Stalled until W0 can be overwritten
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of W0 access - SET W0 valid
      DILITHIUM_SIGN_SET_W0 : begin
        set_w0_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      //START of C access - check if C is still valid
      DILITHIUM_SIGN_CHECK_C_CLR : begin
        if (c_valid) begin //Stalled until C can be overwritten
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of C access - SET C valid
      DILITHIUM_SIGN_SET_C : begin
        set_c_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      DILITHIUM_SIGN_E : begin // end of challenge generation
        //increment kappa value
        update_kappa = 1;
        //restart challenge generation
        prog_cntr_nxt = DILITHIUM_SIGN_CHECK_Y_CLR;
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

//Controller instruction decode - drives sampler and primary ntt
//FIXME latch the sampler mode here
  always_comb begin
    sampler_mode_o = ABR_SAMPLER_NONE;
    if (instr.opcode.sampler_en) begin
      if (instr.opcode.ntt_en & instr.opcode.mode.ntt_mode inside {ABR_PWM_SMPL, ABR_PWM_ACCUM_SMPL}) begin
        sampler_mode_o = ABR_REJ_SAMPLER;
      end else begin
        sampler_mode_o = instr.opcode.mode.sampler_mode;
      end
    end else if (instr.opcode.keccak_en) begin
      sampler_mode_o = instr.opcode.mode.sampler_mode;
    end else if (instr.opcode.aux_en) begin
      if (instr.opcode.mode.aux_mode == ABR_DECOMP) begin
        sampler_mode_o = ABR_SHAKE256;
      end
    end
  end

  always_comb begin
    ntt_mode_o[0] = ABR_NTT_NONE;
    if (instr.opcode.ntt_en) begin
      ntt_mode_o[0] = instr.opcode.mode.ntt_mode;
    end
  end

  always_comb sampler_src_offset = {4'b0, msg_cnt}; //fixme

  //FIXME one interface here?
  always_comb ntt_mem_base_addr_o[0] = '{src_base_addr:instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                         interim_base_addr:instr.operand2[ABR_MEM_ADDR_WIDTH-1:0],
                                         dest_base_addr:instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

  always_comb pwo_mem_base_addr_o[0] = '{pw_base_addr_b:instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src
                                         pw_base_addr_a:instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src or sampler src
                                         pw_base_addr_c:instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

  always_comb dest_base_addr_o = instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src_base_addr_o[0] = instr.operand1[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_dest_base_addr_o[0] = instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];

//determine the number of bytes in the last message
//operand 2 contains the length of the message being fed to sha3
//shift a zero into the strobe for each byte, and invert to get the valid bytes
always_comb last_msg_strobe = ~(MsgStrbW'('1) << instr.length[$clog2(MsgStrbW)+1:0]);
 
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
always_comb begin : primary_ctrl_fsm_out_combo
    ctrl_fsm_ns = ctrl_fsm_ps;
    sha3_start_o = 0;
    msg_start_o = 0;
    msg_valid_o = 0;
    msg_strobe_o = 0;
    sampler_start_o = 0;
    sampler_src = 0;
    sampler_iter = 0;
    ntt_enable_o[0] = 0;
    decompose_start_o = 0;
    skencode_enable_o = 0;

    unique case (ctrl_fsm_ps)
      ABR_CTRL_IDLE: begin
        //load keccak data to SIPO
        if (instr.opcode.keccak_en)
          ctrl_fsm_ns = ABR_CTRL_SHA3_START;
        //start sampler flow, data already driven to SIPO
        else if (instr.opcode.sampler_en | instr.opcode.ntt_en | instr.opcode.aux_en)
          ctrl_fsm_ns = ABR_CTRL_FUNC_START;
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
          msg_strobe_o = last_msg_strobe;
          if (instr.opcode.sampler_en) ctrl_fsm_ns = ABR_CTRL_FUNC_START;
          else ctrl_fsm_ns = ABR_CTRL_MSG_WAIT;
        end else begin
          msg_strobe_o = '1;
        end
      end
      ABR_CTRL_MSG_WAIT: begin
        //load another message
        if (instr.opcode.keccak_en) ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
        //kick off the sampler
        else if (instr.opcode.sampler_en | instr.opcode.aux_en | instr.opcode.ntt_en) ctrl_fsm_ns = ABR_CTRL_FUNC_START;
        else ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
      end
      ABR_CTRL_FUNC_START: begin
        ctrl_fsm_ns = ABR_CTRL_DONE;
        sampler_start_o = instr.opcode.sampler_en;
        ntt_enable_o[0] = instr.opcode.ntt_en;
        if (instr.opcode.aux_en) begin
          decompose_start_o = (instr.opcode.mode.aux_mode == ABR_DECOMP);
          skencode_enable_o = (instr.opcode.mode.aux_mode == ABR_SKENCODE);
        end
      end
      ABR_CTRL_DONE: begin
        if ((~sampler_busy_i & ~ntt_busy_i[0] & ~instr.opcode.aux_en) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == ABR_DECOMP) & decompose_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == ABR_SKENCODE) & skencode_done_i)) begin
          
              ctrl_fsm_ns = ABR_CTRL_IDLE;

        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : primary_ctrl_fsm_flops
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

abr_seq_prim abr_seq_prim_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize),

  .en_i(seq_en),
  .addr_i(prog_cntr_nxt),
  .data_o(instr)
);

  //Second sequencer for simultaneous signing operations

  //FIXME need to optimize sequencer
  //Should be able to implement opcode to load next keccak data while sampler or ntt is running
  //requires a granularity of busy that is context aware of the current and next steps or
  //need a way to advance to the next step and understand when it can proceed and when it can't
  always_comb sign_subcomponent_busy = !(sign_ctrl_fsm_ns inside {ABR_CTRL_IDLE}) |
                                        ntt_busy_i[1];
  //program counter
  always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
      sign_prog_cntr <= DILITHIUM_RESET;
    end
    else if(zeroize) begin
      sign_prog_cntr <= DILITHIUM_RESET;
    end
    else begin
      if (error_flag_edge) begin
        sign_prog_cntr <= DILITHIUM_ERROR;
      end
      else begin
        sign_prog_cntr <= sign_prog_cntr_nxt;
      end
    end
  end

  //subroutine decode
  always_comb begin
    sign_prog_cntr_nxt = DILITHIUM_RESET;
    clear_c_valid = 0;
    clear_y_valid = 0;
    clear_w0_valid = 0;
    set_signature_valid = 0;
    signature_done = 0;
    unique case (sign_prog_cntr) inside
      DILITHIUM_RESET : begin 
        // Waiting for new valid command 
        unique case (cmd_reg) inside
          ABR_KEYGEN : begin  // keygen
            sign_prog_cntr_nxt = DILITHIUM_RESET;
          end   
          ABR_SIGN : begin  // signing
            sign_prog_cntr_nxt = DILITHIUM_SIGN_INIT_S;
          end                                   
          ABR_VERIFY : begin  // verifying
            sign_prog_cntr_nxt = DILITHIUM_RESET;
          end                     
          ABR_KEYGEN_SIGN : begin  // KEYGEN + SIGNING 
            sign_prog_cntr_nxt = DILITHIUM_RESET;
          end
          default : begin
            sign_prog_cntr_nxt = DILITHIUM_RESET;
          end   
        endcase
        if (prog_cntr == DILITHIUM_KG_JUMP_SIGN) begin
          sign_prog_cntr_nxt = DILITHIUM_SIGN_INIT_S+8; //FIXME
        end
      end
      //START of C access - check if C is valid
      DILITHIUM_SIGN_CHECK_C_VLD : begin
        if (c_valid) begin
          set_signature_valid = 1;
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr;
        end
      end
      //END of C access - SET C valid
      //Need to protect C the entire validity checks so that challenge generation doesn't overwrite the valid c~
      //FIXME another place to consider odd/even counter on challenge/validity
      DILITHIUM_SIGN_CLEAR_C : begin
        clear_c_valid = 1;
        sign_prog_cntr_nxt = DILITHIUM_SIGN_CHECK_C_VLD;
      end
      //START of Y access - check if Y is valid
      DILITHIUM_SIGN_CHECK_Y_VLD : begin
        if (y_valid & w0_valid) begin 
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr;
        end
      end
      //END of Y access - SET Y valid
      DILITHIUM_SIGN_CLEAR_Y : begin
        clear_y_valid = 1;
        sign_prog_cntr_nxt = sign_prog_cntr + 1;
      end
      //START of W0 access - check if W0 is valid
      DILITHIUM_SIGN_CHECK_W0_VLD : begin
        if (w0_valid) begin 
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr ;
        end
      end
      //END of W0 access - SET W0 valid
      DILITHIUM_SIGN_CLEAR_W0 : begin
        clear_w0_valid = 1;
        sign_prog_cntr_nxt = sign_prog_cntr + 1;
      end
      DILITHIUM_SIGN_GEN_S : begin // end of validity checks
        if (signature_valid) begin
          sign_prog_cntr_nxt = sign_prog_cntr + 2; //Jump to encode
        end else begin
          //restart
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
      end
      DILITHIUM_SIGN_GEN_E : begin // Successful signature generation
        signature_done = 1;
      end
      default : begin
        if (sign_subcomponent_busy) begin //Stalled until sub-component is done
          sign_prog_cntr_nxt = sign_prog_cntr;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
      end
    endcase
  end

  //instruciton decode - drives secondary ntt
  always_comb begin
    ntt_mode_o[1] = ABR_NTT_NONE;
    if (sign_instr.opcode.ntt_en) begin
      ntt_mode_o[1] = sign_instr.opcode.mode.ntt_mode;
    end
  end

  //FIXME one interface here?
  always_comb ntt_mem_base_addr_o[1] = '{src_base_addr:sign_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                         interim_base_addr:sign_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0],
                                         dest_base_addr:sign_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

  always_comb pwo_mem_base_addr_o[1] = '{pw_base_addr_b:sign_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src
                                         pw_base_addr_a:sign_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //FIXME PWO src or sampler src
                                         pw_base_addr_c:sign_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

  always_comb aux_src_base_addr_o[1] = sign_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_dest_base_addr_o[1] = sign_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];

  always_comb normcheck_mode_o = sign_instr.iter[1:0];

//State logic
always_comb begin : secpondary_ctrl_fsm_out_combo
    sign_ctrl_fsm_ns = sign_ctrl_fsm_ps;
    ntt_enable_o[1] = 0;
    skdecode_enable_o = 0;
    makehint_enable_o = 0;
    normcheck_enable_o = 0;
    sigencode_enable_o = 0;

    unique case (sign_ctrl_fsm_ps)
      ABR_CTRL_IDLE: begin
        //Start function
        if (sign_instr.opcode.sampler_en)
          sign_ctrl_fsm_ns = ABR_CTRL_ERROR;
        if (sign_instr.opcode.ntt_en | sign_instr.opcode.aux_en)
          sign_ctrl_fsm_ns = ABR_CTRL_FUNC_START;
      end
      ABR_CTRL_FUNC_START: begin
        sign_ctrl_fsm_ns = ABR_CTRL_DONE;
        ntt_enable_o[1] = sign_instr.opcode.ntt_en;
        if (sign_instr.opcode.aux_en) begin
          skdecode_enable_o = (sign_instr.opcode.mode.aux_mode == ABR_SKDECODE);
          makehint_enable_o = (sign_instr.opcode.mode.aux_mode == ABR_MAKEHINT);
          normcheck_enable_o = (sign_instr.opcode.mode.aux_mode == ABR_NORMCHK);
          sigencode_enable_o = (sign_instr.opcode.mode.aux_mode == ABR_SIGENC);
        end
      end
      ABR_CTRL_DONE: begin
        if ((sign_instr.opcode.ntt_en & ~ntt_busy_i[1]) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == ABR_SKDECODE) & skdecode_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == ABR_MAKEHINT) & makehint_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == ABR_NORMCHK) & normcheck_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == ABR_SIGENC) & sigencode_done_i) ) begin
          sign_ctrl_fsm_ns = ABR_CTRL_IDLE;
        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : secondary_ctrl_fsm_flops
  if (!rst_b) begin
      sign_ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else if (zeroize) begin
      sign_ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else begin
      sign_ctrl_fsm_ps <= sign_ctrl_fsm_ns;
  end
end  

abr_seq_sec abr_seq_sec_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize),

  .en_i(seq_en),
  .addr_i(sign_prog_cntr_nxt),
  .data_o(sign_instr)
);

  `ABR_ASSERT_KNOWN(ERR_CTRL_FSM_X, {ctrl_fsm_ps}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_SIGN_CTRL_FSM_X, {sign_ctrl_fsm_ps}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_NTT_MEM_X, {ntt_mem_base_addr_o}, clk, !rst_b) 
  `ABR_ASSERT_KNOWN(ERR_PWO_MEM_X, {pwo_mem_base_addr_o}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_REG_HWIF_X, {abr_reg_hwif_in_o}, clk, !rst_b)

endmodule