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

`include "mldsa_config_defines.svh"

module mldsa_ctrl
  import mldsa_reg_pkg::*;
  import abr_sha3_pkg::*;
  import mldsa_sampler_pkg::*;
  import mldsa_ctrl_pkg::*;
  import mldsa_params_pkg::*;
  import ntt_defines_pkg::*;
  #(
  )
  (
  input logic clk,
  input logic rst_b,
  output logic zeroize,

  output mldsa_reg__in_t mldsa_reg_hwif_in_o,
  input  mldsa_reg__out_t mldsa_reg_hwif_out_i,

  //sampler interface
  output mldsa_sampler_mode_e        sampler_mode_o,
  output logic                       sha3_start_o,
  output logic                       msg_start_o,
  output logic                       msg_valid_o,
  input  logic                       msg_rdy_i,
  output logic [MsgStrbW-1:0]        msg_strobe_o,
  output logic [MsgWidth-1:0]        msg_data_o[Sha3Share],
  output logic                       sampler_start_o,

  input  logic                       sampler_busy_i,
  input logic                        sampler_state_dv_i,
  input logic [abr_sha3_pkg::StateW-1:0] sampler_state_data_i [Sha3Share],

  output logic [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_addr_o,

  //ntt interfaces
  output logic [1:0]                        ntt_enable_o,
  output mldsa_ntt_mode_e [1:0]             ntt_mode_o,
  output ntt_mem_addr_t [1:0]               ntt_mem_base_addr_o,
  output pwo_mem_addr_t [1:0]               pwo_mem_base_addr_o,
  input logic [1:0]                         ntt_busy_i,

  //aux interfaces
  output logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_src0_base_addr_o,
  output logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_src1_base_addr_o,
  output logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_dest_base_addr_o,

  output logic power2round_enable_o,
  input mem_if_t [1:0] pwr2rnd_keymem_if_i,
  input logic [1:0] [DATA_WIDTH-1:0] pwr2rnd_wr_data_i,
  input logic pk_t1_wren_i,
  input logic [7:0][9:0] pk_t1_wrdata_i, // TODO: change to parameter
  input logic [7:0] pk_t1_wr_addr_i, // TODO: change to parameter
  input logic power2round_done_i,

  output logic decompose_enable_o,
  output logic decompose_mode_o,
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
  input logic [MLDSA_MEM_ADDR_WIDTH-1:0] makehint_reg_wr_addr_i,

  output logic normcheck_enable_o,
  output logic [1:0] normcheck_mode_o,
  output logic [MLDSA_MEM_ADDR_WIDTH-1:0] normcheck_src_addr_o,
  input logic normcheck_invalid_i,
  input logic normcheck_done_i,

  output logic sigencode_enable_o,
  input mem_if_t sigencode_wr_req_i,
  input logic [1:0][3:0][19:0] sigencode_wr_data_i,
  input logic sigencode_done_i,

  output logic pkdecode_enable_o,
  input logic [7:0] pkdecode_rd_addr_i,
  output logic [7:0][T1_COEFF_W-1:0] pkdecode_rd_data_o,
  input logic pkdecode_done_i,


  output logic sigdecode_h_enable_o, 
  output logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] signature_h_o,
  input logic sigdecode_h_invalid_i,
  input logic sigdecode_h_done_i,

  output logic sigdecode_z_enable_o, 
  input mem_if_t sigdecode_z_rd_req_i,
  output logic [1:0][3:0][19:0] sigdecode_z_rd_data_o,
  input logic sigdecode_z_done_i,

  output logic lfsr_enable_o,
  output logic [1:0][LFSR_W-1:0] lfsr_seed_o,

  //Interrupts
  output logic error_intr,
  output logic notif_intr

  );

  logic [2:0] cmd_reg;

  logic mldsa_ready;

  logic keygen_process, keygen_process_nxt;
  logic signing_process, signing_process_nxt;
  logic verifying_process, verifying_process_nxt;
  logic keygen_signing_process, keygen_signing_process_nxt;
  logic mldsa_valid_reg;
  logic keygen_done;
  logic signature_done;
  logic verify_done;

  //assign appropriate data to msg interface
  logic [MLDSA_OPR_WIDTH-1:0]  sampler_src;
  logic [15:0]               sampler_src_offset;
  logic [15:0]               sampler_imm;
  
  logic [ENTROPY_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] entropy_reg;
  logic [SEED_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] seed_reg;
  logic [MSG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] msg_reg;
  logic [SIGN_RND_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] sign_rnd_reg;
  logic [7:0][63:0] rho_p_reg;
  logic [3:0][63:0] rho_reg;
  logic [7:0][63:0] mu_reg;
  logic [15:0] kappa_reg;
  logic update_kappa;

  logic seq_en;
  logic [MLDSA_PROG_ADDR_W-1 : 0] prog_cntr, prog_cntr_nxt;
  mldsa_seq_instr_t instr;
  logic [MLDSA_PROG_ADDR_W-1 : 0] sign_prog_cntr, sign_prog_cntr_nxt;
  mldsa_seq_instr_t sign_instr;

  logic msg_done;
  logic [MsgStrbW-1:0] last_msg_strobe;
  logic [MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)] msg_cnt;
  logic vld_cycle;

  logic error_flag_edge;
  logic subcomponent_busy;
  logic sign_subcomponent_busy;

  mldsa_ctrl_fsm_state_e ctrl_fsm_ps, ctrl_fsm_ns;
  mldsa_ctrl_fsm_state_e sign_ctrl_fsm_ps, sign_ctrl_fsm_ns;

  mldsa_reg__in_t mldsa_reg_hwif_in;
  mldsa_reg__out_t mldsa_reg_hwif_out;

  mldsa_privkey_u privatekey_reg;
  mldsa_signature_u signature_reg;
  mldsa_pubkey_u publickey_reg;

  //sync points for dual sequencers
  logic y_valid, set_y_valid, clear_y_valid;
  logic w0_valid, set_w0_valid, clear_w0_valid;
  logic c_valid, set_c_valid, clear_c_valid;

  //signature and verify validity checks
  logic signature_valid, set_signature_valid, clear_signature_valid;
  logic verify_valid, set_verify_valid, clear_verify_valid;
  
  //shared aux functions
  logic [1:0] normcheck_enable;

  //Interrupts
  logic mldsa_status_done_d, mldsa_status_done_p;

  logic set_entropy;
  logic [7:0][63:0] lfsr_entropy_reg;
  logic [MsgWidth-1:0] counter_reg;
  
  assign mldsa_reg_hwif_in_o = mldsa_reg_hwif_in;
  assign mldsa_reg_hwif_out = mldsa_reg_hwif_out_i;

  always_comb mldsa_ready = (prog_cntr == MLDSA_RESET);

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
      counter_reg <= '0;
    else
      counter_reg <= counter_reg + 1;
  end

//HWIF to reg block
  always_comb mldsa_reg_hwif_in.reset_b = rst_b;
  always_comb mldsa_reg_hwif_in.hard_reset_b = rst_b; //FIXME interface needs a hard reset signal?
  always_comb mldsa_reg_hwif_in.mldsa_ready = mldsa_ready;
  always_comb cmd_reg = mldsa_reg_hwif_out.MLDSA_CTRL.CTRL.value;
  always_comb mldsa_reg_hwif_in.MLDSA_CTRL.CTRL.hwclr = |cmd_reg;
  
  always_comb mldsa_reg_hwif_in.MLDSA_NAME[0].NAME.next = '0;
  always_comb mldsa_reg_hwif_in.MLDSA_NAME[1].NAME.next = '0;
  always_comb mldsa_reg_hwif_in.MLDSA_VERSION[0].VERSION.next = '0;
  always_comb mldsa_reg_hwif_in.MLDSA_VERSION[1].VERSION.next = '0;
  
  always_comb mldsa_reg_hwif_in.MLDSA_STATUS.READY.next = mldsa_ready;
  always_comb mldsa_reg_hwif_in.MLDSA_STATUS.VALID.next = mldsa_valid_reg;
  
  always_comb zeroize = mldsa_reg_hwif_out.MLDSA_CTRL.ZEROIZE.value;
  
  always_comb begin // mldsa reg writing 
    for (int dword=0; dword < PUBKEY_NUM_DWORDS; dword++)begin
        mldsa_reg_hwif_in.MLDSA_PUBKEY[dword].rd_ack = mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req & ~mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req_is_wr; //FIXME protect with key done
        mldsa_reg_hwif_in.MLDSA_PUBKEY[dword].wr_ack = mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req & mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req_is_wr; //FIXME protect with busy
        mldsa_reg_hwif_in.MLDSA_PUBKEY[dword].rd_data = publickey_reg.raw[PUBKEY_NUM_DWORDS-1-dword]; 
    end

    for (int dword=0; dword < ENTROPY_NUM_DWORDS; dword++)begin
      entropy_reg[dword] = mldsa_reg_hwif_out.MLDSA_ENTROPY[ENTROPY_NUM_DWORDS-1-dword].ENTROPY.value;
      mldsa_reg_hwif_in.MLDSA_ENTROPY[dword].ENTROPY.hwclr = zeroize;
    end

    for (int dword=0; dword < SEED_NUM_DWORDS; dword++)begin
      seed_reg[dword] = mldsa_reg_hwif_out.MLDSA_SEED[SEED_NUM_DWORDS-1-dword].SEED.value;
      mldsa_reg_hwif_in.MLDSA_SEED[dword].SEED.we = '0;
      mldsa_reg_hwif_in.MLDSA_SEED[dword].SEED.next = '0;
      mldsa_reg_hwif_in.MLDSA_SEED[dword].SEED.hwclr = zeroize;
    end
  
    for (int dword=0; dword < MSG_NUM_DWORDS; dword++)begin
      msg_reg[dword] = mldsa_reg_hwif_out.MLDSA_MSG[MSG_NUM_DWORDS-1-dword].MSG.value;
      mldsa_reg_hwif_in.MLDSA_MSG[dword].MSG.we = '0;
      mldsa_reg_hwif_in.MLDSA_MSG[dword].MSG.next = '0;
      mldsa_reg_hwif_in.MLDSA_MSG[dword].MSG.hwclr = zeroize;
    end
  
    for (int dword=0; dword < SIGNATURE_NUM_DWORDS; dword++)begin
        mldsa_reg_hwif_in.MLDSA_SIGNATURE[dword].rd_ack = mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req & ~mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req_is_wr; //FIXME protect with signature done
        mldsa_reg_hwif_in.MLDSA_SIGNATURE[dword].wr_ack = mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req & mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req_is_wr; //FIXME protect with busy
        mldsa_reg_hwif_in.MLDSA_SIGNATURE[dword].rd_data = signature_reg.raw[SIGNATURE_NUM_DWORDS-1-dword]; 
    end
  
    for (int dword=0; dword < SIGN_RND_NUM_DWORDS; dword++)begin
      sign_rnd_reg[dword] = mldsa_reg_hwif_out.MLDSA_SIGN_RND[SIGN_RND_NUM_DWORDS-1-dword].SIGN_RND.value;
      mldsa_reg_hwif_in.MLDSA_SIGN_RND[dword].SIGN_RND.hwclr = zeroize;
    end
  
    for (int dword=0; dword < VERIFY_RES_NUM_DWORDS; dword++)begin 
      mldsa_reg_hwif_in.MLDSA_VERIFY_RES[dword].VERIFY_RES.we = verify_valid & sampler_state_dv_i & (instr.operand3 == MLDSA_DEST_VERIFY_RES_REG_ID);       
      mldsa_reg_hwif_in.MLDSA_VERIFY_RES[VERIFY_RES_NUM_DWORDS-1-dword].VERIFY_RES.next = sampler_state_data_i[0][dword*32 +: 32];
      mldsa_reg_hwif_in.MLDSA_VERIFY_RES[dword].VERIFY_RES.hwclr = zeroize | clear_verify_valid;
    end
  
    for (int dword=0; dword < ENTROPY_NUM_DWORDS; dword++)begin
        mldsa_reg_hwif_in.MLDSA_ENTROPY[dword].ENTROPY.hwclr = zeroize;
    end
  end

  //Generate a pulse to trig the interrupt after finishing the operation
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
      mldsa_status_done_d <= 1'b0;
    else if (zeroize)
      mldsa_status_done_d <= 1'b0;
    else
      mldsa_status_done_d <= mldsa_reg_hwif_in.MLDSA_STATUS.VALID.next;
  end

  always_comb mldsa_status_done_p = mldsa_reg_hwif_in.MLDSA_STATUS.VALID.next & !mldsa_status_done_d;

  assign error_intr = mldsa_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
  assign notif_intr = mldsa_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;

  always_comb begin
    mldsa_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = '0; //TODO
    mldsa_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = mldsa_status_done_p;
  end
  
  logic [1:0][10:0] skdecode_rdaddr;
  logic [1:0] skdecode_rden;

  always_comb begin
    for (int port = 0; port < 2; port++) begin
      skdecode_rdaddr[port] = skdecode_keymem_if_i[port].addr[10:0];
      skdecode_rden[port] = skdecode_keymem_if_i[port].rd_wr_en == RW_READ;
    end
  end

  //Private Key External Memory
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      privatekey_reg <= '0;
    end else if (zeroize) begin
      privatekey_reg <= '0;
    end else begin
      //SW write port
      if (mldsa_reg_hwif_in.MLDSA_PRIVKEY_IN.wr_ack & mldsa_ready) begin
        privatekey_reg.raw[PRIVKEY_NUM_DWORDS-1-mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.addr[12:2]] <= mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.wr_data;
      end
      //HW write rho
      if (sampler_state_dv_i) begin
        if (instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
          privatekey_reg.enc.rho <= sampler_state_data_i[0][255:0]; //FIXME optimize this to be shared with pubkey?
        end
      end
      //HW write K
      if (sampler_state_dv_i) begin
        if (instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
          privatekey_reg.enc.K <= sampler_state_data_i[0][1023:768];
        end
      end
      //HW write tr
      if (sampler_state_dv_i) begin
        if (instr.operand3 == MLDSA_DEST_TR_REG_ID) begin
          privatekey_reg.enc.tr <= sampler_state_data_i[0][511:0];
        end
      end
      //HW write s1s2
      if (skencode_keymem_if_i.rd_wr_en == RW_WRITE) begin
        privatekey_reg.enc.s1s2[skencode_keymem_if_i.addr[8:0]] <= skencode_wr_data_i;
      end
      //HW write t0
      if (pwr2rnd_keymem_if_i[0].rd_wr_en == RW_WRITE) begin
        privatekey_reg.enc.t0[pwr2rnd_keymem_if_i[0].addr[9:1]] <= pwr2rnd_wr_data_i; //fixme one interface
      end
    end 
  end

  //private key read ports
  logic [DATA_WIDTH-1:0] privkey_out_rdata;

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      skdecode_rd_data_o <= '0;
      privkey_out_rdata <= '0;
    end else if (zeroize) begin
      skdecode_rd_data_o <= '0;
      privkey_out_rdata <= '0;
    end else begin
      for (int i = 0; i < 2; i++) begin 
        if (skdecode_rden[i]) begin
          skdecode_rd_data_o[i] <= privatekey_reg.raw[skdecode_rdaddr[i]];
        end
      end
      if (mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & ~mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr) begin
        privkey_out_rdata <= privatekey_reg.raw[PRIVKEY_NUM_DWORDS-1-mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.addr[12:2]];
      end
    end
  end

  assign mldsa_reg_hwif_in.MLDSA_PRIVKEY_IN.wr_ack = mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.req & mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.req_is_wr;
  //no reads to PRIVKEY_IN allowed - just ack it
  assign mldsa_reg_hwif_in.MLDSA_PRIVKEY_IN.rd_ack = mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.req & ~mldsa_reg_hwif_out.MLDSA_PRIVKEY_IN.req_is_wr;
  assign mldsa_reg_hwif_in.MLDSA_PRIVKEY_IN.rd_data = '0;


  //ack the read request one clock later
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      mldsa_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_ack <= 0;
    end
    else begin
      mldsa_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_ack <= mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & ~mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr;
    end
  end

  always_comb mldsa_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_data = mldsa_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_ack ? privkey_out_rdata : 0;

  //No write to PRIVKEY_OUT allowed - just ack it
  assign mldsa_reg_hwif_in.MLDSA_PRIVKEY_OUT.wr_ack = mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & mldsa_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr;

  //Signature
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      signature_reg <= '0;
    end else if (zeroize) begin
      signature_reg <= '0;
    end else begin
      for (int dword = 0; dword < SIGNATURE_NUM_DWORDS; dword++) begin
        if (mldsa_ready & mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req & mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].req_is_wr) begin
          signature_reg.raw[SIGNATURE_NUM_DWORDS-1-dword] <= mldsa_reg_hwif_out.MLDSA_SIGNATURE[dword].wr_data;
        end
      end
      //HW write c
      if (sampler_state_dv_i) begin
        if (instr.operand3 == MLDSA_DEST_SIG_C_REG_ID) begin
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
        if (set_signature_valid) begin
          signature_reg.enc.h[dword] <= '0;
        end else if (makehint_reg_wren_i & (makehint_reg_wr_addr_i == dword)) begin
          signature_reg.enc.h[dword] <= signature_reg.enc.h[dword] | makehint_reg_wrdata_i;
        end
      end
    end
  end

  always_comb begin
    //HW read h
    for (int i = 0; i < SIGNATURE_H_VALID_NUM_BYTES; i++) begin
      signature_h_o[i] = signature_reg.enc.h[i/4][(i%4)*8 +: 8];
    end
  end

  //HW read z
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      sigdecode_z_rd_data_o <= '0;
      pkdecode_rd_data_o <= '0;
    end else begin
      if ((sigdecode_z_rd_req_i.rd_wr_en == RW_READ)) begin
        sigdecode_z_rd_data_o <= signature_reg.enc.z[sigdecode_z_rd_req_i.addr[8:1]*5 +: 5];
      end
      if (1) begin //fixme read enable or remove flop
        pkdecode_rd_data_o <= publickey_reg.enc.t1[pkdecode_rd_addr_i*8 +: 8];
      end
    end
  end

  //Public Key
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      publickey_reg <= '0;
    end else if (zeroize) begin
      publickey_reg <= '0;
    end else begin
      for (int dword = 0; dword < PUBKEY_NUM_DWORDS; dword++) begin
        if (mldsa_ready & mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req & mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].req_is_wr) begin
          publickey_reg.raw[PUBKEY_NUM_DWORDS-1-dword] <= mldsa_reg_hwif_out.MLDSA_PUBKEY[dword].wr_data;
        end
      end
      //HW write rho
      if (sampler_state_dv_i) begin
        if (instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
          publickey_reg.enc.rho <= sampler_state_data_i[0][255:0];
        end
      end
      //HW write t1
      for (int coeff = 0; coeff < T1_NUM_COEFF; coeff++) begin 
        if (pk_t1_wren_i & (pk_t1_wr_addr_i == coeff[10:3])) begin //pubkey t1 write interface
          publickey_reg.enc.t1[coeff] <= pk_t1_wrdata_i[coeff[2:0]];
        end
      end
    end
  end

  //concatenate OID and MSG to make msg prime
  logic [MSG_NUM_DWORDS-1+4 : 0][DATA_WIDTH-1:0] msg_p_reg;

  always_comb msg_p_reg = {24'h0, msg_reg, PREHASH_OID, 8'h00, 8'h01};

  always_comb rho_reg = verifying_process ? publickey_reg.enc.rho : privatekey_reg.enc.rho;

  always_comb begin : sampler_src_mux
    unique case (sampler_src) inside
      MLDSA_SEED_ID:        msg_data_o[0] = msg_done ? {48'b0,sampler_imm} : {seed_reg[{sampler_src_offset[1:0],1'b1}],seed_reg[{sampler_src_offset[1:0],1'b0}]};
      MLDSA_RHO_ID:         msg_data_o[0] = msg_done ? {48'b0,sampler_imm} : rho_reg[sampler_src_offset[1:0]];
      MLDSA_RHO_P_ID:       msg_data_o[0] = msg_done ? {48'b0,sampler_imm} : rho_p_reg[sampler_src_offset[2:0]];
      MLDSA_TR_ID:          msg_data_o[0] = privatekey_reg.enc.tr[sampler_src_offset[2:0]];
      MLDSA_MSG_ID:         msg_data_o[0] = {msg_p_reg[{sampler_src_offset[3:0],1'b1}],msg_p_reg[{sampler_src_offset[3:0],1'b0}]};
      MLDSA_K_ID:           msg_data_o[0] = privatekey_reg.enc.K[sampler_src_offset[1:0]];
      MLDSA_MU_ID:          msg_data_o[0] = mu_reg[sampler_src_offset[2:0]];
      MLDSA_SIGN_RND_ID:    msg_data_o[0] = {sign_rnd_reg[{sampler_src_offset[1:0],1'b1}],sign_rnd_reg[{sampler_src_offset[1:0],1'b0}]};
      MLDSA_RHO_P_KAPPA_ID: msg_data_o[0] = msg_done ? {48'b0,(kappa_reg + sampler_imm[2:0])} : rho_p_reg[sampler_src_offset[2:0]];
      MLDSA_SIG_C_REG_ID:   msg_data_o[0] = {signature_reg.enc.c[{sampler_src_offset[2:0],1'b1}], signature_reg.enc.c[{sampler_src_offset[2:0],1'b0}]};
      MLDSA_PK_REG_ID:      msg_data_o[0] = {publickey_reg.raw[{sampler_src_offset[8:0],1'b1}],publickey_reg.raw[{sampler_src_offset[8:0],1'b0}]};
      MLDSA_ENTROPY_ID:     msg_data_o[0] = lfsr_entropy_reg[sampler_src_offset[2:0]];
      MLDSA_CNT_ID:         msg_data_o[0] = counter_reg;
      default:              msg_data_o[0] = '0;
    endcase
  end
  
  //If we're storing state directly into registers, do that here
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      rho_p_reg <= 0;
      mu_reg <= 0;
    end
    else if (zeroize) begin
      rho_p_reg <= 0;
      mu_reg <= 0;
    end
    else if (sampler_state_dv_i) begin
      if (instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
        rho_p_reg <= sampler_state_data_i[0][767:256];
      end
      else if (instr.operand3 == MLDSA_DEST_MU_REG_ID) begin
        mu_reg <= sampler_state_data_i[0][511:0];
      end
      else if (instr.operand3 == MLDSA_DEST_RHO_P_REG_ID) begin
        rho_p_reg <= sampler_state_data_i[0][511:0];
      end
    end
  end

  // without zeroize to make it more complex
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      lfsr_seed_o <= '0;
      lfsr_entropy_reg <= '0;
    end
    else if (set_entropy) begin
      lfsr_entropy_reg <= lfsr_entropy_reg ^ entropy_reg;
    end
    else if (sampler_state_dv_i) begin
      if (instr.operand3 == MLDSA_DEST_LFSR_SEED_REG_ID) begin
          lfsr_seed_o <= sampler_state_data_i[0][2*LFSR_W-1:0];
          lfsr_entropy_reg <= sampler_state_data_i[0][2*LFSR_W+511:2*LFSR_W];
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
      mldsa_valid_reg <= '0;
      y_valid <= '0;
      w0_valid <= '0;
      c_valid <= '0;
      signature_valid <= 0;
      verify_valid <= 0;
      keygen_process <= 0;
      signing_process <= 0;
      verifying_process <= 0;
      keygen_signing_process <= 0;
    end
    else if (zeroize) begin
      mldsa_valid_reg <= '0;
      y_valid <= '0;
      w0_valid <= '0;
      c_valid <= '0;
      signature_valid <= 0;
      verify_valid <= 0;
      keygen_process <= 0;
      signing_process <= 0;
      verifying_process <= 0;
      keygen_signing_process <= 0;
    end
    else begin
      mldsa_valid_reg <= mldsa_valid_reg | 
                             (keygen_process & keygen_done) |
                             (signing_process & signature_done) |
                             (verifying_process & verify_done);
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
      verify_valid <= set_verify_valid ? 1 :
                      clear_verify_valid ? 0 :
                      verify_valid;
      keygen_process <= keygen_process | keygen_process_nxt;
      signing_process <= signing_process | signing_process_nxt;
      verifying_process <= verifying_process | verifying_process_nxt;
      keygen_signing_process <= keygen_signing_process | keygen_signing_process_nxt;
    end
  end
  
  //FIXME check if aux mode is set appropriately?
  always_comb clear_signature_valid = signing_process & ((makehint_done_i & makehint_invalid_i) | (normcheck_done_i & normcheck_invalid_i));

  //FIXME jump to done if this happens, could cause x reads (or fix sigdecode to not stop early)
  always_comb clear_verify_valid = verifying_process & ((normcheck_done_i & normcheck_invalid_i) | 
                                   (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & sigdecode_h_invalid_i));
                                   
//Primary sequencer for keygen, signing, and verify

  //FIXME need to optimize sequencer
  //Should be able to implement opcode to load next keccak data while sampler or ntt is running
  //requires a granularity of busy that is context aware of the current and next steps or
  //need a way to advance to the next step and understand when it can proceed and when it can't
  always_comb subcomponent_busy = !(ctrl_fsm_ns inside {MLDSA_CTRL_IDLE, MLDSA_CTRL_MSG_WAIT}) |
                                  sampler_busy_i |
                                  ntt_busy_i[0];
  always_comb error_flag_edge = 0;
  always_comb seq_en = 1;
  //program counter
  always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
      prog_cntr <= MLDSA_RESET;
    end
    else if(zeroize) begin
      prog_cntr <= MLDSA_RESET;
    end
    else begin
      if (error_flag_edge) begin
        prog_cntr <= MLDSA_ERROR;
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
    verify_done = 0;
    set_y_valid = 0;
    set_w0_valid = 0;
    set_c_valid = 0;
    update_kappa = 0;
    set_verify_valid = 0;
    set_entropy = 0;
    prog_cntr_nxt = MLDSA_RESET;

    unique case (prog_cntr) inside
      MLDSA_RESET : begin 
        // Waiting for new valid command 
        unique case (cmd_reg) inside
          MLDSA_KEYGEN : begin  // keygen
            prog_cntr_nxt = MLDSA_KG_S;
            keygen_process_nxt = 1;
            set_entropy = 1;
          end   
          MLDSA_SIGN : begin  // signing
            prog_cntr_nxt = MLDSA_SIGN_RND_S;
            signing_process_nxt  = 1;
            set_entropy = 1;
          end                                   
          MLDSA_VERIFY : begin  // verifying
            prog_cntr_nxt = MLDSA_VERIFY_S;
            verifying_process_nxt  = 1;
            set_verify_valid = 1;
          end                          
          MLDSA_KEYGEN_SIGN : begin  // KEYGEN + SIGNING 
            prog_cntr_nxt = MLDSA_KG_S;
            keygen_signing_process_nxt  = 1;
            set_entropy = 1;
          end
          default : begin
            prog_cntr_nxt = MLDSA_RESET;
          end
        endcase
      end        
      MLDSA_KG_JUMP_SIGN : begin
        //Jump to signing process
        if (keygen_signing_process) begin
          prog_cntr_nxt = MLDSA_SIGN_S;
          signing_process_nxt  = 1;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      MLDSA_KG_E : begin // end of keygen
        //prog_cntr_nxt = MLDSA_RESET;
        keygen_done = 1;
      end
      //START of Y access - check if Y is still valid
      MLDSA_SIGN_CHECK_Y_CLR : begin
        if (y_valid | w0_valid) begin //Stalled until Y can be overwritten //FIXME reads are colliding
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of Y access - SET Y valid
      MLDSA_SIGN_SET_Y : begin
        set_y_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      //START of W0 access - check if W0 is still valid
      MLDSA_SIGN_CHECK_W0_CLR : begin
        if (w0_valid) begin //Stalled until W0 can be overwritten
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of W0 access - SET W0 valid
      MLDSA_SIGN_SET_W0 : begin
        set_w0_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      //START of C access - check if C is still valid
      MLDSA_SIGN_CHECK_C_CLR : begin
        if (c_valid) begin //Stalled until C can be overwritten
          prog_cntr_nxt = prog_cntr;
        end
        else begin
          prog_cntr_nxt = prog_cntr + 1;
        end
      end
      //END of C access - SET C valid
      MLDSA_SIGN_SET_C : begin
        set_c_valid = 1;
        prog_cntr_nxt = prog_cntr + 1;
      end
      MLDSA_SIGN_E : begin // end of challenge generation
        //increment kappa value
        update_kappa = 1;
        //restart challenge generation
        prog_cntr_nxt = MLDSA_SIGN_CHECK_Y_CLR;
      end
      MLDSA_VERIFY_E : begin // end of verify flow
        verify_done = 1;
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
    sampler_mode_o = MLDSA_SAMPLER_NONE;
    if (instr.opcode.sampler_en) begin
      if (instr.opcode.ntt_en & instr.opcode.mode.ntt_mode inside {MLDSA_PWM_SMPL, MLDSA_PWM_ACCUM_SMPL}) begin
        sampler_mode_o = MLDSA_REJ_SAMPLER;
      end else begin
        sampler_mode_o = instr.opcode.mode.sampler_mode;
      end
    end else if (instr.opcode.keccak_en) begin
      sampler_mode_o = instr.opcode.mode.sampler_mode;
    end else if (instr.opcode.aux_en) begin
      if (instr.opcode.mode.aux_mode == MLDSA_DECOMP) begin
        sampler_mode_o = MLDSA_SHAKE256;
      end
    end
  end

  always_comb begin
    ntt_mode_o[0] = MLDSA_NTT_NONE;
    if (instr.opcode.ntt_en) begin
      ntt_mode_o[0] = instr.opcode.mode.ntt_mode;
    end
  end

  always_comb sampler_src_offset = {4'b0, msg_cnt}; //fixme

  //FIXME one interface here?
  always_comb ntt_mem_base_addr_o[0] = '{src_base_addr:instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0],
                                         interim_base_addr:instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0],
                                         dest_base_addr:instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0]};

  always_comb pwo_mem_base_addr_o[0] = '{pw_base_addr_b:instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0], //FIXME PWO src
                                         pw_base_addr_a:instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0], //FIXME PWO src or sampler src
                                         pw_base_addr_c:instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0]};

  always_comb dest_base_addr_o = instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src0_base_addr_o[0] = instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src1_base_addr_o[0] = instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0];
  always_comb aux_dest_base_addr_o[0] = instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0];

//determine the number of bytes in the last message
//operand 2 contains the length of the message being fed to sha3
//shift a zero into the strobe for each byte, and invert to get the valid bytes
always_comb last_msg_strobe = ~(MsgStrbW'('1) << instr.length[$clog2(MsgStrbW)-1:0]);
 
always_comb vld_cycle = msg_valid_o & msg_rdy_i;

//Done when msg count is equal to length
//length is in bytes - compare against MSB from strobe width gets us the length in msg interface chunks
always_comb msg_done = msg_cnt >= instr.length[MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)];

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

always_comb decompose_mode_o = instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_USEHINT);

//State logic
always_comb begin : primary_ctrl_fsm_out_combo
    ctrl_fsm_ns = ctrl_fsm_ps;
    sha3_start_o = 0;
    msg_start_o = 0;
    msg_valid_o = 0;
    msg_strobe_o = 0;
    sampler_start_o = 0;
    sampler_src = 0;
    sampler_imm = 0;
    ntt_enable_o[0] = 0;
    power2round_enable_o = 0;
    decompose_enable_o = 0;
    skencode_enable_o = 0;
    pkdecode_enable_o = 0;
    sigdecode_h_enable_o = 0;
    sigdecode_z_enable_o = 0;
    normcheck_enable[0] = 0;
    lfsr_enable_o = 0;

    unique case (ctrl_fsm_ps)
      MLDSA_CTRL_IDLE: begin
        //load keccak data to SIPO
        if (instr.opcode.keccak_en)
          ctrl_fsm_ns = MLDSA_CTRL_SHA3_START;
        //start sampler flow, data already driven to SIPO
        else if (instr.opcode.sampler_en | instr.opcode.ntt_en | instr.opcode.aux_en)
          ctrl_fsm_ns = MLDSA_CTRL_FUNC_START;
      end
      MLDSA_CTRL_SHA3_START: begin
        ctrl_fsm_ns = MLDSA_CTRL_MSG_START;
        //drive start
        sha3_start_o = 1;
      end
      MLDSA_CTRL_MSG_START: begin
        ctrl_fsm_ns = MLDSA_CTRL_MSG_LOAD;
        msg_start_o = 1;
      end
      MLDSA_CTRL_MSG_LOAD: begin
        msg_valid_o = 1;
        sampler_src = instr.operand1;
        sampler_imm = instr.imm;
        if (msg_done) begin
          msg_strobe_o = last_msg_strobe;
          if (instr.opcode.sampler_en) ctrl_fsm_ns = MLDSA_CTRL_FUNC_START;
          else ctrl_fsm_ns = MLDSA_CTRL_MSG_WAIT;
        end else begin
          msg_strobe_o = '1;
        end
      end
      MLDSA_CTRL_MSG_WAIT: begin
        //load another message
        if (instr.opcode.keccak_en) ctrl_fsm_ns = MLDSA_CTRL_MSG_LOAD;
        //kick off the sampler
        else if (instr.opcode.sampler_en | instr.opcode.aux_en | instr.opcode.ntt_en) ctrl_fsm_ns = MLDSA_CTRL_FUNC_START;
        else ctrl_fsm_ns = MLDSA_CTRL_MSG_LOAD;
      end
      MLDSA_CTRL_FUNC_START: begin
        ctrl_fsm_ns = MLDSA_CTRL_DONE;
        sampler_start_o = instr.opcode.sampler_en;
        ntt_enable_o[0] = instr.opcode.ntt_en;
        if (instr.opcode.aux_en) begin
          power2round_enable_o = (instr.opcode.mode.aux_mode == MLDSA_PWR2RND);
          decompose_enable_o = (instr.opcode.mode.aux_mode inside {MLDSA_DECOMP,MLDSA_USEHINT});
          skencode_enable_o = (instr.opcode.mode.aux_mode == MLDSA_SKENCODE);
          pkdecode_enable_o = (instr.opcode.mode.aux_mode == MLDSA_PKDECODE);
          sigdecode_h_enable_o = (instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H);
          sigdecode_z_enable_o = (instr.opcode.mode.aux_mode == MLDSA_SIGDEC_Z);
          normcheck_enable[0] = (instr.opcode.mode.aux_mode == MLDSA_NORMCHK);
          lfsr_enable_o = (instr.opcode.mode.aux_mode == MLDSA_LFSR);
        end
      end
      MLDSA_CTRL_DONE: begin
        if ((~sampler_busy_i & ~ntt_busy_i[0] & ~instr.opcode.aux_en) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode inside {MLDSA_DECOMP,MLDSA_USEHINT}) & decompose_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_PWR2RND) & power2round_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_SKENCODE) & skencode_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_PKDECODE) & pkdecode_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & sigdecode_h_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_SIGDEC_Z) & sigdecode_z_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_NORMCHK) & normcheck_done_i) |
            (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_LFSR)) ) begin
          
              ctrl_fsm_ns = MLDSA_CTRL_IDLE;

        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : primary_ctrl_fsm_flops
  if (!rst_b) begin
      ctrl_fsm_ps <= MLDSA_CTRL_IDLE;
  end
  else if (zeroize) begin
      ctrl_fsm_ps <= MLDSA_CTRL_IDLE;
  end
  else begin
      ctrl_fsm_ps <= ctrl_fsm_ns;
  end
end  

mldsa_seq_prim mldsa_seq_prim_inst
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
  always_comb sign_subcomponent_busy = !(sign_ctrl_fsm_ns inside {MLDSA_CTRL_IDLE}) |
                                        ntt_busy_i[1];
  //program counter
  always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
      sign_prog_cntr <= MLDSA_RESET;
    end
    else if(zeroize) begin
      sign_prog_cntr <= MLDSA_RESET;
    end
    else begin
      if (error_flag_edge) begin
        sign_prog_cntr <= MLDSA_ERROR;
      end
      else begin
        sign_prog_cntr <= sign_prog_cntr_nxt;
      end
    end
  end

  //subroutine decode
  always_comb begin
    sign_prog_cntr_nxt = MLDSA_RESET;
    clear_c_valid = 0;
    clear_y_valid = 0;
    clear_w0_valid = 0;
    set_signature_valid = 0;
    signature_done = 0;
    unique case (sign_prog_cntr) inside
      MLDSA_RESET : begin 
        // Waiting for new valid command 
        unique case (cmd_reg) inside
          MLDSA_KEYGEN : begin  // keygen
            sign_prog_cntr_nxt = MLDSA_RESET;
          end   
          MLDSA_SIGN : begin  // signing
            sign_prog_cntr_nxt = MLDSA_SIGN_INIT_S;
          end                                   
          MLDSA_VERIFY : begin  // verifying
            sign_prog_cntr_nxt = MLDSA_RESET;
          end                     
          MLDSA_KEYGEN_SIGN : begin  // KEYGEN + SIGNING 
            sign_prog_cntr_nxt = MLDSA_RESET;
          end
          default : begin
            sign_prog_cntr_nxt = MLDSA_RESET;
          end   
        endcase
        if (keygen_signing_process & (prog_cntr == MLDSA_KG_JUMP_SIGN)) begin
          sign_prog_cntr_nxt = MLDSA_SIGN_INIT_S;
        end
      end
      //START of C access - check if C is valid
      MLDSA_SIGN_CHECK_C_VLD : begin
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
      MLDSA_SIGN_CLEAR_C : begin
        clear_c_valid = 1;
        sign_prog_cntr_nxt = MLDSA_SIGN_CHECK_C_VLD;
      end
      //START of Y access - check if Y is valid
      MLDSA_SIGN_CHECK_Y_VLD : begin
        if (y_valid & w0_valid) begin 
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr;
        end
      end
      //END of Y access - SET Y valid
      MLDSA_SIGN_CLEAR_Y : begin
        clear_y_valid = 1;
        sign_prog_cntr_nxt = sign_prog_cntr + 1;
      end
      //START of W0 access - check if W0 is valid
      MLDSA_SIGN_CHECK_W0_VLD : begin
        if (w0_valid) begin 
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
        else begin
          sign_prog_cntr_nxt = sign_prog_cntr ;
        end
      end
      //END of W0 access - SET W0 valid
      MLDSA_SIGN_CLEAR_W0 : begin
        clear_w0_valid = 1;
        sign_prog_cntr_nxt = sign_prog_cntr + 1;
      end
      MLDSA_SIGN_GEN_S : begin // end of validity checks
        if (signature_valid) begin
          sign_prog_cntr_nxt = sign_prog_cntr + 2; //Jump to encode
        end else begin
          //restart
          sign_prog_cntr_nxt = sign_prog_cntr + 1;
        end
      end
      MLDSA_SIGN_GEN_E : begin // Successful signature generation
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
    ntt_mode_o[1] = MLDSA_NTT_NONE;
    if (sign_instr.opcode.ntt_en) begin
      ntt_mode_o[1] = sign_instr.opcode.mode.ntt_mode;
    end
  end

  //FIXME one interface here?
  always_comb ntt_mem_base_addr_o[1] = '{src_base_addr:sign_instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0],
                                         interim_base_addr:sign_instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0],
                                         dest_base_addr:sign_instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0]};

  always_comb pwo_mem_base_addr_o[1] = '{pw_base_addr_b:sign_instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0], //FIXME PWO src
                                         pw_base_addr_a:sign_instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0], //FIXME PWO src or sampler src
                                         pw_base_addr_c:sign_instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0]};

  always_comb aux_src0_base_addr_o[1] = sign_instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src1_base_addr_o[1] = sign_instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0];
  always_comb aux_dest_base_addr_o[1] = sign_instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0];

  always_comb normcheck_mode_o = (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? instr.imm[1:0] :
                                 (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? sign_instr.imm[1:0] : '0;
  always_comb normcheck_src_addr_o = (instr.opcode.aux_en & (instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? aux_src0_base_addr_o[0] :
                                     (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? aux_src0_base_addr_o[1] : '0;
  always_comb normcheck_enable_o = |normcheck_enable;

//State logic
always_comb begin : secpondary_ctrl_fsm_out_combo
    sign_ctrl_fsm_ns = sign_ctrl_fsm_ps;
    ntt_enable_o[1] = 0;
    skdecode_enable_o = 0;
    makehint_enable_o = 0;
    normcheck_enable[1] = 0;
    sigencode_enable_o = 0;

    unique case (sign_ctrl_fsm_ps)
      MLDSA_CTRL_IDLE: begin
        //Start function
        if (sign_instr.opcode.sampler_en)
          sign_ctrl_fsm_ns = MLDSA_CTRL_ERROR;
        if (sign_instr.opcode.ntt_en | sign_instr.opcode.aux_en)
          sign_ctrl_fsm_ns = MLDSA_CTRL_FUNC_START;
      end
      MLDSA_CTRL_FUNC_START: begin
        sign_ctrl_fsm_ns = MLDSA_CTRL_DONE;
        ntt_enable_o[1] = sign_instr.opcode.ntt_en;
        if (sign_instr.opcode.aux_en) begin
          skdecode_enable_o = (sign_instr.opcode.mode.aux_mode == MLDSA_SKDECODE);
          makehint_enable_o = (sign_instr.opcode.mode.aux_mode == MLDSA_MAKEHINT);
          normcheck_enable[1] = (sign_instr.opcode.mode.aux_mode == MLDSA_NORMCHK);
          sigencode_enable_o = (sign_instr.opcode.mode.aux_mode == MLDSA_SIGENC);
        end
      end
      MLDSA_CTRL_DONE: begin
        if ((sign_instr.opcode.ntt_en & ~ntt_busy_i[1]) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_SKDECODE) & skdecode_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_MAKEHINT) & makehint_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_NORMCHK) & normcheck_done_i) |
            (sign_instr.opcode.aux_en & (sign_instr.opcode.mode.aux_mode == MLDSA_SIGENC) & sigencode_done_i) ) begin
          sign_ctrl_fsm_ns = MLDSA_CTRL_IDLE;
        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : secondary_ctrl_fsm_flops
  if (!rst_b) begin
      sign_ctrl_fsm_ps <= MLDSA_CTRL_IDLE;
  end
  else if (zeroize) begin
      sign_ctrl_fsm_ps <= MLDSA_CTRL_IDLE;
  end
  else begin
      sign_ctrl_fsm_ps <= sign_ctrl_fsm_ns;
  end
end  

mldsa_seq_sec mldsa_seq_sec_inst
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
  `ABR_ASSERT_KNOWN(ERR_REG_HWIF_X, {mldsa_reg_hwif_in_o}, clk, !rst_b)

endmodule
