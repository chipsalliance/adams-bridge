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

module abr_ctrl
  import abr_reg_pkg::*;
  import abr_sha3_pkg::*;
  import abr_sampler_pkg::*;
  import abr_ctrl_pkg::*;
  import abr_params_pkg::*;
  import ntt_defines_pkg::*;
  `ifdef CALIPTRA
  import kv_defines_pkg::*; 
  `endif
  #(
  )
  (
  input logic clk,
  input logic rst_b,
  output logic zeroize,

`ifdef RV_FPGA_SCA
  output logic NTT_trigger,
  output logic PWM_trigger,
  output logic PWA_trigger,
  output logic INTT_trigger,
`endif

  output abr_reg__in_t abr_reg_hwif_in_o,
  input  abr_reg__out_t abr_reg_hwif_out_i,

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
  input logic [abr_sha3_pkg::StateW-1:0] sampler_state_data_i [Sha3Share],

  output logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr_o,

  //ntt interfaces
  output logic [ABR_NUM_NTT-1:0]            ntt_enable_o,
  output mldsa_ntt_mode_e [ABR_NUM_NTT-1:0] ntt_mode_o,
  output ntt_mem_addr_t [ABR_NUM_NTT-1:0]   ntt_mem_base_addr_o,
  output pwo_mem_addr_t [ABR_NUM_NTT-1:0]   pwo_mem_base_addr_o,
  output logic [ABR_NUM_NTT-1:0]            ntt_masking_en_o,
  output logic [ABR_NUM_NTT-1:0]            ntt_shuffling_en_o,
  input logic [ABR_NUM_NTT-1:0]             ntt_busy_i,

  //aux interfaces
  output logic [1:0][ABR_MEM_ADDR_WIDTH-1:0] aux_src0_base_addr_o,
  output logic [1:0][ABR_MEM_ADDR_WIDTH-1:0] aux_src1_base_addr_o,
  output logic [1:0][ABR_MEM_ADDR_WIDTH-1:0] aux_dest_base_addr_o,

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
  input logic skdecode_error_i,

  output logic makehint_enable_o,
  input logic makehint_invalid_i,
  input logic makehint_done_i,
  input logic makehint_reg_wren_i,
  input logic [3:0][7:0] makehint_reg_wrdata_i,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] makehint_reg_wr_addr_i,

  output logic normcheck_enable_o,
  output logic [1:0] normcheck_mode_o,
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

  //Memory interface export
  abr_sram_if.req sk_bank0_mem_if,
  abr_sram_if.req sk_bank1_mem_if,
  abr_sram_be_if.req sig_z_mem_if,
  abr_sram_be_if.req pk_mem_if,

  output mem_if_t zeroize_mem_o,

  `ifdef CALIPTRA
  // KV interface
  output kv_read_t kv_read,
  input kv_rd_resp_t kv_rd_resp,
  //PCR Signing
  input pcr_signing_t pcr_signing_data,
  `endif

  input logic debugUnlock_or_scan_mode_switch,
  output logic busy_o,

  //Interrupts
  output logic error_intr,
  output logic notif_intr

  );

  abr_reg__in_t abr_reg_hwif_in;
  abr_reg__out_t abr_reg_hwif_out;
  logic mldsa_ready;
  logic mldsa_valid_reg;
  logic mldsa_privkey_lock;
  logic kv_seed_data_present;

  logic external_mu;
  logic external_mu_mode, external_mu_mode_nxt;

  `ifdef CALIPTRA
//Custom keyvault logic for Caliptra

  logic kv_seed_write_en;
  logic [$clog2(SEED_NUM_DWORDS)-1:0] kv_seed_write_offset;
  logic [DATA_WIDTH-1:0] kv_seed_write_data;
  kv_read_ctrl_reg_t kv_seed_read_ctrl_reg;
  kv_error_code_e kv_seed_error;
  logic kv_seed_ready, kv_seed_done;
  //KV Seed Data Present
  logic kv_seed_data_present_set, kv_seed_data_present_reset;
  logic pcr_sign_mode;
  logic pcr_sign_input_invalid;

  always_comb begin: mldsa_kv_ctrl_reg
    //ready when fsm is not busy
    abr_reg_hwif_in.mldsa_kv_rd_seed_status.ERROR.next = kv_seed_error;
    //ready when fsm is not busy
    abr_reg_hwif_in.mldsa_kv_rd_seed_status.READY.next = kv_seed_ready;
    //set valid when fsm is done
    abr_reg_hwif_in.mldsa_kv_rd_seed_status.VALID.hwset = kv_seed_done;
    //clear valid when new request is made
    abr_reg_hwif_in.mldsa_kv_rd_seed_status.VALID.hwclr = kv_seed_read_ctrl_reg.read_en;
    //clear enable when busy
    abr_reg_hwif_in.mldsa_kv_rd_seed_ctrl.read_en.hwclr = ~kv_seed_ready;
  end

  `CALIPTRA_KV_READ_CTRL_REG2STRUCT(kv_seed_read_ctrl_reg, mldsa_kv_rd_seed_ctrl, abr_reg_hwif_out)

  //Detect keyvault data coming in to lock api registers and protect outputs
  always_comb kv_seed_data_present_set = kv_seed_read_ctrl_reg.read_en | pcr_sign_mode;
  always_comb kv_seed_data_present_reset = kv_seed_data_present & mldsa_valid_reg;

  //Read SEED
  kv_read_client #(
    .DATA_WIDTH(SEED_NUM_DWORDS*32),
    .PAD(0)
  )
  mldsa_seed_kv_read
  (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),

    //client control register
    .read_ctrl_reg(kv_seed_read_ctrl_reg),

    //interface with kv
    .kv_read(kv_read),
    .kv_resp(kv_rd_resp),

    //interface with client
    .write_en(kv_seed_write_en),
    .write_offset(kv_seed_write_offset),
    .write_data(kv_seed_write_data),

    .error_code(kv_seed_error),
    .kv_ready(kv_seed_ready),
    .read_done(kv_seed_done)
);

always_ff @(posedge clk or negedge rst_b) begin : mldsa_kv_reg
  if (!rst_b)
    kv_seed_data_present <= '0;
  else if (zeroize)
    kv_seed_data_present <= '0;
  else begin
    kv_seed_data_present <= kv_seed_data_present_set ? '1 :
                            kv_seed_data_present_reset ? '0 : kv_seed_data_present;
  end
end

always_comb pcr_sign_mode = abr_reg_hwif_out.MLDSA_CTRL.PCR_SIGN.value;

`else
always_comb begin: mldsa_kv_ctrl_reg
  //ready when fsm is not busy
  abr_reg_hwif_in.mldsa_kv_rd_seed_status.ERROR.next = '0;
  //ready when fsm is not busy
  abr_reg_hwif_in.mldsa_kv_rd_seed_status.READY.next = '0;
  //set valid when fsm is done
  abr_reg_hwif_in.mldsa_kv_rd_seed_status.VALID.hwset = '0;
  //clear valid when new request is made
  abr_reg_hwif_in.mldsa_kv_rd_seed_status.VALID.hwclr = '0;
  //clear enable when busy
  abr_reg_hwif_in.mldsa_kv_rd_seed_ctrl.read_en.hwclr = '0;
end

always_comb kv_seed_data_present = '0;
`endif

  logic [2:0] cmd_reg;

  logic keygen_process, keygen_process_nxt;
  logic signing_process, signing_process_nxt;
  logic verifying_process, verifying_process_nxt;
  logic keygen_signing_process, keygen_signing_process_nxt;
  logic keygen_done;
  logic signature_done;
  logic verify_done;
  logic process_done;

  //assign appropriate data to msg interface
  logic [ABR_OPR_WIDTH-1:0]  sampler_src;
  logic [15:0]               sampler_src_offset;
  logic [2:0]                sampler_src_offset_f;
  logic [15:0]               sampler_imm;
  
  logic [ENTROPY_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] entropy_reg;
  logic [SEED_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] seed_reg;
  logic [MLDSA_MSG_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] msg_reg;
  logic internal_mu_we;
  logic [MU_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] internal_mu_reg;
  logic [MU_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] external_mu_reg;
  logic [SIGN_RND_NUM_DWORDS-1 : 0][DATA_WIDTH-1:0] sign_rnd_reg;
  logic [7:0][63:0] rho_p_reg;
  logic [3:0][63:0] rho_reg;
  logic [7:0][63:0] mu_reg;
  logic [15:0] kappa_reg;
  logic update_kappa;

  logic [MsgWidth-1:0] msg_data;
  logic stream_msg_mode;
  logic stream_msg_rdy;
  logic stream_msg_valid;
  logic [3:0] stream_msg_strobe;
  logic stream_msg_last;
  logic stream_msg_done;
  logic stream_msg_ip;

  logic [31:0] stream_msg_data;
  logic [63:0] stream_msg_buffer_data;
  logic        stream_msg_buffer_valid;
  logic [7:0]  stream_msg_buffer_strobe;
  logic        stream_msg_buffer_flush;

  logic [CTX_NUM_DWORDS-1:0][DATA_WIDTH-1:0] ctx_reg;
  logic [CTX_SIZE_W-1:0] ctx_size;
  logic [CTX_SIZE_W-$clog2(STREAM_MSG_STROBE_W)-1:0] ctx_cnt_required;
  logic [$clog2(STREAM_MSG_STROBE_W)-1:0] ctx_cnt_offset;

  mldsa_stream_msg_fsm_state_e stream_msg_fsm_ps, stream_msg_fsm_ns;
  logic [CTX_SIZE_W-$clog2(STREAM_MSG_STROBE_W)-1:0] ctx_cnt,ctx_cnt_nxt;

  logic prim_seq_en;
  logic [ABR_PROG_ADDR_W-1 : 0] prim_prog_cntr, prim_prog_cntr_nxt;
  abr_seq_instr_t prim_instr_o, prim_instr;

  logic msg_done;
  logic msg_last;
  logic [MsgStrbW-1:0] msg_strobe_nxt, last_msg_strobe;
  logic [ABR_OPR_WIDTH-1:$clog2(MsgStrbW)] msg_cnt_nxt, msg_cnt;
  logic msg_valid_nxt;
  logic msg_hold;

  logic error_flag;
  logic error_flag_reg;
  logic error_flag_edge;
  logic subcomponent_busy;

  abr_ctrl_fsm_state_e prim_ctrl_fsm_ps, prim_ctrl_fsm_ns;
  logic msg_valid;

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
  
  //per controller enable/busy for ntt
  logic [1:0] ntt_en; //This is the pulse we drive to NTT to start it
  logic [1:0] ntt_active; //This is the mux select for 1 NTT mode
  logic [1:0] ntt_busy;

  logic [ABR_NUM_NTT-1:0][ABR_MEM_ADDR_WIDTH-1:0] ntt_temp_address;

  //Interrupts
  logic mldsa_status_done_d, mldsa_status_done_p;

  logic set_entropy;
  logic [7:0][63:0] lfsr_entropy_reg;
  logic [MsgWidth-1:0] counter_reg;

  logic zeroize_mem_we;
  logic [ABR_MEM_ADDR_WIDTH-1:0] zeroize_mem_addr;
  logic zeroize_mem_done;
  
  assign abr_reg_hwif_in_o = abr_reg_hwif_in;
  assign abr_reg_hwif_out = abr_reg_hwif_out_i;

  always_comb mldsa_ready = (prim_prog_cntr == MLDSA_RESET);

  //without zeroize to make it more complex
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
      counter_reg <= '0;
    else
      counter_reg <= counter_reg + 1;
  end

  //Set busy when engine is in progress
  always_comb busy_o = ~mldsa_ready;

//HWIF to reg block
  always_comb abr_reg_hwif_in.reset_b = rst_b;
  always_comb abr_reg_hwif_in.hard_reset_b = rst_b; //FIXME interface needs a hard reset signal?
  always_comb abr_reg_hwif_in.abr_ready = mldsa_ready; //FIXME add mlkem
  always_comb cmd_reg = abr_reg_hwif_out.MLDSA_CTRL.CTRL.value;
  always_comb abr_reg_hwif_in.MLDSA_CTRL.CTRL.hwclr = |cmd_reg;
  `ifdef CALIPTRA
    always_comb abr_reg_hwif_in.MLDSA_CTRL.PCR_SIGN.hwclr = abr_reg_hwif_out.MLDSA_CTRL.PCR_SIGN.value;
  `else
    always_comb abr_reg_hwif_in.MLDSA_CTRL.PCR_SIGN.hwclr = '0;
  `endif

  always_comb abr_reg_hwif_in.MLDSA_NAME[0].NAME.next = '0;
  always_comb abr_reg_hwif_in.MLDSA_NAME[1].NAME.next = '0;
  always_comb abr_reg_hwif_in.MLDSA_VERSION[0].VERSION.next = '0;
  always_comb abr_reg_hwif_in.MLDSA_VERSION[1].VERSION.next = '0;
  
  always_comb abr_reg_hwif_in.MLDSA_STATUS.READY.next = mldsa_ready;
  always_comb abr_reg_hwif_in.MLDSA_STATUS.VALID.next = mldsa_valid_reg;
  always_comb abr_reg_hwif_in.MLDSA_STATUS.MSG_STREAM_READY.next = stream_msg_rdy;

  always_comb zeroize = abr_reg_hwif_out.MLDSA_CTRL.ZEROIZE.value || debugUnlock_or_scan_mode_switch;
  
  always_comb external_mu = 0; //abr_reg_hwif_out.MLDSA_CTRL.EXTERNAL_MU.value; //TODO: enable after ExternalMu validation
  always_comb abr_reg_hwif_in.MLDSA_CTRL.EXTERNAL_MU.hwclr = abr_reg_hwif_out.MLDSA_CTRL.EXTERNAL_MU.value;
  
  always_comb stream_msg_mode = abr_reg_hwif_out.MLDSA_CTRL.STREAM_MSG.value;
  always_comb abr_reg_hwif_in.MLDSA_CTRL.STREAM_MSG.hwclr = zeroize;

  always_comb abr_reg_hwif_in.MLDSA_CTX_CONFIG.CTX_SIZE.hwclr = zeroize;

  always_comb abr_reg_hwif_in.MLDSA_MSG_STROBE.STROBE.swwe = stream_msg_rdy;
  always_comb abr_reg_hwif_in.MLDSA_MSG_STROBE.STROBE.hwclr = zeroize;

  always_comb begin // mldsa reg writing 

    for (int dword=0; dword < ENTROPY_NUM_DWORDS; dword++) begin
      entropy_reg[dword] = abr_reg_hwif_out.ABR_ENTROPY[dword].ENTROPY.value;
      abr_reg_hwif_in.ABR_ENTROPY[dword].ENTROPY.hwclr = zeroize;
    end

    for (int dword=0; dword < SEED_NUM_DWORDS; dword++) begin
      seed_reg[dword] = abr_reg_hwif_out.MLDSA_SEED[dword].SEED.value;

      `ifdef CALIPTRA
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.we = (pcr_sign_mode | (kv_seed_write_en & (kv_seed_write_offset == SEED_NUM_DWORDS-1-dword))) & ~zeroize;
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.next = pcr_sign_mode   ? pcr_signing_data.pcr_mldsa_signing_seed[SEED_NUM_DWORDS-1-dword] : 
                                                      kv_seed_write_data;
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.hwclr = zeroize | kv_seed_data_present_reset | (kv_seed_error == KV_READ_FAIL);
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.swwe = mldsa_ready & ~kv_seed_data_present;
      `else
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.we = '0;
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.next = '0;
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.hwclr = zeroize;
      abr_reg_hwif_in.MLDSA_SEED[dword].SEED.swwe = mldsa_ready;
      `endif
    end
  
    for (int dword=0; dword < MLDSA_MSG_NUM_DWORDS; dword++) begin
      msg_reg[dword] = external_mu_mode? '0 : abr_reg_hwif_out.MLDSA_MSG[dword].MSG.value;
      `ifdef CALIPTRA
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.we = pcr_sign_mode & !external_mu & !zeroize;
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.next = pcr_signing_data.pcr_hash[MLDSA_MSG_NUM_DWORDS-1-dword];
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.hwclr = zeroize;
      `else
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.we = '0;
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.next = '0;
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.hwclr = zeroize;
      `endif
      abr_reg_hwif_in.MLDSA_MSG[dword].MSG.swwe = mldsa_ready | stream_msg_rdy;
    end

    for (int dword=0; dword < MU_NUM_DWORDS; dword++) begin
      external_mu_reg[dword] = abr_reg_hwif_out.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.value;
      abr_reg_hwif_in.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.we = internal_mu_we & !external_mu & !zeroize;
      abr_reg_hwif_in.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.next = internal_mu_reg[dword];
      abr_reg_hwif_in.MLDSA_EXTERNAL_MU[dword].EXTERNAL_MU.hwclr = zeroize;
    end
  
    for (int dword=0; dword < SIGN_RND_NUM_DWORDS; dword++) begin
      sign_rnd_reg[dword] = abr_reg_hwif_out.MLDSA_SIGN_RND[dword].SIGN_RND.value;
      abr_reg_hwif_in.MLDSA_SIGN_RND[dword].SIGN_RND.hwclr = zeroize;
    end
  
    for (int dword=0; dword < VERIFY_RES_NUM_DWORDS; dword++) begin 
      abr_reg_hwif_in.MLDSA_VERIFY_RES[dword].VERIFY_RES.we = verify_valid & sampler_state_dv_i & (prim_instr.operand3 == MLDSA_DEST_VERIFY_RES_REG_ID);       
      abr_reg_hwif_in.MLDSA_VERIFY_RES[dword].VERIFY_RES.next = sampler_state_data_i[0][dword*32 +: 32];
      abr_reg_hwif_in.MLDSA_VERIFY_RES[dword].VERIFY_RES.hwclr = zeroize | clear_verify_valid;
    end
  
    for (int dword = 0; dword < CTX_NUM_DWORDS; dword++) begin
      ctx_reg[dword] = abr_reg_hwif_out.MLDSA_CTX[dword].CTX.value;
      abr_reg_hwif_in.MLDSA_CTX[dword].CTX.hwclr = zeroize;
    end

    ctx_size = abr_reg_hwif_out.MLDSA_CTX_CONFIG.CTX_SIZE.value;

  end

  //Generate a pulse to trig the interrupt after finishing the operation
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
      mldsa_status_done_d <= 1'b0;
    else if (zeroize)
      mldsa_status_done_d <= 1'b0;
    else
      mldsa_status_done_d <= abr_reg_hwif_in.MLDSA_STATUS.VALID.next;
  end

  always_comb mldsa_status_done_p = abr_reg_hwif_in.MLDSA_STATUS.VALID.next & !mldsa_status_done_d;

  assign error_intr = abr_reg_hwif_out.intr_block_rf.error_global_intr_r.intr;
  assign notif_intr = abr_reg_hwif_out.intr_block_rf.notif_global_intr_r.intr;

  always_comb begin
    abr_reg_hwif_in.intr_block_rf.error_internal_intr_r.error_internal_sts.hwset = error_flag_edge; //TODO
    abr_reg_hwif_in.intr_block_rf.notif_internal_intr_r.notif_cmd_done_sts.hwset = mldsa_status_done_p;
  end

  //Private Key External Memory

  //Request muxing
  logic [1:0] sk_ram_we_bank, sk_ram_re_bank;
  logic [1:0][SK_MEM_BANK_ADDR_W-1:0] sk_ram_waddr_bank, sk_ram_raddr_bank;
  logic [1:0][DATA_WIDTH-1:0] sk_ram_wdata, sk_ram_rdata;

  logic [1:0] skencode_keymem_we_bank, pwr2rnd_keymem_we_bank, api_keymem_we_bank;
  logic [SK_MEM_BANK_ADDR_W:0] api_sk_waddr, api_sk_raddr;
  logic [SK_MEM_BANK_ADDR_W:0] api_sk_mem_waddr, api_sk_mem_raddr;
  logic [4:0] api_sk_reg_waddr, api_sk_reg_raddr;

  logic [1:0] api_keymem_re_bank, api_keymem_re_bank_f;
  logic [1:0] skdecode_re_bank;
  logic [1:0][SK_MEM_BANK_ADDR_W:0] skdecode_rdaddr;

  logic api_keymem_wr_dec, api_sk_reg_wr_dec;
  logic api_keymem_rd_dec, api_sk_reg_rd_dec, api_sk_reg_rd_dec_f;
  logic api_keymem_rd_vld;
  logic [DATA_WIDTH-1:0] privkey_reg_rdata;
  logic [DATA_WIDTH-1:0] privkey_out_rdata;

  always_ff @(posedge clk or negedge rst_b) begin : mldsa_privkey_lock_reg
    if (!rst_b)
      mldsa_privkey_lock <= '1;
    else if (zeroize)
      mldsa_privkey_lock <= '1;
    //Clear the lock only after completing standalone keygen where the seed did not come from the keyvault
    else if (~kv_seed_data_present & (keygen_process & keygen_done))
      mldsa_privkey_lock <= '0;
  end
  
  always_comb api_keymem_rd_vld = abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & ~abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr & 
                                  mldsa_valid_reg & ~mldsa_privkey_lock ;

  always_comb api_sk_waddr = abr_reg_hwif_out.MLDSA_PRIVKEY_IN.addr[12:2];
  always_comb api_sk_raddr = abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.addr[12:2];

  always_comb api_sk_reg_wr_dec = abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req & api_sk_waddr inside {[0:31]};
  always_comb api_keymem_wr_dec = abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req & api_sk_waddr inside {[31:PRIVKEY_NUM_DWORDS-1]};

  always_comb api_sk_reg_rd_dec = abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & api_sk_raddr inside {[0:31]};
  always_comb api_keymem_rd_dec = abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & api_sk_raddr inside {[32:PRIVKEY_NUM_DWORDS-1]};

  assign api_sk_reg_waddr = api_sk_waddr[4:0];
  assign api_sk_reg_raddr = api_sk_raddr[4:0];

  assign api_sk_mem_waddr = api_sk_waddr - 'd32;
  assign api_sk_mem_raddr = api_sk_raddr - 'd32;

  always_comb begin
    for (int i = 0; i < 2; i++) begin
      skencode_keymem_we_bank[i] = ((skencode_keymem_if_i.rd_wr_en == RW_WRITE) & (skencode_keymem_if_i.addr[0] == i));
      pwr2rnd_keymem_we_bank[i] = (pwr2rnd_keymem_if_i[i].rd_wr_en == RW_WRITE);
      api_keymem_we_bank[i] = abr_reg_hwif_in.MLDSA_PRIVKEY_IN.wr_ack & mldsa_ready & api_keymem_wr_dec & (api_sk_mem_waddr[0] == i);

      sk_ram_we_bank[i] = skencode_keymem_we_bank[i] | pwr2rnd_keymem_we_bank[i] | api_keymem_we_bank[i] | zeroize_mem_we;

      sk_ram_waddr_bank[i] = ({SK_MEM_BANK_ADDR_W{skencode_keymem_we_bank[i]}} & skencode_keymem_if_i.addr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{pwr2rnd_keymem_we_bank[i]}} & pwr2rnd_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:1] ) |
                             ({SK_MEM_BANK_ADDR_W{api_keymem_we_bank[i]}} & api_sk_mem_waddr[SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{zeroize_mem_we}} & zeroize_mem_addr[SK_MEM_BANK_ADDR_W-1:0]);
                 
      sk_ram_wdata[i] = ({DATA_WIDTH{skencode_keymem_we_bank[i]}} & skencode_wr_data_i) |
                        ({DATA_WIDTH{pwr2rnd_keymem_we_bank[i]}} & pwr2rnd_wr_data_i[i]) |
                        ({DATA_WIDTH{api_keymem_we_bank[i]}} & abr_reg_hwif_out.MLDSA_PRIVKEY_IN.wr_data);         
    end
  end     
  
  always_comb begin
    for (int i = 0; i < 2; i++) begin
      api_keymem_re_bank[i] = api_keymem_rd_vld & api_keymem_rd_dec & (api_sk_mem_raddr[0] == i);

      skdecode_re_bank[i] = (skdecode_keymem_if_i[i].rd_wr_en == RW_READ);

      skdecode_rdaddr[i] = skdecode_keymem_if_i[i].addr[SK_MEM_BANK_ADDR_W:0];

      sk_ram_re_bank[i] = skdecode_re_bank[i] | api_keymem_re_bank[i];

      sk_ram_raddr_bank[i] = ({SK_MEM_BANK_ADDR_W{skdecode_re_bank[i]}} & skdecode_rdaddr[i][SK_MEM_BANK_ADDR_W:1]) |
                             ({SK_MEM_BANK_ADDR_W{api_keymem_re_bank[i]}} & api_sk_mem_raddr[SK_MEM_BANK_ADDR_W:1]);

    end
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      api_keymem_re_bank_f <= '0;
      api_sk_reg_rd_dec_f <= '0;
    end else if (zeroize) begin
      api_keymem_re_bank_f <= '0;
      api_sk_reg_rd_dec_f <= '0;
    end else begin
      api_keymem_re_bank_f <= api_keymem_re_bank;
      api_sk_reg_rd_dec_f <= api_sk_reg_rd_dec;
    end
  end

  always_comb skdecode_rd_data_o = sk_ram_rdata;
  always_comb privkey_out_rdata = {DATA_WIDTH{api_keymem_re_bank_f[0]}} & sk_ram_rdata[0] |
                                  {DATA_WIDTH{api_keymem_re_bank_f[1]}} & sk_ram_rdata[1] |
                                  {DATA_WIDTH{api_sk_reg_rd_dec_f}} & privkey_reg_rdata;

  always_comb sk_bank0_mem_if.we_i = (sk_ram_we_bank[0]);
  always_comb sk_bank0_mem_if.waddr_i = (sk_ram_waddr_bank[0]);
  always_comb sk_bank0_mem_if.wdata_i = (sk_ram_wdata[0]);
  always_comb sk_bank0_mem_if.re_i = (sk_ram_re_bank[0]);
  always_comb sk_bank0_mem_if.raddr_i = (sk_ram_raddr_bank[0]);
  always_comb sk_ram_rdata[0] = sk_bank0_mem_if.rdata_o;

  always_comb sk_bank1_mem_if.we_i = (sk_ram_we_bank[1]);
  always_comb sk_bank1_mem_if.waddr_i = (sk_ram_waddr_bank[1]);
  always_comb sk_bank1_mem_if.wdata_i = (sk_ram_wdata[1]);
  always_comb sk_bank1_mem_if.re_i = (sk_ram_re_bank[1]);
  always_comb sk_bank1_mem_if.raddr_i = (sk_ram_raddr_bank[1]);
  always_comb sk_ram_rdata[1] = sk_bank1_mem_if.rdata_o;

  //Private Key External Memory
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      privatekey_reg <= '0;
    end else if (zeroize) begin
      privatekey_reg <= '0;
    end else begin
      if (sampler_state_dv_i) begin
        if (prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
          //HW write rho
          privatekey_reg.enc.rho <= sampler_state_data_i[0][255:0]; //FIXME optimize this to be shared with pubkey?
          //HW write K
          privatekey_reg.enc.K <= sampler_state_data_i[0][1023:768];
        end else if (prim_instr.operand3 == MLDSA_DEST_TR_REG_ID) begin
          //HW write tr
          privatekey_reg.enc.tr <= sampler_state_data_i[0][511:0];
        end
      end else if (abr_reg_hwif_in.MLDSA_PRIVKEY_IN.wr_ack & mldsa_ready & api_sk_reg_wr_dec) begin
        //SW write port
        privatekey_reg.raw[api_sk_reg_waddr] <= abr_reg_hwif_out.MLDSA_PRIVKEY_IN.wr_data;
      end
    end 
  end

  //private key read ports
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      privkey_reg_rdata <= '0;
    end else if (zeroize) begin
      privkey_reg_rdata <= '0;
    end else begin
      if (api_keymem_rd_vld & api_sk_reg_rd_dec) begin
        privkey_reg_rdata <= privatekey_reg.raw[api_sk_reg_raddr];
      end
    end
  end

  assign abr_reg_hwif_in.MLDSA_PRIVKEY_IN.wr_ack = abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req & abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req_is_wr;
  //no reads to PRIVKEY_IN allowed - just ack it
  assign abr_reg_hwif_in.MLDSA_PRIVKEY_IN.rd_ack = abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req & ~abr_reg_hwif_out.MLDSA_PRIVKEY_IN.req_is_wr;
  assign abr_reg_hwif_in.MLDSA_PRIVKEY_IN.rd_data = '0;


  logic privkey_out_rd_ack, signature_rd_ack, pubkey_rd_ack;

  always_comb  abr_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_ack = privkey_out_rd_ack;
  always_comb  abr_reg_hwif_in.MLDSA_SIGNATURE.rd_ack = signature_rd_ack;
  always_comb  abr_reg_hwif_in.MLDSA_PUBKEY.rd_ack = pubkey_rd_ack;

  //ack the read request one clock later
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      privkey_out_rd_ack <= 0;
      signature_rd_ack <= 0;
      pubkey_rd_ack <= 0;
    end
    else if (zeroize) begin
      privkey_out_rd_ack <= 0;
      signature_rd_ack <= 0;
      pubkey_rd_ack <= 0;
    end
    else begin
      privkey_out_rd_ack <= abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & ~abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr;
      signature_rd_ack <= abr_reg_hwif_out.MLDSA_SIGNATURE.req & ~abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr;
      pubkey_rd_ack <= abr_reg_hwif_out.MLDSA_PUBKEY.req & ~abr_reg_hwif_out.MLDSA_PUBKEY.req_is_wr;
    end
  end

  always_comb abr_reg_hwif_in.MLDSA_PRIVKEY_OUT.rd_data = privkey_out_rd_ack & mldsa_valid_reg & ~mldsa_privkey_lock ? privkey_out_rdata : 0;

  //No write to PRIVKEY_OUT allowed - just ack it
  assign abr_reg_hwif_in.MLDSA_PRIVKEY_OUT.wr_ack = abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req & abr_reg_hwif_out.MLDSA_PRIVKEY_OUT.req_is_wr;

  //Signature external mem
  logic sig_z_ram_we, sig_z_ram_re;
  logic [SIG_Z_MEM_ADDR_W-1:0] sig_z_ram_waddr, sig_z_ram_raddr;
  logic [SIG_Z_MEM_NUM_DWORD-1:0][31:0] sig_z_ram_wdata, sig_z_ram_rdata;
  logic [SIG_Z_MEM_WSTROBE_W-1:0] sig_z_ram_wstrobe;
  logic api_sig_z_dec, api_sig_h_dec, api_sig_c_dec;
  logic api_sig_z_re, api_sig_z_re_f, api_sig_z_we;
  logic [SIG_ADDR_W-1:0] api_sig_addr;
  mldsa_signature_z_addr_t api_sig_z_addr;
  mldsa_signature_z_addr_t api_sig_z_addr_f;
  logic [SIG_C_REG_ADDR_W-1:0] api_sig_c_addr;
  logic [SIG_H_REG_ADDR_W-1:0] api_sig_h_addr;
  logic [DATA_WIDTH-1:0] signature_reg_rdata;


  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      api_sig_z_re_f <= '0;
      api_sig_z_addr_f <= '0;
    end else if (zeroize) begin
      api_sig_z_re_f <= '0;
      api_sig_z_addr_f <= '0;
    end else begin
      api_sig_z_re_f <= api_sig_z_re;
      api_sig_z_addr_f <= api_sig_z_addr;
    end
  end

  always_comb api_sig_addr = abr_reg_hwif_out.MLDSA_SIGNATURE.addr[SIG_ADDR_W+1:2];

  always_comb api_sig_c_dec = abr_reg_hwif_out.MLDSA_SIGNATURE.req & api_sig_addr inside {[0:SIGNATURE_C_NUM_DWORDS-1]};
  always_comb api_sig_z_dec = abr_reg_hwif_out.MLDSA_SIGNATURE.req & api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS:SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS-1]};
  always_comb api_sig_h_dec = abr_reg_hwif_out.MLDSA_SIGNATURE.req & api_sig_addr inside {[SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS:SIGNATURE_NUM_DWORDS-1]};

  always_comb api_sig_z_addr.addr   = SIG_Z_MEM_ADDR_W'( (api_sig_addr - SIGNATURE_C_NUM_DWORDS)/SIG_Z_MEM_NUM_DWORD );
  always_comb api_sig_z_addr.offset = (api_sig_addr - SIGNATURE_C_NUM_DWORDS)%SIG_Z_MEM_NUM_DWORD; //FIXME can this be done better?
  always_comb api_sig_c_addr = api_sig_addr[SIG_C_REG_ADDR_W-1:0];
  always_comb api_sig_h_addr = SIG_H_REG_ADDR_W'( api_sig_addr - (SIGNATURE_C_NUM_DWORDS+SIGNATURE_Z_NUM_DWORDS) );

  always_comb abr_reg_hwif_in.MLDSA_SIGNATURE.wr_ack = abr_reg_hwif_out.MLDSA_SIGNATURE.req &  abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr;
  always_comb api_sig_z_we = mldsa_ready & api_sig_z_dec & abr_reg_hwif_in.MLDSA_SIGNATURE.wr_ack;

  always_comb api_sig_z_re = mldsa_valid_reg & api_sig_z_dec & ~abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr;

  always_comb sig_z_mem_if.we_i = (sig_z_ram_we);
  always_comb sig_z_mem_if.waddr_i = (sig_z_ram_waddr);
  always_comb sig_z_mem_if.wstrobe_i = (sig_z_ram_wstrobe);
  always_comb sig_z_mem_if.wdata_i = (sig_z_ram_wdata);
  always_comb sig_z_mem_if.re_i = (sig_z_ram_re);
  always_comb sig_z_mem_if.raddr_i = (sig_z_ram_raddr);
  always_comb sig_z_ram_rdata = sig_z_mem_if.rdata_o;

  //read requests
  always_comb sig_z_ram_re = (sigdecode_z_rd_req_i.rd_wr_en == RW_READ) | api_sig_z_re;
  always_comb sig_z_ram_raddr = ({SIG_Z_MEM_ADDR_W{(sigdecode_z_rd_req_i.rd_wr_en == RW_READ)}} & sigdecode_z_rd_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{api_sig_z_re}} & api_sig_z_addr.addr);

  always_comb sigdecode_z_rd_data_o = sig_z_ram_rdata;
  always_comb abr_reg_hwif_in.MLDSA_SIGNATURE.rd_data = api_sig_z_re_f ? sig_z_ram_rdata[api_sig_z_addr_f.offset] : signature_reg_rdata;

  //write requests
  always_comb sig_z_ram_we = (sigencode_wr_req_i.rd_wr_en == RW_WRITE) | api_sig_z_we | zeroize_mem_we;
  always_comb sig_z_ram_waddr = ({SIG_Z_MEM_ADDR_W{(sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & sigencode_wr_req_i.addr[SIG_Z_MEM_ADDR_W:1]) |
                                ({SIG_Z_MEM_ADDR_W{api_sig_z_we}} & api_sig_z_addr.addr) |
                                ({SIG_Z_MEM_ADDR_W{zeroize_mem_we}} & zeroize_mem_addr[SIG_Z_MEM_ADDR_W-1:0]);

  always_comb sig_z_ram_wstrobe = ({SIG_Z_MEM_WSTROBE_W{(sigencode_wr_req_i.rd_wr_en == RW_WRITE)}}) |
                                  ({SIG_Z_MEM_WSTROBE_W{api_sig_z_we}} & ('hF << api_sig_z_addr.offset*4)) |
                                  ({SIG_Z_MEM_WSTROBE_W{zeroize_mem_we}});


  always_comb sig_z_ram_wdata = ({SIG_Z_MEM_DATA_W{(sigencode_wr_req_i.rd_wr_en == RW_WRITE)}} & sigencode_wr_data_i) |
                                ({SIG_Z_MEM_DATA_W{(api_sig_z_we)}} & SIG_Z_MEM_DATA_W'(abr_reg_hwif_out.MLDSA_SIGNATURE.wr_data << api_sig_z_addr.offset*32));

  //signature reg read flop
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      signature_reg_rdata <= '0;
    end else if (zeroize) begin
      signature_reg_rdata <= '0;
    end else begin
      if (mldsa_valid_reg & abr_reg_hwif_out.MLDSA_SIGNATURE.req & ~abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr)
        signature_reg_rdata <= {DATA_WIDTH{api_sig_c_dec}} & signature_reg.enc.c[api_sig_c_addr] |
                               {DATA_WIDTH{api_sig_h_dec}} & signature_reg.enc.h[api_sig_h_addr];
    end
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      signature_reg <= '0;
    end else if (zeroize) begin
      signature_reg <= '0;
    end else begin
      //HW write c
      if (sampler_state_dv_i & (prim_instr.operand3 == MLDSA_DEST_SIG_C_REG_ID)) begin
        signature_reg.enc.c <= sampler_state_data_i[0][511:0];
      end else if (mldsa_ready & api_sig_c_dec & abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr) begin
        for (int dword = 0; dword < SIGNATURE_NUM_DWORDS; dword++) begin
          signature_reg.enc.c[api_sig_c_addr] <= abr_reg_hwif_out.MLDSA_SIGNATURE.wr_data;
        end
      end
      //HW write h
      if (set_signature_valid) begin
        signature_reg.enc.h <= '0;
      end else if (makehint_reg_wren_i) begin
        for (int dword = 0; dword < SIGNATURE_H_NUM_DWORDS; dword++) begin
          if (makehint_reg_wr_addr_i == dword)
            signature_reg.enc.h[dword] <= signature_reg.enc.h[dword] | makehint_reg_wrdata_i;
        end
      end else if (mldsa_ready & api_sig_h_dec & abr_reg_hwif_out.MLDSA_SIGNATURE.req_is_wr) begin
        signature_reg.enc.h[api_sig_h_addr] <= abr_reg_hwif_out.MLDSA_SIGNATURE.wr_data;
      end
    end
  end

  always_comb begin
    //HW read h
    for (int i = 0; i < SIGNATURE_H_VALID_NUM_BYTES; i++) begin
      signature_h_o[i] = signature_reg.enc.h[i/4][(i%4)*8 +: 8];
    end
  end


//public key memory
  logic pubkey_ram_we, pubkey_ram_re;
  logic [PK_MEM_ADDR_W-1:0] pubkey_ram_waddr, pubkey_ram_raddr;
  logic [PK_MEM_NUM_DWORDS-1:0][31:0] pubkey_ram_wdata, pubkey_ram_rdata;
  logic [31:0][T1_COEFF_W-1:0] pubkey_ram_rdata_t1;
  logic [PK_MEM_WSTROBE_W-1:0] pubkey_ram_wstrobe;
  logic api_pubkey_dec, api_pubkey_rho_dec;
  logic api_pubkey_re, api_pubkey_re_f, api_pubkey_we;
  logic [PK_ADDR_W-1:0] api_pubkey_addr;
  mldsa_pubkey_mem_addr_t api_pubkey_mem_addr;
  mldsa_pubkey_mem_addr_t api_pubkey_mem_addr_f;
  mldsa_pubkey_mem_addr_t sampler_pubkey_mem_addr;
  logic [PK_RHO_REG_ADDR_W-1:0] api_pk_rho_addr;
  logic [DATA_WIDTH-1:0] pk_reg_rdata;
  logic sampler_pk_rd_en, sampler_pk_rd_en_f, pkdecode_rd_en;
  logic [1:0] pkdecode_rd_offset_f;

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      api_pubkey_re_f <= '0;
      api_pubkey_mem_addr_f <= '0;
      sampler_pk_rd_en_f <= '0;
      sampler_src_offset_f <= '0;
      pkdecode_rd_offset_f <= '0;
    end else if (zeroize) begin
      api_pubkey_re_f <= '0;
      api_pubkey_mem_addr_f <= '0;
      sampler_pk_rd_en_f <= '0;
      sampler_src_offset_f <= '0;
      pkdecode_rd_offset_f <= '0;
    end else begin
      api_pubkey_re_f <= api_pubkey_re;
      api_pubkey_mem_addr_f <= api_pubkey_mem_addr;
      sampler_pk_rd_en_f <= msg_hold ? sampler_pk_rd_en_f : sampler_pk_rd_en;
      sampler_src_offset_f <= msg_hold ? sampler_src_offset_f : sampler_pubkey_mem_addr.offset[2:0];
      pkdecode_rd_offset_f <= pkdecode_rd_addr_i[1:0];
    end
  end

  always_comb api_pubkey_addr = abr_reg_hwif_out.MLDSA_PUBKEY.addr[PK_ADDR_W+1:2];

  always_comb api_pubkey_rho_dec = abr_reg_hwif_out.MLDSA_PUBKEY.req & api_pubkey_addr inside {[0:7]};
  always_comb api_pubkey_dec = abr_reg_hwif_out.MLDSA_PUBKEY.req & api_pubkey_addr inside {[8:PUBKEY_NUM_DWORDS-1]};

  always_comb api_pubkey_mem_addr.addr   = PK_MEM_ADDR_W'( (api_pubkey_addr - 8)/PK_MEM_NUM_DWORDS );
  always_comb api_pubkey_mem_addr.offset = (api_pubkey_addr - 8)%PK_MEM_NUM_DWORDS; //FIXME can this be done better?

  always_comb sampler_pubkey_mem_addr.addr = PK_MEM_ADDR_W'((sampler_src_offset- 4)/(PK_MEM_NUM_DWORDS/2));
  always_comb sampler_pubkey_mem_addr.offset = (sampler_src_offset- 4)%(PK_MEM_NUM_DWORDS/2);
  always_comb api_pk_rho_addr = api_pubkey_addr[2:0];

  always_comb abr_reg_hwif_in.MLDSA_PUBKEY.wr_ack = abr_reg_hwif_out.MLDSA_PUBKEY.req &  abr_reg_hwif_out.MLDSA_PUBKEY.req_is_wr;
  always_comb api_pubkey_we = mldsa_ready & api_pubkey_dec & abr_reg_hwif_in.MLDSA_PUBKEY.wr_ack;

  always_comb api_pubkey_re = mldsa_valid_reg & api_pubkey_dec & ~abr_reg_hwif_out.MLDSA_PUBKEY.req_is_wr;


  always_comb pk_mem_if.we_i = (pubkey_ram_we);
  always_comb pk_mem_if.waddr_i = (pubkey_ram_waddr);
  always_comb pk_mem_if.wstrobe_i = (pubkey_ram_wstrobe);
  always_comb pk_mem_if.wdata_i = (pubkey_ram_wdata);
  always_comb pk_mem_if.re_i = (pubkey_ram_re);
  always_comb pk_mem_if.raddr_i = (pubkey_ram_raddr);
  always_comb pubkey_ram_rdata = pk_mem_if.rdata_o;

  assign pubkey_ram_rdata_t1 = pubkey_ram_rdata;

  always_comb pkdecode_rd_en = prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_PKDECODE);

  always_comb sampler_pk_rd_en = (sampler_src == MLDSA_PK_REG_ID) & (sampler_src_offset inside {[4:324]}) & ~msg_hold;

  //read requests
  always_comb pubkey_ram_re = sampler_pk_rd_en | pkdecode_rd_en | api_pubkey_re;
  always_comb pubkey_ram_raddr = ({PK_MEM_ADDR_W{sampler_pk_rd_en}} & sampler_pubkey_mem_addr.addr) |
                                 ({PK_MEM_ADDR_W{pkdecode_rd_en}} & pkdecode_rd_addr_i[PK_MEM_ADDR_W+1:2]) |
                                 ({PK_MEM_ADDR_W{api_pubkey_re}} & api_pubkey_mem_addr.addr);

  always_comb begin
    unique case (pkdecode_rd_offset_f[1:0])
      2'b00:   pkdecode_rd_data_o = pubkey_ram_rdata_t1[7:0];
      2'b01:   pkdecode_rd_data_o = pubkey_ram_rdata_t1[15:8];
      2'b10:   pkdecode_rd_data_o = pubkey_ram_rdata_t1[23:16];
      default: pkdecode_rd_data_o = pubkey_ram_rdata_t1[31:24];
    endcase
  end

  always_comb abr_reg_hwif_in.MLDSA_PUBKEY.rd_data = api_pubkey_re_f ? pubkey_ram_rdata[api_pubkey_mem_addr_f.offset] : pk_reg_rdata;

  //write requests
  always_comb pubkey_ram_we = (pk_t1_wren_i) | api_pubkey_we | zeroize_mem_we;
  always_comb pubkey_ram_waddr = ({PK_MEM_ADDR_W{pk_t1_wren_i}} & pk_t1_wr_addr_i[PK_MEM_ADDR_W+1:2]) |
                                ({PK_MEM_ADDR_W{api_pubkey_we}} & api_pubkey_mem_addr.addr) |
                                ({PK_MEM_ADDR_W{zeroize_mem_we}} & zeroize_mem_addr[PK_MEM_ADDR_W-1:0]);

  always_comb pubkey_ram_wstrobe = ({PK_MEM_WSTROBE_W{pk_t1_wren_i}} & PK_MEM_WSTROBE_W'('h3FF << pk_t1_wr_addr_i[1:0]*10)) |
                                   ({PK_MEM_WSTROBE_W{api_pubkey_we}} & PK_MEM_WSTROBE_W'('hF << api_pubkey_mem_addr.offset*4)) |
                                   ({PK_MEM_WSTROBE_W{zeroize_mem_we}});


  always_comb pubkey_ram_wdata = ({PK_MEM_DATA_W{pk_t1_wren_i}} & PK_MEM_DATA_W'(pk_t1_wrdata_i << pk_t1_wr_addr_i[1:0]*80)) |
                                 ({PK_MEM_DATA_W{(api_pubkey_we)}} & PK_MEM_DATA_W'(abr_reg_hwif_out.MLDSA_PUBKEY.wr_data << api_pubkey_mem_addr.offset*32));


  //pk reg read flop
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      pk_reg_rdata <= '0;
    end else if (zeroize) begin
      pk_reg_rdata <= '0;
    end else begin
      if (mldsa_valid_reg & api_pubkey_rho_dec)
        pk_reg_rdata <= publickey_reg.enc.rho[api_pk_rho_addr];
    end
  end

  //Public Key rho
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      publickey_reg <= '0;
    end else if (zeroize) begin
      publickey_reg <= '0;
    end else begin
      //HW write rho
      if (sampler_state_dv_i & (prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID)) begin
        publickey_reg.enc.rho <= sampler_state_data_i[0][255:0];
      end else if (mldsa_ready & api_pubkey_rho_dec & abr_reg_hwif_out.MLDSA_PUBKEY.req_is_wr) begin
        publickey_reg.enc.rho[api_pk_rho_addr] <= abr_reg_hwif_out.MLDSA_PUBKEY.wr_data;
      end
    end
  end
  
//MLKEM tie offs
  always_comb begin
    abr_reg_hwif_in.MLKEM_CIPHERTEXT.rd_ack = abr_reg_hwif_out.MLKEM_CIPHERTEXT.req & ~abr_reg_hwif_out.MLKEM_CIPHERTEXT.req_is_wr;
    abr_reg_hwif_in.MLKEM_CIPHERTEXT.wr_ack = abr_reg_hwif_out.MLKEM_CIPHERTEXT.req & abr_reg_hwif_out.MLKEM_CIPHERTEXT.req_is_wr;
    abr_reg_hwif_in.MLKEM_CIPHERTEXT.rd_data = '0;
    abr_reg_hwif_in.MLKEM_DECAPS_KEY.rd_ack = abr_reg_hwif_out.MLKEM_DECAPS_KEY.req & ~abr_reg_hwif_out.MLKEM_DECAPS_KEY.req_is_wr;
    abr_reg_hwif_in.MLKEM_DECAPS_KEY.wr_ack = abr_reg_hwif_out.MLKEM_DECAPS_KEY.req & abr_reg_hwif_out.MLKEM_DECAPS_KEY.req_is_wr;
    abr_reg_hwif_in.MLKEM_DECAPS_KEY.rd_data = '0;
    abr_reg_hwif_in.MLKEM_ENCAPS_KEY.rd_ack = abr_reg_hwif_out.MLKEM_ENCAPS_KEY.req & ~abr_reg_hwif_out.MLKEM_ENCAPS_KEY.req_is_wr;
    abr_reg_hwif_in.MLKEM_ENCAPS_KEY.wr_ack = abr_reg_hwif_out.MLKEM_ENCAPS_KEY.req & abr_reg_hwif_out.MLKEM_ENCAPS_KEY.req_is_wr;
    abr_reg_hwif_in.MLKEM_ENCAPS_KEY.rd_data = '0;
    abr_reg_hwif_in.MLKEM_CTRL.CTRL.hwclr = zeroize; //MERGE with MLDSA CTRL?
    abr_reg_hwif_in.MLKEM_NAME[0].NAME.next = '0; //FIXME need this?
    abr_reg_hwif_in.MLKEM_NAME[1].NAME.next = '0; //FIXME need this?
    abr_reg_hwif_in.MLKEM_VERSION[0].VERSION.next = '0; //FIXME need this?
    abr_reg_hwif_in.MLKEM_VERSION[1].VERSION.next = '0; //FIXME need this?
    for (int dword=0; dword < SHAREDKEY_NUM_DWORDS; dword++) begin
      abr_reg_hwif_in.MLKEM_SHARED_KEY[dword].KEY.hwclr = zeroize;
      abr_reg_hwif_in.MLKEM_SHARED_KEY[dword].KEY.next = '0;
      abr_reg_hwif_in.MLKEM_SHARED_KEY[dword].KEY.we = '0;
    end

    for (int dword=0; dword < SEED_NUM_DWORDS; dword++) begin
      abr_reg_hwif_in.MLKEM_SEED_D[dword].SEED.we = '0;
      abr_reg_hwif_in.MLKEM_SEED_D[dword].SEED.next = '0;
      abr_reg_hwif_in.MLKEM_SEED_D[dword].SEED.hwclr = zeroize;
      abr_reg_hwif_in.MLKEM_SEED_D[dword].SEED.swwe = '0;
    end

    for (int dword=0; dword < SEED_NUM_DWORDS; dword++) begin
      abr_reg_hwif_in.MLKEM_SEED_Z[dword].SEED.we = '0;
      abr_reg_hwif_in.MLKEM_SEED_Z[dword].SEED.next = '0;
      abr_reg_hwif_in.MLKEM_SEED_Z[dword].SEED.hwclr = zeroize;
      abr_reg_hwif_in.MLKEM_SEED_Z[dword].SEED.swwe = '0;
    end

    for (int dword=0; dword < MLKEM_MSG_NUM_DWORDS; dword++) begin
      abr_reg_hwif_in.MLKEM_MSG[dword].MSG.we = '0;
      abr_reg_hwif_in.MLKEM_MSG[dword].MSG.next = '0;
      abr_reg_hwif_in.MLKEM_MSG[dword].MSG.hwclr = zeroize;
      abr_reg_hwif_in.MLKEM_MSG[dword].MSG.swwe = '0;
    end

    abr_reg_hwif_in.MLKEM_STATUS.READY.next = '0;
    abr_reg_hwif_in.MLKEM_STATUS.VALID.next = '0;
  end

  //pure-MLDSA assuming 512-bit input msg and empty ctx
  //padding zeroes for highest dword to prevent x prop
  logic [MLDSA_MSG_NUM_DWORDS-1+2 : 0][DATA_WIDTH-1:0] msg_p_reg;
  always_comb begin
    if (stream_msg_mode) msg_p_reg = {512'b0 ,stream_msg_buffer_data};
    else msg_p_reg = {32'h0, 16'h0, msg_reg, 8'h00, 8'h00};
  end

  always_comb rho_reg = verifying_process ? publickey_reg.enc.rho : privatekey_reg.enc.rho;

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      msg_data <= '0;
    end else if (zeroize) begin
      msg_data <= '0;
    end else if (~msg_hold) begin
      unique case (sampler_src) inside
        MLDSA_SEED_ID:        msg_data <= msg_last ? {48'b0,sampler_imm} : {seed_reg[{sampler_src_offset[1:0],1'b1}],seed_reg[{sampler_src_offset[1:0],1'b0}]};
        MLDSA_RHO_ID:         msg_data <= msg_last ? {48'b0,sampler_imm} : rho_reg[sampler_src_offset[1:0]];
        MLDSA_RHO_P_ID:       msg_data <= msg_last ? {48'b0,sampler_imm} : rho_p_reg[sampler_src_offset[2:0]];
        MLDSA_TR_ID:          msg_data <= privatekey_reg.enc.tr[sampler_src_offset[2:0]];
        MLDSA_MSG_ID:         msg_data <= {msg_p_reg[{sampler_src_offset[3:0],1'b1}],msg_p_reg[{sampler_src_offset[3:0],1'b0}]};
        MLDSA_K_ID:           msg_data <= privatekey_reg.enc.K[sampler_src_offset[1:0]];
        MLDSA_MU_ID:          msg_data <= mu_reg[sampler_src_offset[2:0]];
        MLDSA_SIGN_RND_ID:    msg_data <= {sign_rnd_reg[{sampler_src_offset[1:0],1'b1}],sign_rnd_reg[{sampler_src_offset[1:0],1'b0}]};
        MLDSA_RHO_P_KAPPA_ID: msg_data <= msg_last ? {48'b0,(kappa_reg + sampler_imm[2:0])} : rho_p_reg[sampler_src_offset[2:0]];
        MLDSA_SIG_C_REG_ID:   msg_data <= {signature_reg.enc.c[{sampler_src_offset[2:0],1'b1}], signature_reg.enc.c[{sampler_src_offset[2:0],1'b0}]};
        MLDSA_PK_REG_ID:      msg_data <= {publickey_reg.enc.rho[{sampler_src_offset[1:0],1'b1}],publickey_reg.enc.rho[{sampler_src_offset[1:0],1'b0}]};
        MLDSA_ENTROPY_ID:     msg_data <= lfsr_entropy_reg[sampler_src_offset[2:0]];
        MLDSA_CNT_ID:         msg_data <= counter_reg;
        default:              msg_data <= '0;
      endcase
    end 
  end

  always_comb begin
    msg_data_o[0] = sampler_pk_rd_en_f ? {pubkey_ram_rdata[{sampler_src_offset_f[2:0],1'b1}],pubkey_ram_rdata[{sampler_src_offset_f[2:0],1'b0}]} : 
                    msg_data;
  end
  
  //If we're storing state directly into registers, do that here
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      rho_p_reg <= 0;
    end
    else if (zeroize) begin
      rho_p_reg <= 0;
    end
    else if (sampler_state_dv_i) begin
      if (prim_instr.operand3 == MLDSA_DEST_K_RHO_REG_ID) begin
        rho_p_reg <= sampler_state_data_i[0][767:256];
      end
      else if (prim_instr.operand3 == MLDSA_DEST_RHO_P_REG_ID) begin
        rho_p_reg <= sampler_state_data_i[0][511:0];
      end
    end
  end

  always_comb begin
    internal_mu_we = sampler_state_dv_i & (prim_instr.operand3 == MLDSA_DEST_MU_REG_ID);
    internal_mu_reg = sampler_state_data_i[0][511:0];
    mu_reg = external_mu_reg;
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
      if (prim_instr.operand3 == MLDSA_DEST_LFSR_SEED_REG_ID) begin
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
      mldsa_valid_reg <= mldsa_valid_reg | process_done;
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
      keygen_process <= process_done ? '0 : keygen_process | keygen_process_nxt;
      signing_process <= process_done ? '0 : signing_process | signing_process_nxt;
      verifying_process <= process_done ? '0 : verifying_process | verifying_process_nxt;
      keygen_signing_process <= process_done ? '0 : keygen_signing_process | keygen_signing_process_nxt;
    end
  end

  always_comb process_done = (keygen_process & keygen_done) |
                             (signing_process & signature_done) |
                             (verifying_process & verify_done);

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)
      external_mu_mode <= 0;  
    else if (zeroize | process_done)
      external_mu_mode <= 0;  
    else if (process_done)
      external_mu_mode <= 0;
    else 
      external_mu_mode <= external_mu_mode | external_mu_mode_nxt;
  end
      
  //Clear signature if makehint or normcheck fail
  always_comb clear_signature_valid = signing_process & ((makehint_done_i & makehint_invalid_i) | (normcheck_done_i & normcheck_invalid_i));

  //Jump to done if this happens, could cause x reads (or fix sigdecode to not stop early)
  always_comb clear_verify_valid = verifying_process & ((normcheck_done_i & normcheck_invalid_i) | 
                                   (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & sigdecode_h_invalid_i));
                                   
//Primary sequencer for keygen, signing, and verify
  always_comb subcomponent_busy = !(prim_ctrl_fsm_ns inside {ABR_CTRL_IDLE, ABR_CTRL_MSG_WAIT}) |
                                  sampler_busy_i | ntt_busy[0];
`ifdef CALIPTRA
  always_comb pcr_sign_input_invalid = (cmd_reg inside {MLDSA_KEYGEN, MLDSA_SIGN, MLDSA_VERIFY}) & pcr_sign_mode;
  always_comb error_flag = skdecode_error_i | pcr_sign_input_invalid;
`else
  always_comb error_flag = skdecode_error_i;
`endif                                  

  always_ff @(posedge clk or negedge rst_b) 
  begin : error_detection
      if(!rst_b)
          error_flag_reg <= 1'b0;
      else if(zeroize)
          error_flag_reg <= 1'b0;
      else if (error_flag)
          error_flag_reg <= 1'b1;
  end // error_detection

  always_comb error_flag_edge = error_flag & (!error_flag_reg);

  //program counter
  always_ff @(posedge clk or negedge rst_b) begin
    if(!rst_b) begin
      prim_prog_cntr <= MLDSA_RESET;
    end
    else if(zeroize) begin
      prim_prog_cntr <= MLDSA_ZEROIZE;
    end
    else begin
      if (error_flag_edge) begin
        prim_prog_cntr <= MLDSA_ERROR;
      end
      else begin
        prim_prog_cntr <= prim_prog_cntr_nxt;
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
    signature_done = 0;
    verify_done = 0;
    set_y_valid = 0;
    set_w0_valid = 0;
    set_c_valid = 0;
    update_kappa = 0;
    set_verify_valid = 0;
    set_entropy = 0;
    prim_prog_cntr_nxt = MLDSA_RESET;
    prim_seq_en = !zeroize;
    external_mu_mode_nxt = 0;    
    clear_c_valid = 0;
    clear_y_valid = 0;
    clear_w0_valid = 0;
    set_signature_valid = 0;

    unique case (prim_prog_cntr) inside
      MLDSA_RESET : begin 
        // Waiting for new valid command
        unique case (cmd_reg) inside
          MLDSA_KEYGEN : begin  // keygen
            prim_prog_cntr_nxt = MLDSA_KG_S;
            keygen_process_nxt = 1;
            set_entropy = 1;
            external_mu_mode_nxt = 0;
          end   
          MLDSA_SIGN : begin  // signing
            prim_prog_cntr_nxt = MLDSA_SIGN_S;
            signing_process_nxt  = 1;
            set_entropy = 1;
            external_mu_mode_nxt = external_mu;
          end                                   
          MLDSA_VERIFY : begin  // verifying
            prim_prog_cntr_nxt = MLDSA_VERIFY_S;
            verifying_process_nxt  = 1;
            set_verify_valid = 1;
            external_mu_mode_nxt = external_mu;
          end                          
          MLDSA_KEYGEN_SIGN : begin  // KEYGEN + SIGNING 
            prim_prog_cntr_nxt = MLDSA_KG_S;
            keygen_signing_process_nxt  = 1;
            set_signature_valid = 1;
            set_entropy = 1;
            external_mu_mode_nxt = external_mu;
          end
          default : begin
            prim_prog_cntr_nxt = MLDSA_RESET;
            prim_seq_en = 0;
            external_mu_mode_nxt = 0;
          end
        endcase
      end
      MLDSA_ZEROIZE : begin
        if (zeroize_mem_done)
          prim_prog_cntr_nxt = MLDSA_RESET;
        else
          prim_prog_cntr_nxt = MLDSA_ZEROIZE;
        prim_seq_en = 0;  
      end     
      MLDSA_KG_JUMP_SIGN : begin
        //Jump to signing process
        if (keygen_signing_process) begin
          set_signature_valid = 1;
          prim_prog_cntr_nxt = MLDSA_SIGN_CHECK_MODE;
          signing_process_nxt  = 1;
        end
        else begin
          prim_prog_cntr_nxt = prim_prog_cntr + 1;
        end
      end
      MLDSA_KG_E : begin // end of keygen
        //prim_prog_cntr_nxt = MLDSA_RESET;
        keygen_done = 1;
      end
      MLDSA_SIGN_CHECK_MODE : begin
        if (external_mu_mode)
          prim_prog_cntr_nxt = MLDSA_SIGN_H_RHO_P;
        else
          prim_prog_cntr_nxt = MLDSA_SIGN_H_MU;
      end
      MLDSA_SIGN_CHL_E : begin // end of challenge generation
        if (signature_valid) 
          prim_prog_cntr_nxt = MLDSA_SIGN_E;
        else begin
          set_signature_valid = 1;
          //increment kappa value
          update_kappa = 1;
          //restart challenge generation
          prim_prog_cntr_nxt = MLDSA_SIGN_LFSR_S;
       end
      end
      MLDSA_SIGN_E : begin // end of signature
        signature_done = 1;
      end
      MLDSA_VERIFY_CHECK_MODE : begin
        if (external_mu_mode)
          prim_prog_cntr_nxt = MLDSA_VERIFY_MAKE_C;
        else
          prim_prog_cntr_nxt = MLDSA_VERIFY_H_MU;
      end
      MLDSA_VERIFY_E : begin // end of verify flow
        verify_done = 1;
      end
      default : begin
        if (clear_verify_valid)
          prim_prog_cntr_nxt = MLDSA_VERIFY_E;
        else if (subcomponent_busy) begin //Stalled until sub-component is done 
          prim_prog_cntr_nxt = prim_prog_cntr;
        end
        else begin
          prim_prog_cntr_nxt = prim_prog_cntr + 1;
        end
      end
    endcase
  end

//Controller prim_instr decode - drives sampler and primary ntt
  always_comb begin
    sampler_mode_o = ABR_SAMPLER_NONE;
    if (prim_instr.opcode.sampler_en) begin
      if (prim_instr.opcode.ntt_en & prim_instr.opcode.mode.ntt_mode inside {MLDSA_PWM_SMPL, MLDSA_PWM_ACCUM_SMPL}) begin
        sampler_mode_o = MLDSA_REJ_SAMPLER;
      end else begin
        sampler_mode_o = prim_instr.opcode.mode.sampler_mode;
      end
    end else if (prim_instr.opcode.keccak_en) begin
      sampler_mode_o = prim_instr.opcode.mode.sampler_mode;
    end else if (prim_instr.opcode.aux_en) begin
      if (prim_instr.opcode.mode.aux_mode == MLDSA_DECOMP) begin
        sampler_mode_o = ABR_SHAKE256;
      end
    end
  end

  always_comb sampler_src_offset = {4'b0, msg_cnt};

  always_comb dest_base_addr_o = prim_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src0_base_addr_o[0] = prim_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_src1_base_addr_o[0] = prim_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0];
  always_comb aux_dest_base_addr_o[0] = prim_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0];

  always_comb normcheck_mode_o = (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_NORMCHK)) ? prim_instr.imm[1:0] : '0;

//Message streaming mode
//new input data available
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    stream_msg_valid <= 0;
  end
  else if (zeroize) begin
    stream_msg_valid <= 0;
  end
  else if (stream_msg_rdy) begin
    stream_msg_valid <= abr_reg_hwif_out.MLDSA_MSG[0].MSG.swmod;
  end
end 

//set stream message ip when given instruction to load MSG
always_comb stream_msg_ip = stream_msg_mode & (prim_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) & (sampler_src == MLDSA_MSG_ID);

//count how many dwords of ctx sent
always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    ctx_cnt <= 0;
  end
  else if (zeroize) begin
    ctx_cnt <= 0;
  end
  else begin
    ctx_cnt <= ctx_cnt_nxt;
  end
end 

always_comb {ctx_cnt_required,ctx_cnt_offset} = ctx_size;

always_comb begin
  stream_msg_fsm_ns = stream_msg_fsm_ps;
  stream_msg_buffer_flush = 0;
  stream_msg_rdy = 0;
  stream_msg_done = 0;
  stream_msg_strobe = 0;
  stream_msg_data = 0;
  stream_msg_last = 0;
  ctx_cnt_nxt = 0;
  unique case (stream_msg_fsm_ps) inside
    MLDSA_MSG_IDLE: begin
      if (stream_msg_ip) stream_msg_fsm_ns = MLDSA_MSG_CTX_SIZE;
    end
    MLDSA_MSG_CTX_SIZE: begin
      //Drive context mode and size - 2 bytes
      stream_msg_strobe = 4'b0011;
      stream_msg_data = {16'h0, ctx_size, 8'h00};
      stream_msg_fsm_ns = MLDSA_MSG_CTX;
    end
    MLDSA_MSG_CTX: begin
      //Drive context
      ctx_cnt_nxt = ctx_cnt + 1;
      stream_msg_last = ctx_cnt >= ctx_cnt_required;
      stream_msg_strobe = stream_msg_last ? ~(STREAM_MSG_STROBE_W'('1) << ctx_cnt_offset) : '1;
      stream_msg_data = ctx_reg[ctx_cnt];
      if (ctx_cnt >= ctx_cnt_required) begin
        stream_msg_fsm_ns = MLDSA_MSG_RDY;
        ctx_cnt_nxt = 0;
      end
    end
    MLDSA_MSG_RDY: begin
      //Stream msg
      stream_msg_rdy = 1;
      stream_msg_strobe = stream_msg_valid ? abr_reg_hwif_out.MLDSA_MSG_STROBE.STROBE.value : '0;
      stream_msg_data = abr_reg_hwif_out.MLDSA_MSG[0].MSG.value;
      if ((stream_msg_strobe != '1) & stream_msg_valid) begin
        stream_msg_fsm_ns = MLDSA_MSG_FLUSH;
      end
    end
    MLDSA_MSG_FLUSH: begin
      //Flush buffer
      stream_msg_buffer_flush = 1;
      if (stream_msg_buffer_strobe == '0) begin
        stream_msg_fsm_ns = MLDSA_MSG_DONE;
      end
    end
    MLDSA_MSG_DONE: begin
      stream_msg_done = 1;
      stream_msg_fsm_ns = MLDSA_MSG_IDLE;
    end
  endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : stream_msg_fsm_flops
  if (!rst_b) begin
    stream_msg_fsm_ps <= MLDSA_MSG_IDLE;
  end
  else if (zeroize) begin
    stream_msg_fsm_ps <= MLDSA_MSG_IDLE;
  end
  else begin
    stream_msg_fsm_ps <= stream_msg_fsm_ns;
  end
end 

//Buffer msg data to align to msg interface
abr_msg_buffer #(
  .NUM_WR(STREAM_MSG_STROBE_W),
  .NUM_RD(MsgStrbW),
  .BUFFER_DATA_W(8) //stores on byte level
) stream_msg_buffer (
  .clk(clk),
  .rst_b(rst_b),
  .flush(stream_msg_buffer_flush),
  //input data
  .data_valid_i(stream_msg_strobe),
  .data_i(stream_msg_data),
  .buffer_full_o(),
  //output data
  .data_valid_o(stream_msg_buffer_strobe),
  .data_hold_i('0),
  .data_o(stream_msg_buffer_data)
);

//send valid when full packet, or when flushing
always_comb stream_msg_buffer_valid = stream_msg_buffer_flush ? (|stream_msg_buffer_strobe) : (&stream_msg_buffer_strobe);

//determine the number of bytes in the last message
//operand 2 contains the length of the message being fed to sha3
//shift a zero into the strobe for each byte, and invert to get the valid bytes
always_comb last_msg_strobe = ~(MsgStrbW'('1) << prim_instr.length[$clog2(MsgStrbW)-1:0]);
 
always_comb msg_hold = msg_valid_o & ~msg_rdy_i;

//Last cycle when msg count is equal to length
//length is in bytes - compare against MSB from strobe width gets us the length in msg interface chunks
always_comb msg_last = stream_msg_ip ? '0 : (msg_cnt == prim_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]);
always_comb msg_done = stream_msg_ip ? stream_msg_done : (msg_cnt > prim_instr.length[ABR_OPR_WIDTH-1:$clog2(MsgStrbW)]);

//overload msg interface with stream msg interface
always_comb msg_cnt_nxt = stream_msg_ip ? '0 :
                          msg_done ? '0 :
                          msg_valid ? msg_cnt + 'd1 : msg_cnt;
always_comb msg_valid_nxt = stream_msg_ip ? stream_msg_buffer_valid : msg_valid;
always_comb msg_strobe_nxt = stream_msg_ip ? stream_msg_buffer_strobe :
                             msg_last ? last_msg_strobe : '1;

always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    msg_cnt <= 0;
    msg_valid_o <= 0;
    msg_strobe_o <= 0;
  end
  else if (zeroize) begin
    msg_cnt <= 0;
    msg_valid_o <= 0;
    msg_strobe_o <= 0;
  end
  else begin
    msg_cnt <= msg_hold ? msg_cnt : msg_cnt_nxt;
    msg_valid_o <= msg_hold ? msg_valid_o : msg_valid_nxt;
    msg_strobe_o <= msg_hold ? msg_strobe_o : msg_strobe_nxt;
  end
end

always_comb decompose_mode_o = prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_USEHINT);

//State logic
always_comb begin : primary_ctrl_fsm_out_combo
    prim_ctrl_fsm_ns = prim_ctrl_fsm_ps;
    sha3_start_o = '0;
    msg_start_o = '0;
    msg_valid = '0;
    sampler_start_o = '0;
    sampler_src = '0;
    sampler_imm = '0;
    ntt_en[0] = '0;
    ntt_active[0] = '0;
    power2round_enable_o = '0;
    decompose_enable_o = '0;
    skencode_enable_o = '0;
    pkdecode_enable_o = '0;
    sigdecode_h_enable_o = '0;
    sigdecode_z_enable_o = '0;
    skdecode_enable_o = '0;
    makehint_enable_o = '0;
    sigencode_enable_o = '0;
    normcheck_enable_o = '0;
    lfsr_enable_o = '0;

    unique case (prim_ctrl_fsm_ps)
      ABR_CTRL_IDLE: begin
        //load keccak data to SIPO
        if (prim_instr.opcode.keccak_en)
          prim_ctrl_fsm_ns = ABR_CTRL_SHA3_START;
        //start sampler flow, data already driven to SIPO
        else if ((prim_instr.opcode.sampler_en | prim_instr.opcode.aux_en | prim_instr.opcode.ntt_en) & ~ntt_busy[0])
          prim_ctrl_fsm_ns = ABR_CTRL_FUNC_START;
      end
      ABR_CTRL_SHA3_START: begin
        prim_ctrl_fsm_ns = ABR_CTRL_MSG_START;
        //drive start
        sha3_start_o = 1;
      end
      ABR_CTRL_MSG_START: begin
        prim_ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
        msg_start_o = 1;
      end
      ABR_CTRL_MSG_LOAD: begin
        msg_valid = 1;
        sampler_src = prim_instr.operand1;
        sampler_imm = prim_instr.imm;
        if (msg_done & ~msg_hold) begin
          msg_valid = 0;
          if (prim_instr.opcode.sampler_en & ~ntt_busy[0]) prim_ctrl_fsm_ns = ABR_CTRL_FUNC_START;
          else prim_ctrl_fsm_ns = ABR_CTRL_MSG_WAIT;
        end
      end
      ABR_CTRL_MSG_WAIT: begin
        //load another message
        if (prim_instr.opcode.keccak_en) prim_ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
        //kick off the sampler
        else if ((prim_instr.opcode.sampler_en | prim_instr.opcode.aux_en | prim_instr.opcode.ntt_en) & ~ntt_busy[0])
          prim_ctrl_fsm_ns = ABR_CTRL_FUNC_START;
        else 
          prim_ctrl_fsm_ns = ABR_CTRL_MSG_LOAD;
      end
      ABR_CTRL_FUNC_START: begin
        prim_ctrl_fsm_ns = ABR_CTRL_DONE;
        sampler_start_o = prim_instr.opcode.sampler_en;
        ntt_en[0] = prim_instr.opcode.ntt_en;
        ntt_active[0] = prim_instr.opcode.ntt_en;
        if (prim_instr.opcode.aux_en) begin
          power2round_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_PWR2RND);
          decompose_enable_o = (prim_instr.opcode.mode.aux_mode inside {MLDSA_DECOMP,MLDSA_USEHINT});
          skencode_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_SKENCODE);
          pkdecode_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_PKDECODE);
          sigdecode_h_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H);
          sigdecode_z_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_Z);
          skdecode_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_SKDECODE);
          makehint_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_MAKEHINT);
          sigencode_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_SIGENC);
          normcheck_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_NORMCHK);
          lfsr_enable_o = (prim_instr.opcode.mode.aux_mode == MLDSA_LFSR);
        end
      end
      ABR_CTRL_DONE: begin
        ntt_active[0] = prim_instr.opcode.ntt_en;
        if ((~sampler_busy_i & ~ntt_busy[0] & ~prim_instr.opcode.aux_en) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode inside {MLDSA_DECOMP,MLDSA_USEHINT}) & decompose_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_PWR2RND) & power2round_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SKENCODE) & skencode_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_PKDECODE) & pkdecode_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_H) & sigdecode_h_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SIGDEC_Z) & sigdecode_z_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_NORMCHK) & normcheck_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SKDECODE) & skdecode_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_MAKEHINT) & makehint_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_SIGENC) & sigencode_done_i) |
            (prim_instr.opcode.aux_en & (prim_instr.opcode.mode.aux_mode == MLDSA_LFSR)) ) begin
          
          prim_ctrl_fsm_ns = ABR_CTRL_IDLE;

        end
      end
      default: begin
      end
    endcase
end

//State flop
always_ff @(posedge clk or negedge rst_b) begin : primary_ctrl_fsm_flops
  if (!rst_b) begin
      prim_ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else if (zeroize) begin
      prim_ctrl_fsm_ps <= ABR_CTRL_IDLE;
  end
  else begin
      prim_ctrl_fsm_ps <= prim_ctrl_fsm_ns;
  end
end  

mldsa_seq_prim mldsa_seq_prim_inst
(
  .clk(clk),

  .en_i(prim_seq_en),
  .addr_i(prim_prog_cntr_nxt),
  .data_o(prim_instr_o)
);

//NTT gasket
//If we have 2 NTT, connect to 0/1
//If we have 1 NTT, connect both to 0
localparam PRIM_SEQ_NTT = 0;
localparam SEC_SEQ_NTT = ABR_NUM_NTT-1;

//Check if ntt is being enabled in this clock also
always_comb ntt_busy[0] = prim_instr.opcode.ntt_en & (ntt_busy_i[PRIM_SEQ_NTT] | ntt_enable_o[PRIM_SEQ_NTT]);
always_comb ntt_busy[1] = 1'b0; //FIXME for mlkem sec_instr.opcode.ntt_en & (ntt_busy_i[SEC_SEQ_NTT] | ntt_enable_o[SEC_SEQ_NTT]);

always_comb begin
  for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
    ntt_enable_o[ntt] = '0;
    ntt_mode_o[ntt] = MLDSA_NTT_NONE;
    ntt_masking_en_o[ntt] = '0;
    ntt_shuffling_en_o[ntt] = '0;
    ntt_temp_address[ntt] = '0;
    ntt_mem_base_addr_o[ntt] = '0;
    pwo_mem_base_addr_o[ntt] = '0;
  end
  if (ntt_active[0]) begin
    ntt_enable_o[PRIM_SEQ_NTT] = ntt_en[0]; //this comes from prim sequencer
    ntt_mode_o[PRIM_SEQ_NTT] = prim_instr.opcode.mode.ntt_mode;
    ntt_masking_en_o[PRIM_SEQ_NTT] = prim_instr.opcode.masking_en;
    ntt_shuffling_en_o[PRIM_SEQ_NTT] = prim_instr.opcode.shuffling_en;
    //passing a bit on the immediate field to mux between temp address locations
    ntt_temp_address[PRIM_SEQ_NTT] = prim_instr.imm[0] ? MLDSA_TEMP2_BASE : MLDSA_TEMP0_BASE;
    //optimization - could be one interface here?
    ntt_mem_base_addr_o[PRIM_SEQ_NTT] = '{src_base_addr:prim_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                          interim_base_addr:ntt_temp_address[PRIM_SEQ_NTT],
                                          dest_base_addr:prim_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};
    pwo_mem_base_addr_o[PRIM_SEQ_NTT] = '{pw_base_addr_b:prim_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //PWO src
                                          pw_base_addr_a:prim_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //PWO src or sampler src
                                          pw_base_addr_c:prim_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};                                   
  end
/* FIXME for ML-KEM
  if (ntt_active[1]) begin
    ntt_enable_o[SEC_SEQ_NTT] = ntt_en[1]; //this comes from sec seq
    ntt_mode_o[SEC_SEQ_NTT] = sec_instr.opcode.mode.ntt_mode;
    ntt_masking_en_o[SEC_SEQ_NTT] = sec_instr.opcode.masking_en;
    ntt_shuffling_en_o[SEC_SEQ_NTT] = sec_instr.opcode.shuffling_en;
    //passing a bit on the immediate field to mux between temp address locations
    ntt_temp_address[SEC_SEQ_NTT] = sec_instr.imm[0] ? MLDSA_TEMP2_BASE : MLDSA_TEMP0_BASE;

    //one interface here?
    ntt_mem_base_addr_o[SEC_SEQ_NTT] = '{src_base_addr:sec_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0],
                                         interim_base_addr:ntt_temp_address[SEC_SEQ_NTT],
                                         dest_base_addr:sec_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};

    pwo_mem_base_addr_o[SEC_SEQ_NTT] = '{pw_base_addr_b:sec_instr.operand1[ABR_MEM_ADDR_WIDTH-1:0], //PWO src
                                         pw_base_addr_a:sec_instr.operand2[ABR_MEM_ADDR_WIDTH-1:0], //PWO src or sampler src
                                         pw_base_addr_c:sec_instr.operand3[ABR_MEM_ADDR_WIDTH-1:0]};
  end
*/  
end

//Zeroizer
always_comb prim_instr = ((prim_prog_cntr == MLDSA_ZEROIZE) | (prim_prog_cntr == MLDSA_RESET))? '0 : prim_instr_o;

always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    zeroize_mem_addr <= 0;
    zeroize_mem_done <= 0;
  end
  else if (zeroize) begin
    zeroize_mem_addr <= 0;
    zeroize_mem_done <= 0;
  end
  else if (prim_prog_cntr == MLDSA_ZEROIZE) begin
    if (zeroize_mem_addr == ABR_MEM_MAX_DEPTH) begin
      zeroize_mem_addr <= 0;
      zeroize_mem_done <= 1;
    end else begin
      zeroize_mem_addr <= zeroize_mem_addr + 1;
    end
  end else begin
    zeroize_mem_addr <= 0;
    zeroize_mem_done <= 0;
  end
end

always_comb zeroize_mem_we = (prim_prog_cntr == MLDSA_ZEROIZE);

always_comb zeroize_mem_o.rd_wr_en = zeroize_mem_we? RW_WRITE : RW_IDLE;
always_comb zeroize_mem_o.addr = zeroize_mem_addr;
  
`ifdef RV_FPGA_SCA
    //===========================================================================
    //
    //      ************** TRIGER Functionality **************
    //
    //===========================================================================
    logic NTT_raw_signal, PWM_raw_signal, PWA_raw_signal, INTT_raw_signal;
    gen_pulse_custom NTT_pulse
    (
        .clk(clk),
        .reset_n(rst_b),
        .raw_signal(NTT_raw_signal),
        .trigger_pulse(NTT_trigger)
    );

    gen_pulse_custom PWM_pulse
    (
        .clk(clk),
        .reset_n(rst_b),
        .raw_signal(PWM_raw_signal),
        .trigger_pulse(PWM_trigger)
    );
    
    gen_pulse_custom PWA_pulse
    (
        .clk(clk),
        .reset_n(rst_b),
        .raw_signal(PWA_raw_signal),
        .trigger_pulse(PWA_trigger)
    );

    gen_pulse_custom INTT_pulse
    (
        .clk(clk),
        .reset_n(rst_b),
        .raw_signal(INTT_raw_signal),
        .trigger_pulse(INTT_trigger)
    );

    always_ff @(posedge clk or negedge rst_b) begin
        if (!rst_b) begin
            NTT_raw_signal <= 'h0;
            PWM_raw_signal <= 'h0;
            PWA_raw_signal <= 'h0;
            INTT_raw_signal <= 'h0;
        end 
        else if (zeroize) begin
            NTT_raw_signal <= 'h0;
            PWM_raw_signal <= 'h0;
            PWA_raw_signal <= 'h0;
            INTT_raw_signal <= 'h0;
        end 
        else begin
            if (sec_seq_en) begin
                unique case(sec_prog_cntr_nxt)
                    MLDSA_SIGN_VALID_S : begin //NTT(C)
                        NTT_raw_signal <= 'h1;
                        PWM_raw_signal <= 'h0;
                        PWA_raw_signal <= 'h0;
                        INTT_raw_signal <= 'h0;
                    end
                    MLDSA_SIGN_VALID_S+2 : begin
                        NTT_raw_signal <= 'h0;
                        PWM_raw_signal <= 'h1;
                        PWA_raw_signal <= 'h0;
                        INTT_raw_signal <= 'h0;
                    end
                    MLDSA_SIGN_VALID_S+4 : begin
                        NTT_raw_signal <= 'h0;
                        PWM_raw_signal <= 'h0;
                        PWA_raw_signal <= 'h1;
                        INTT_raw_signal <= 'h0;
                    end
                    MLDSA_SIGN_VALID_S+3 : begin
                        NTT_raw_signal <= 'h0;
                        PWM_raw_signal <= 'h0;
                        PWA_raw_signal <= 'h0;
                        INTT_raw_signal <= 'h1;
                    end
                    default : begin
                        NTT_raw_signal <= 'h0;
                        PWM_raw_signal <= 'h0;
                        PWA_raw_signal <= 'h0;
                        INTT_raw_signal <= 'h0;
                    end
                endcase 
            end
        end
    end
`endif

  `ABR_ASSERT_KNOWN(ERR_PRIM_CTRL_FSM_X, {prim_ctrl_fsm_ps}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_NTT_MEM_X, {ntt_mem_base_addr_o}, clk, !rst_b) 
  `ABR_ASSERT_KNOWN(ERR_PWO_MEM_X, {pwo_mem_base_addr_o}, clk, !rst_b)
  `ABR_ASSERT_KNOWN(ERR_REG_HWIF_X, {abr_reg_hwif_in_o}, clk, !rst_b)
  `ABR_ASSERT(ZEROIZE_SEED_REG, $fell(zeroize) |-> (seed_reg === '0), clk, !rst_b)
  //Assumption that stream message is never fast enough to get stalled
  `ABR_ASSERT_NEVER(ERR_STREAM_MSG_STALLED, !(stream_msg_fsm_ps inside {MLDSA_MSG_IDLE}) & msg_hold, clk, !rst_b)

endmodule
