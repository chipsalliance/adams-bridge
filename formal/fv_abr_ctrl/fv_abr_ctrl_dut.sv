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

module fv_abr_ctrl_dut
  import abr_reg_pkg::*;
  import abr_sha3_pkg::*;
  import abr_sampler_pkg::*;
  import abr_ctrl_pkg::*;
  import abr_params_pkg::*;
  import ntt_defines_pkg::*;
  import compress_defines_pkg::*;
  import decompress_defines_pkg::*;
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
  output abr_ntt_mode_e [ABR_NUM_NTT-1:0]   ntt_mode_o,
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
  input logic [7:0][9:0] pk_t1_wrdata_i, // : change to parameter
  input logic [7:0] pk_t1_wr_addr_i, // : change to parameter
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

  output logic compress_enable_o,
  output compress_mode_t compress_mode_o,
  output logic compress_compare_mode_o,
  output logic [2:0] compress_num_poly_o,
  input logic compress_done_i,
  input logic compress_compare_failed_i,
  input logic [1:0] compress_api_rw_en_i,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] compress_api_rw_addr_i,
  input logic [DATA_WIDTH-1:0] compress_api_wr_data_i,
  output logic [DATA_WIDTH-1:0] compress_api_rd_data_o,

  output logic decompress_enable_o,
  input logic decompress_done_i,
  output decompress_mode_t decompress_mode_o,
  output logic [2:0] decompress_num_poly_o,
  input logic decompress_api_rd_en_i,
  input logic [ABR_MEM_ADDR_WIDTH-1:0] decompress_api_rd_addr_i,
  output logic [1:0][DATA_WIDTH-1:0] decompress_api_rd_data_o,

  output logic lfsr_enable_o,
  output logic [1:0][LFSR_W-1:0] lfsr_seed_o,

  //Memory interface export
  //abr_sram_if.req sk_bank0_mem_if,
  //abr_sram_if.req sk_bank1_mem_if,
  //abr_sram_be_if.req sig_z_mem_if,
  //abr_sram_be_if.req pk_mem_if,
  output logic                                        po_sk_bank0_mem_if_we_i,
  output logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank0_mem_if_waddr_i,
  output logic [SK_MEM_BANK_DATA_W-1:0]               po_sk_bank0_mem_if_wdata_i,
  output logic                                        po_sk_bank0_mem_if_re_i,
  output logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank0_mem_if_raddr_i,
  input logic [SK_MEM_BANK_DATA_W-1:0]                pi_sk_bank0_mem_if_rdata_o,
  output logic                                        po_sk_bank1_mem_if_we_i,
  output logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank1_mem_if_waddr_i,
  output logic [SK_MEM_BANK_DATA_W-1:0]               po_sk_bank1_mem_if_wdata_i,
  output logic                                        po_sk_bank1_mem_if_re_i,
  output logic [SK_MEM_BANK_ADDR_W-1:0]               po_sk_bank1_mem_if_raddr_i,
  input logic [SK_MEM_BANK_DATA_W-1:0]                pi_sk_bank1_mem_if_rdata_o,
  output logic                                        po_sig_z_mem_if_we_i,
  output logic [SIG_Z_MEM_ADDR_W-1:0]                 po_sig_z_mem_if_waddr_i,
  output logic [SIG_Z_MEM_DATA_W-1:0]                 po_sig_z_mem_if_wdata_i,
  output logic [SIG_Z_MEM_DATA_W/8-1:0]               po_sig_z_mem_if_wstrobe_i,
  output logic                                        po_sig_z_mem_if_re_i,
  output logic [SIG_Z_MEM_ADDR_W-1:0]                 po_sig_z_mem_if_raddr_i,
  input logic [SIG_Z_MEM_DATA_W-1:0]                  pi_sig_z_mem_if_rdata_o,
  output logic                                        po_pk_mem_if_we_i,
  output logic [PK_MEM_ADDR_W-1:0]                    po_pk_mem_if_waddr_i,
  output logic [PK_MEM_DATA_W-1:0]                    po_pk_mem_if_wdata_i,
  output logic [PK_MEM_DATA_W/8-1:0]                  po_pk_mem_if_wstrobe_i,
  output logic                                        po_pk_mem_if_re_i,
  output logic [PK_MEM_ADDR_W-1:0]                    po_pk_mem_if_raddr_i,
  input logic [PK_MEM_DATA_W-1:0]                     pi_pk_mem_if_rdata_o,

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

    //memory interfaces
  abr_sram_if #(.ADDR_W(SK_MEM_BANK_ADDR_W), .DATA_W(SK_MEM_BANK_DATA_W)) fv_sk_bank0_mem_if();
  abr_sram_if #(.ADDR_W(SK_MEM_BANK_ADDR_W), .DATA_W(SK_MEM_BANK_DATA_W)) fv_sk_bank1_mem_if();
  abr_sram_be_if #(.ADDR_W(SIG_Z_MEM_ADDR_W), .DATA_W(SIG_Z_MEM_DATA_W)) fv_sig_z_mem_if();
  abr_sram_be_if #(.ADDR_W(PK_MEM_ADDR_W), .DATA_W(PK_MEM_DATA_W)) fv_pk_mem_if();

  always_comb begin : fv_mem_if_connections
    //sk_bank0_mem_if
    po_sk_bank0_mem_if_we_i   = fv_sk_bank0_mem_if.we_i;
    po_sk_bank0_mem_if_waddr_i = fv_sk_bank0_mem_if.waddr_i;
    po_sk_bank0_mem_if_wdata_i = fv_sk_bank0_mem_if.wdata_i;
    po_sk_bank0_mem_if_re_i    = fv_sk_bank0_mem_if.re_i;
    po_sk_bank0_mem_if_raddr_i = fv_sk_bank0_mem_if.raddr_i;
    fv_sk_bank0_mem_if.rdata_o = pi_sk_bank0_mem_if_rdata_o;

    //sk_bank1_mem_if
    po_sk_bank1_mem_if_we_i    = fv_sk_bank1_mem_if.we_i;
    po_sk_bank1_mem_if_waddr_i = fv_sk_bank1_mem_if.waddr_i;
    po_sk_bank1_mem_if_wdata_i = fv_sk_bank1_mem_if.wdata_i;
    po_sk_bank1_mem_if_re_i    = fv_sk_bank1_mem_if.re_i;
    po_sk_bank1_mem_if_raddr_i = fv_sk_bank1_mem_if.raddr_i;
    fv_sk_bank1_mem_if.rdata_o = pi_sk_bank1_mem_if_rdata_o;

    //sig_z_mem_if
    po_sig_z_mem_if_we_i = fv_sig_z_mem_if.we_i;
    po_sig_z_mem_if_waddr_i = fv_sig_z_mem_if.waddr_i;
    po_sig_z_mem_if_wdata_i = fv_sig_z_mem_if.wdata_i;
    po_sig_z_mem_if_wstrobe_i = fv_sig_z_mem_if.wstrobe_i;
    po_sig_z_mem_if_re_i = fv_sig_z_mem_if.re_i;
    po_sig_z_mem_if_raddr_i = fv_sig_z_mem_if.raddr_i;
    fv_sig_z_mem_if.rdata_o  = pi_sig_z_mem_if_rdata_o;

    //pk_mem_if
    po_pk_mem_if_we_i = fv_pk_mem_if.we_i;
    po_pk_mem_if_waddr_i = fv_pk_mem_if.waddr_i;
    po_pk_mem_if_wdata_i = fv_pk_mem_if.wdata_i;
    po_pk_mem_if_wstrobe_i = fv_pk_mem_if.wstrobe_i;
    po_pk_mem_if_re_i = fv_pk_mem_if.re_i;
    po_pk_mem_if_raddr_i = fv_pk_mem_if.raddr_i;
    fv_pk_mem_if.rdata_o = pi_pk_mem_if_rdata_o;
  end


  abr_ctrl abr_ctrl_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize),

  .sk_bank0_mem_if(fv_sk_bank0_mem_if.req),
  .sk_bank1_mem_if(fv_sk_bank1_mem_if.req),
  .sig_z_mem_if(fv_sig_z_mem_if.req),
  .pk_mem_if(fv_pk_mem_if.req),

`ifdef RV_FPGA_SCA
  .NTT_trigger(NTT_trigger),
  .PWM_trigger(PWM_trigger),
  .PWA_trigger(PWA_trigger),
  .INTT_trigger(INTT_trigger),
`endif

`ifdef CALIPTRA
  .kv_read(kv_read),
  .kv_rd_resp(kv_rd_resp),
  .pcr_signing_data(pcr_signing_data),
`endif

  //control interface
  .abr_reg_hwif_in_o(abr_reg_hwif_in_o),
  .abr_reg_hwif_out_i(abr_reg_hwif_out_i),

  //sampler interface
  .sampler_mode_o(sampler_mode_o),
  .sha3_start_o(sha3_start_o), //start the sha3 engine
  .msg_start_o(msg_start_o), //start a new message
  .msg_valid_o(msg_valid_o), //msg interface valid
  .msg_rdy_i(msg_rdy_i),  //msg interface rdy (~hold)
  .msg_strobe_o(msg_strobe_o), //msg byte enables
  .msg_data_o(msg_data_o),

  .sampler_start_o(sampler_start_o),
  .dest_base_addr_o(dest_base_addr_o),

  .sampler_state_dv_i(sampler_state_dv_i),
  .sampler_state_data_i(sampler_state_data_i),
  .sampler_busy_i(sampler_busy_i),

  //ntt interface
  .ntt_enable_o(ntt_enable_o),
  .ntt_mode_o(ntt_mode_o),
  .ntt_mem_base_addr_o(ntt_mem_base_addr_o),
  .pwo_mem_base_addr_o(pwo_mem_base_addr_o),
  .ntt_masking_en_o(ntt_masking_en_o),
  .ntt_shuffling_en_o(ntt_shuffling_en_o),
  .ntt_busy_i(ntt_busy_i),

  //aux interface
  .aux_src0_base_addr_o(aux_src0_base_addr_o),
  .aux_src1_base_addr_o(aux_src1_base_addr_o),
  .aux_dest_base_addr_o(aux_dest_base_addr_o),

  .power2round_enable_o(power2round_enable_o),
  .pwr2rnd_keymem_if_i(pwr2rnd_keymem_if_i),
  .pwr2rnd_wr_data_i(pwr2rnd_wr_data_i),
  .pk_t1_wren_i(pk_t1_wren_i),
  .pk_t1_wr_addr_i(pk_t1_wr_addr_i),
  .pk_t1_wrdata_i(pk_t1_wrdata_i),
  .power2round_done_i(power2round_done_i),
  
  .decompose_enable_o(decompose_enable_o),
  .decompose_mode_o(decompose_mode_o),
  .decompose_done_i(decompose_done_i),

  .skdecode_enable_o(skdecode_enable_o),
  .skdecode_keymem_if_i(skdecode_keymem_if_i),
  .skdecode_rd_data_o(skdecode_rd_data_o),
  .skdecode_done_i(skdecode_done_i),
  .skdecode_error_i(skdecode_error_i),

  .skencode_enable_o(skencode_enable_o),
  .skencode_keymem_if_i(skencode_keymem_if_i),
  .skencode_wr_data_i(skencode_wr_data_i),
  .skencode_done_i(skencode_done_i),

  .makehint_enable_o(makehint_enable_o),
  .makehint_invalid_i(makehint_invalid_i),
  .makehint_done_i(makehint_done_i),
  .makehint_reg_wren_i(makehint_reg_wren_i),
  .makehint_reg_wr_addr_i(makehint_reg_wr_addr_i),
  .makehint_reg_wrdata_i(makehint_reg_wrdata_i),

  .normcheck_enable_o(normcheck_enable_o),
  .normcheck_mode_o(normcheck_mode_o),
  .normcheck_invalid_i(normcheck_invalid_i),
  .normcheck_done_i(normcheck_done_i),

  .sigencode_enable_o(sigencode_enable_o),
  .sigencode_wr_req_i(sigencode_wr_req_i),
  .sigencode_wr_data_i(sigencode_wr_data_i),
  .sigencode_done_i(sigencode_done_i),

  .pkdecode_enable_o(pkdecode_enable_o),
  .pkdecode_rd_addr_i(pkdecode_rd_addr_i),
  .pkdecode_rd_data_o(pkdecode_rd_data_o),
  .pkdecode_done_i(pkdecode_done_i),

  .sigdecode_h_enable_o(sigdecode_h_enable_o),
  .signature_h_o(signature_h_o),
  .sigdecode_h_invalid_i(sigdecode_h_invalid_i),
  .sigdecode_h_done_i(sigdecode_h_done_i),

  .sigdecode_z_enable_o(sigdecode_z_enable_o),
  .sigdecode_z_rd_req_i(sigdecode_z_rd_req_i),
  .sigdecode_z_rd_data_o(sigdecode_z_rd_data_o),
  .sigdecode_z_done_i(sigdecode_z_done_i),

  .compress_enable_o(compress_enable_o),
  .compress_mode_o(compress_mode_o),
  .compress_num_poly_o(compress_num_poly_o),
  .compress_compare_mode_o(compress_compare_mode_o),
  .compress_done_i(compress_done_i),
  .compress_compare_failed_i(compress_compare_failed_i),
  .compress_api_rw_en_i(compress_api_rw_en_i),
  .compress_api_rw_addr_i(compress_api_rw_addr_i),
  .compress_api_wr_data_i(compress_api_wr_data_i),
  .compress_api_rd_data_o(compress_api_rd_data_o),

  .decompress_enable_o(decompress_enable_o),
  .decompress_mode_o(decompress_mode_o),
  .decompress_num_poly_o(decompress_num_poly_o),
  .decompress_done_i(decompress_done_i),
  .decompress_api_rd_en_i(decompress_api_rd_en_i),
  .decompress_api_rd_addr_i(decompress_api_rd_addr_i),
  .decompress_api_rd_data_o(decompress_api_rd_data_o),

  .lfsr_enable_o(lfsr_enable_o),
  .lfsr_seed_o(lfsr_seed_o),

  .busy_o(busy_o),
  .zeroize_mem_o(zeroize_mem_o),

  .error_intr(error_intr),
  .notif_intr(notif_intr),
  .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
);

endmodule