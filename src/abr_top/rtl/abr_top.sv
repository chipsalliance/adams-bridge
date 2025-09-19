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

//Initial top level module
`include "abr_config_defines.svh"
`include "abr_prim_assert.sv"

module abr_top
  import abr_prim_alert_pkg::*;
  import abr_reg_pkg::*;
  import abr_params_pkg::*;
  import abr_ctrl_pkg::*;
  import abr_sampler_pkg::*;
  import abr_sha3_pkg::*;
  import ntt_defines_pkg::*;
  import decompose_defines_pkg::*;
  import compress_defines_pkg::*;
  import decompress_defines_pkg::*;
  `ifdef CALIPTRA
  import kv_defines_pkg::*; 
  `endif
  #(
  //top level params
    parameter AHB_ADDR_WIDTH = 32,
    parameter AHB_DATA_WIDTH = 64,
    parameter CLIENT_DATA_WIDTH = 32
  )
  (
  input logic clk,
  input logic rst_b,

`ifdef RV_FPGA_SCA
  output wire NTT_trigger,
  output wire PWM_trigger,
  output wire PWA_trigger,
  output wire INTT_trigger,
`endif


  //ahb input
  input logic  [AHB_ADDR_WIDTH-1:0] haddr_i,
  input logic  [AHB_DATA_WIDTH-1:0] hwdata_i,
  input logic                       hsel_i,
  input logic                       hwrite_i,
  input logic                       hready_i,
  input logic  [1:0]                htrans_i,
  input logic  [2:0]                hsize_i,

  //ahb output
  output logic                      hresp_o,
  output logic                      hreadyout_o,
  output logic [AHB_DATA_WIDTH-1:0] hrdata_o,

  abr_mem_if.req                  abr_memory_export,

  `ifdef CALIPTRA
  // KV interface
  output kv_read_t [2:0] kv_read,
  input kv_rd_resp_t [2:0] kv_rd_resp,
  output kv_write_t kv_write,
  input kv_wr_resp_t kv_wr_resp,
  //PCR Signing
  input pcr_signing_t pcr_signing_data,
  input logic ocp_lock_in_progress,
  `endif
  //Zeroize the engine if entering debug or scan mode
  input logic debugUnlock_or_scan_mode_switch,

  output logic                      busy_o,

  output logic                      error_intr,
  output logic                      notif_intr


  );

  localparam DATA_WIDTH = 32;

//Signal Declarations
  logic zeroize_reg;

  abr_sampler_mode_e         sampler_mode;
  logic                      sha3_start;
  logic                      msg_start;
  logic                      msg_valid;
  logic                      msg_rdy;
  logic [MsgStrbW-1:0]       msg_strobe;
  logic [MsgWidth-1:0]       msg_data[Sha3Share];
  logic                      sampler_start;
  logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr;

  logic                        sampler_busy;
  logic                        sampler_state_dv;
  logic [abr_sha3_pkg::StateW-1:0] sampler_state_data[Sha3Share];

  logic sampler_mem_dv;
  logic [ABR_MEM_DATA_WIDTH-1:0] sampler_mem_data;
  logic [ABR_MEM_ADDR_WIDTH-1:0] sampler_mem_addr;

  logic [1:0] sampler_ntt_dv, sampler_ntt_dv_f;
  logic [ABR_NUM_NTT-1:0]                    sampler_ntt_mode;
  logic [ABR_NUM_NTT-1:0]                    sampler_valid;
  logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_ntt_data;

  abr_ntt_mode_e [ABR_NUM_NTT-1:0] ntt_mode;
  mode_t [ABR_NUM_NTT-1:0] mode;
  logic [ABR_NUM_NTT-1:0] accumulate;
  logic [ABR_NUM_NTT-1:0] ntt_enable;
  logic [ABR_NUM_NTT-1:0] mlkem_mode;
  ntt_mem_addr_t [ABR_NUM_NTT-1:0] ntt_mem_base_addr;
  pwo_mem_addr_t [ABR_NUM_NTT-1:0] pwo_mem_base_addr;
  mem_if_t [ABR_NUM_NTT-1:0] ntt_mem_wr_req;
  logic [3:0][ABR_MEM_ADDR_WIDTH-1:0] ntt_mem_wr_req_mux;
  mem_if_t [ABR_NUM_NTT-1:0] ntt_mem_rd_req;
  logic [3:0][ABR_MEM_ADDR_WIDTH-1:0] ntt_mem_rd_req_mux;
  logic [ABR_NUM_NTT-1:0][ABR_MEM_MASKED_DATA_WIDTH-1:0] ntt_mem_wr_data;
  logic [2:0][ABR_MEM_DATA_WIDTH-1:0] ntt_mem_wr_data_mux;
  logic [ABR_NUM_NTT-1:0][ABR_MEM_MASKED_DATA_WIDTH-1:0] ntt_mem_rd_data;
  mem_if_t [ABR_NUM_NTT-1:0] pwm_a_rd_req;
  logic [3:0][ABR_MEM_ADDR_WIDTH-1:0] pwm_a_rd_req_mux;
  mem_if_t [ABR_NUM_NTT-1:0] pwm_b_rd_req;
  logic [3:0][ABR_MEM_ADDR_WIDTH-1:0] pwm_b_rd_req_mux;
  logic [ABR_NUM_NTT-1:0][ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_a_rd_data;
  logic [ABR_NUM_NTT-1:0][ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_b_rd_data;
  logic [ABR_NUM_NTT-1:0] ntt_busy;
  logic [ABR_NUM_NTT-1:0] ntt_random_en;
  logic [ABR_NUM_NTT-1:0] ntt_shuffling_en;
  logic [ABR_NUM_NTT-1:0] ntt_masking_en;

  mem_if_t w1_mem_wr_req;
  logic [ABR_MEM_W1_DATA_W-1:0] w1_mem_wr_data;
  mem_if_t w1_mem_rd_req;
  logic [ABR_MEM_W1_DATA_W-1:0] w1_mem_rd_data;

  logic decomp_msg_valid;
  logic [MsgWidth-1:0] decomp_msg_data[Sha3Share];

  logic [ABR_MEM_ADDR_WIDTH-1:0] aux_src0_base_addr;
  logic [ABR_MEM_ADDR_WIDTH-1:0] aux_src1_base_addr;
  logic [ABR_MEM_ADDR_WIDTH-1:0] aux_dest_base_addr;

  logic power2round_enable, power2round_done;
  mem_if_t [1:0] pwr2rnd_mem_rd_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] pwr2rnd_mem_rd_data;
  mem_if_t [1:0] pwr2rnd_keymem_if;
  logic [1:0] [DATA_WIDTH-1:0] pwr2rnd_wr_data;
  logic pk_t1_wren;
  logic [7:0][T1_COEFF_W-1:0] pk_t1_wrdata;
  logic [7:0] pk_t1_wr_addr;

  logic decompose_enable, decompose_done;
  mem_if_t decomp_mem_wr_req;
  mem_if_t [1:0] decomp_mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] decomp_mem_wr_data;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] decomp_mem_rd_data;
  logic decompose_mode;

  logic skencode_enable, skencode_done;
  mem_if_t skencode_keymem_if;
  logic [DATA_WIDTH-1:0] skencode_wr_data;
  mem_if_t [1:0] skencode_mem_rd_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] skencode_mem_rd_data;

  logic skdecode_enable, skdecode_done;
  mem_if_t [1:0] skdecode_keymem_if;
  logic [1:0][DATA_WIDTH-1:0] skdecode_rd_data;
  mem_if_t [1:0] skdecode_mem_wr_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] skdecode_mem_wr_data;
  logic skdecode_error;

  logic makehint_enable, makehint_done;
  logic makehint_invalid;
  mem_if_t makehint_mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] makehint_mem_rd_data;
  logic makehint_reg_wren;
  logic [3:0][7:0] makehint_reg_wrdata;
  logic [ABR_MEM_ADDR_WIDTH-1:0] makehint_reg_wr_addr;

  logic normcheck_enable;
  logic normcheck_done;
  logic [1:0] normcheck_mode;
  logic normcheck_invalid;
  mem_if_t normcheck_mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] normcheck_mem_rd_data;

  logic compress_enable;
  logic compress_done;
  logic compress_compare_failed;
  compress_mode_t compress_mode;
  logic compress_compare_mode;
  logic [2:0] compress_num_poly;
  mem_if_t compress_mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] compress_mem_rd_data;
  logic [1:0] compress_api_rw_en;
  logic [ABR_MEM_ADDR_WIDTH-1:0] compress_api_rw_addr;
  logic [DATA_WIDTH-1:0] compress_api_wr_data;
  logic [DATA_WIDTH-1:0] compress_api_rd_data;

  logic decompress_enable;
  logic decompress_done;
  decompress_mode_t decompress_mode;
  logic [2:0] decompress_num_poly;
  mem_if_t decompress_mem_wr_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] decompress_mem_wr_data;
  logic decompress_api_rd_en;
  logic [ABR_MEM_ADDR_WIDTH-1:0] decompress_api_rd_addr;
  logic [1:0][DATA_WIDTH-1:0] decompress_api_rd_data;

  logic sigencode_enable, sigencode_done;
  mem_if_t [1:0] sigencode_mem_rd_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] sigencode_mem_rd_data;
  mem_if_t sigencode_mem_wr_req;
  logic [1:0][3:0][19:0] sigencode_mem_wr_data;

  logic pkdecode_enable, pkdecode_done;
  mem_if_t [1:0] pkdecode_mem_wr_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] pkdecode_mem_wr_data;
  logic [7:0] pkdecode_rd_addr;
  logic [7:0][T1_COEFF_W-1:0] pkdecode_rd_data;

  logic sigdecode_z_enable, sigdecode_z_done;
  mem_if_t [1:0] sigdecode_z_mem_wr_req;
  logic [1:0][ABR_MEM_DATA_WIDTH-1:0] sigdecode_z_mem_wr_data;
  mem_if_t sigdecode_z_mem_rd_req;
  logic [1:0][3:0][19:0] sigdecode_z_mem_rd_data;

  logic sigdecode_h_enable, sigdecode_h_done;
  logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] signature_h;
  logic sigdecode_h_invalid;
  mem_if_t sigdecode_h_mem_wr_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] sigdecode_h_mem_wr_data;

  mem_if_t                       sib_mem_rd_req;
  logic [ABR_MEM_DATA_WIDTH-1:0] sib_mem_rd_data;

  logic lfsr_enable;
  logic [1:0][LFSR_W-1:0] lfsr_seed;
  logic [RND_W-1:0] rand_bits;
  logic [RND_W-7:0] ntt_rand_bits;

  //gasket to assemble reg requests
  logic abr_reg_dv;
  logic abr_reg_hold;
  logic abr_reg_rd_ack, abr_reg_wr_ack;
  logic [CLIENT_DATA_WIDTH-1:0] abr_reg_rdata;
  logic [AHB_ADDR_WIDTH-1:0]    abr_reg_addr;
  logic [CLIENT_DATA_WIDTH-1:0] abr_reg_wdata;
  logic                         abr_reg_write;

  logic abr_reg_err, abr_reg_read_err, abr_reg_write_err;

  abr_reg__in_t abr_reg_hwif_in;
  abr_reg__out_t abr_reg_hwif_out;

  mem_if_t zeroize_mem;
  logic zeroize_mem_we;
  logic zeroize_mem_re;
  logic [ABR_MEM_ADDR_WIDTH-1:0] zeroize_mem_addr;
  
  //memory interfaces
  abr_sram_if #(.ADDR_W(SK_MEM_BANK_ADDR_W), .DATA_W(SK_MEM_BANK_DATA_W)) sk_bank0_mem_if();
  abr_sram_if #(.ADDR_W(SK_MEM_BANK_ADDR_W), .DATA_W(SK_MEM_BANK_DATA_W)) sk_bank1_mem_if();
  abr_sram_be_if #(.ADDR_W(SIG_Z_MEM_ADDR_W), .DATA_W(SIG_Z_MEM_DATA_W)) sig_z_mem_if();
  abr_sram_be_if #(.ADDR_W(PK_MEM_ADDR_W), .DATA_W(PK_MEM_DATA_W)) pk_mem_if();

  `ifdef MLDSA_MASKING
    assign ntt_rand_bits = rand_bits[RND_W-1:6];
  `else
    assign ntt_rand_bits = (RND_W-6)'(0);
  `endif

  abr_ahb_slv_sif #(
    .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
    .AHB_DATA_WIDTH(AHB_DATA_WIDTH),
    .CLIENT_DATA_WIDTH(CLIENT_DATA_WIDTH)
)
  mldsa_ahb_slv_inst (
    //AMBA AHB Lite INF
    .hclk(clk),
    .hreset_n(rst_b),
    .haddr_i(haddr_i),
    .hwdata_i(hwdata_i),
    .hsel_i(hsel_i),
    .hwrite_i(hwrite_i),
    .hready_i(hready_i),
    .htrans_i(htrans_i),
    .hsize_i(hsize_i),

    .hresp_o(hresp_o),
    .hreadyout_o(hreadyout_o),
    .hrdata_o(hrdata_o),

    //COMPONENT INF
    .dv(abr_reg_dv),
    .hld(abr_reg_hold),
    .err(abr_reg_err),
    .write(abr_reg_write),
    .wdata(abr_reg_wdata),
    .addr(abr_reg_addr[AHB_ADDR_WIDTH-1:0]),

    .rdata(abr_reg_rdata)
);

always_comb abr_reg_err = (abr_reg_rd_ack & abr_reg_read_err) | (abr_reg_wr_ack & abr_reg_write_err);
always_comb abr_reg_hold = abr_reg_dv & ~(abr_reg_rd_ack | abr_reg_wr_ack);

abr_reg abr_reg_inst (
  .clk(clk),
  .rst(rst_b),

  .s_cpuif_req(abr_reg_dv),
  .s_cpuif_req_is_wr(abr_reg_write),
  .s_cpuif_addr(abr_reg_addr[ABR_REG_ADDR_WIDTH-1:0]),
  .s_cpuif_wr_data(abr_reg_wdata),
  .s_cpuif_wr_biten('1),
  .s_cpuif_req_stall_wr(),
  .s_cpuif_req_stall_rd(),
  .s_cpuif_rd_ack(abr_reg_rd_ack),
  .s_cpuif_rd_err(abr_reg_read_err),
  .s_cpuif_rd_data(abr_reg_rdata),
  .s_cpuif_wr_ack(abr_reg_wr_ack),
  .s_cpuif_wr_err(abr_reg_write_err),

  .hwif_in(abr_reg_hwif_in),
  .hwif_out(abr_reg_hwif_out)
);

abr_ctrl abr_ctrl_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

  .sk_bank0_mem_if(sk_bank0_mem_if.req),
  .sk_bank1_mem_if(sk_bank1_mem_if.req),
  .sig_z_mem_if(sig_z_mem_if.req),
  .pk_mem_if(pk_mem_if.req),

`ifdef RV_FPGA_SCA
  .NTT_trigger(NTT_trigger),
  .PWM_trigger(PWM_trigger),
  .PWA_trigger(PWA_trigger),
  .INTT_trigger(INTT_trigger),
`endif

`ifdef CALIPTRA
  .kv_read(kv_read),
  .kv_rd_resp(kv_rd_resp),
  .kv_write(kv_write),
  .kv_wr_resp(kv_wr_resp),
  .pcr_signing_data(pcr_signing_data),
  .ocp_lock_in_progress(ocp_lock_in_progress),
`endif

  //control interface
  .abr_reg_hwif_in_o(abr_reg_hwif_in),
  .abr_reg_hwif_out_i(abr_reg_hwif_out),

  //sampler interface
  .sampler_mode_o(sampler_mode),
  .sha3_start_o(sha3_start), //start the sha3 engine
  .msg_start_o(msg_start), //start a new message
  .msg_valid_o(msg_valid), //msg interface valid
  .msg_rdy_i(msg_rdy),  //msg interface rdy (~hold)
  .msg_strobe_o(msg_strobe), //msg byte enables
  .msg_data_o(msg_data),

  .sampler_start_o(sampler_start),
  .dest_base_addr_o(dest_base_addr),

  .sampler_state_dv_i(sampler_state_dv),
  .sampler_state_data_i(sampler_state_data),
  .sampler_busy_i(sampler_busy),

  //ntt interface
  .ntt_enable_o(ntt_enable),
  .ntt_mode_o(ntt_mode),
  .ntt_mem_base_addr_o(ntt_mem_base_addr),
  .pwo_mem_base_addr_o(pwo_mem_base_addr),
  .ntt_masking_en_o(ntt_masking_en),
  .ntt_shuffling_en_o(ntt_shuffling_en),
  .ntt_busy_i(ntt_busy),

  //aux interface
  .aux_src0_base_addr_o(aux_src0_base_addr),
  .aux_src1_base_addr_o(aux_src1_base_addr),
  .aux_dest_base_addr_o(aux_dest_base_addr),

  .power2round_enable_o(power2round_enable),
  .pwr2rnd_keymem_if_i(pwr2rnd_keymem_if),
  .pwr2rnd_wr_data_i(pwr2rnd_wr_data),
  .pk_t1_wren_i(pk_t1_wren),
  .pk_t1_wr_addr_i(pk_t1_wr_addr),
  .pk_t1_wrdata_i(pk_t1_wrdata),
  .power2round_done_i(power2round_done),
  
  .decompose_enable_o(decompose_enable),
  .decompose_mode_o(decompose_mode),
  .decompose_done_i(decompose_done),

  .skdecode_enable_o(skdecode_enable),
  .skdecode_keymem_if_i(skdecode_keymem_if),
  .skdecode_rd_data_o(skdecode_rd_data),
  .skdecode_done_i(skdecode_done),
  .skdecode_error_i(skdecode_error),

  .skencode_enable_o(skencode_enable),
  .skencode_keymem_if_i(skencode_keymem_if),
  .skencode_wr_data_i(skencode_wr_data),
  .skencode_done_i(skencode_done),

  .makehint_enable_o(makehint_enable),
  .makehint_invalid_i(makehint_invalid),
  .makehint_done_i(makehint_done),
  .makehint_reg_wren_i(makehint_reg_wren),
  .makehint_reg_wr_addr_i(makehint_reg_wr_addr),
  .makehint_reg_wrdata_i(makehint_reg_wrdata),

  .normcheck_enable_o(normcheck_enable),
  .normcheck_mode_o(normcheck_mode),
  .normcheck_invalid_i(normcheck_invalid),
  .normcheck_done_i(normcheck_done),

  .sigencode_enable_o(sigencode_enable),
  .sigencode_wr_req_i(sigencode_mem_wr_req),
  .sigencode_wr_data_i(sigencode_mem_wr_data),
  .sigencode_done_i(sigencode_done),

  .pkdecode_enable_o(pkdecode_enable),
  .pkdecode_rd_addr_i(pkdecode_rd_addr),
  .pkdecode_rd_data_o(pkdecode_rd_data),
  .pkdecode_done_i(pkdecode_done),

  .sigdecode_h_enable_o(sigdecode_h_enable),
  .signature_h_o(signature_h),
  .sigdecode_h_invalid_i(sigdecode_h_invalid),
  .sigdecode_h_done_i(sigdecode_h_done),

  .sigdecode_z_enable_o(sigdecode_z_enable),
  .sigdecode_z_rd_req_i(sigdecode_z_mem_rd_req),
  .sigdecode_z_rd_data_o(sigdecode_z_mem_rd_data),
  .sigdecode_z_done_i(sigdecode_z_done),

  .compress_enable_o(compress_enable),
  .compress_mode_o(compress_mode),
  .compress_num_poly_o(compress_num_poly),
  .compress_compare_mode_o(compress_compare_mode),
  .compress_done_i(compress_done),
  .compress_compare_failed_i(compress_compare_failed),
  .compress_api_rw_en_i(compress_api_rw_en),
  .compress_api_rw_addr_i(compress_api_rw_addr),
  .compress_api_wr_data_i(compress_api_wr_data),
  .compress_api_rd_data_o(compress_api_rd_data),

  .decompress_enable_o(decompress_enable),
  .decompress_mode_o(decompress_mode),
  .decompress_num_poly_o(decompress_num_poly),
  .decompress_done_i(decompress_done),
  .decompress_api_rd_en_i(decompress_api_rd_en),
  .decompress_api_rd_addr_i(decompress_api_rd_addr),
  .decompress_api_rd_data_o(decompress_api_rd_data),

  .lfsr_enable_o(lfsr_enable),
  .lfsr_seed_o(lfsr_seed),

  .busy_o(busy_o),
  .zeroize_mem_o(zeroize_mem),

  .error_intr(error_intr),
  .notif_intr(notif_intr),
  .debugUnlock_or_scan_mode_switch(debugUnlock_or_scan_mode_switch)
);

always_comb zeroize_mem_we = (zeroize_mem.rd_wr_en == RW_WRITE);
//read pulse to clear flopped output after first entry has been zeroized
always_comb zeroize_mem_re = (zeroize_mem_we) && (zeroize_mem.addr == 'd1);
always_comb zeroize_mem_addr = zeroize_mem.addr;

logic [MsgWidth-1:0] msg_data_i[Sha3Share];
assign msg_data_i = decomp_msg_valid ? decomp_msg_data : msg_data;

abr_sampler_top sampler_top_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

  .sampler_mode_i(sampler_mode),
  .sha3_start_i(sha3_start), //start the sha3 engine
  .msg_start_i(msg_start), //start a new message
  .msg_valid_i(msg_valid | decomp_msg_valid),
  .msg_rdy_o(msg_rdy), 
  .msg_strobe_i(decomp_msg_valid ? '1 : msg_strobe),
  .msg_data_i(msg_data_i), 

  .sib_mem_rd_req_i(sib_mem_rd_req),
  .sib_mem_rd_data_o(sib_mem_rd_data),

  .sampler_start_i(sampler_start),
  .dest_base_addr_i(dest_base_addr),

  .sampler_busy_o(sampler_busy),

  .sampler_ntt_dv_o(sampler_ntt_dv[0]),
  .sampler_ntt_data_o(sampler_ntt_data),

  .sampler_mem_dv_o(sampler_mem_dv),
  .sampler_mem_data_o(sampler_mem_data),
  .sampler_mem_addr_o(sampler_mem_addr),

  .sampler_state_dv_o(sampler_state_dv),
  .sampler_state_data_o(sampler_state_data)
);

//no sampler connect for ntt 1 if present
assign sampler_ntt_dv[1] = 0;

always_ff @(posedge clk or negedge rst_b) begin
  if (!rst_b) begin
    sampler_ntt_dv_f <= 0;
  end
  else if (zeroize_reg) begin
    sampler_ntt_dv_f <= 0;
  end
  else begin
    sampler_ntt_dv_f <= sampler_ntt_dv;
  end
end

generate
  for (genvar g_inst = 0; g_inst < ABR_NUM_NTT; g_inst++) begin : ntt_gen
    //NTT
    //gasket here, create common interfaces?
    always_comb begin
      mode[g_inst] = '0;
      accumulate[g_inst] = '0;
      sampler_valid[g_inst] = 0;
      sampler_ntt_mode[g_inst] = 0;
      ntt_random_en[g_inst] = 0; //Turn off random in NTT for all ops except PWM, INTT
      mlkem_mode[g_inst] = 0;

      unique case (ntt_mode[g_inst]) inside
        ABR_NTT_NONE: begin
        end
        MLDSA_NTT: begin
          mode[g_inst] = ct;
        end
        MLDSA_INTT: begin
          mode[g_inst] = gs;
          ntt_random_en[g_inst] = 1;
        end
        MLDSA_PWM_SMPL: begin
          mode[g_inst] = pwm;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
          sampler_ntt_mode[g_inst] = 1;
        end
        MLDSA_PWM_ACCUM_SMPL: begin
          mode[g_inst] = pwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
          sampler_ntt_mode[g_inst] = 1;
        end
        MLDSA_PWM: begin
          mode[g_inst] = pwm;
          sampler_valid[g_inst] = 1;
          ntt_random_en[g_inst] = 1;
        end
        MLDSA_PWM_ACCUM: begin
          mode[g_inst] = pwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = 1;
          ntt_random_en[g_inst] = 1;
        end
        MLDSA_PWA: begin
          mode[g_inst] = pwa;
          sampler_valid[g_inst] = 1;
        end
        MLDSA_PWS: begin
          mode[g_inst] = pws;
          sampler_valid[g_inst] = 1;
        end
        MLKEM_NTT: begin
          mode[g_inst] = ct;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_INTT: begin
          mode[g_inst] = gs;
          ntt_random_en[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWM_SMPL: begin
          mode[g_inst] = pairwm;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
          sampler_ntt_mode[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWM_ACCUM_SMPL: begin
          mode[g_inst] = pairwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = sampler_ntt_dv[g_inst];
          sampler_ntt_mode[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWM: begin
          mode[g_inst] = pairwm;
          sampler_valid[g_inst] = 1;
          ntt_random_en[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWM_ACCUM: begin
          mode[g_inst] = pairwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = 1;
          ntt_random_en[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWA: begin
          mode[g_inst] = pwa;
          sampler_valid[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        MLKEM_PWS: begin
          mode[g_inst] = pws;
          sampler_valid[g_inst] = 1;
          mlkem_mode[g_inst] = 1;
        end
        default: begin
        end
      endcase
      
      
    end

  ntt_top #(
    .REG_SIZE(REG_SIZE),
    .MLDSA_Q(MLDSA_Q),
    .MLDSA_N(MLDSA_N),
    .MEM_ADDR_WIDTH(ABR_MEM_ADDR_WIDTH)
  )
  ntt_top_inst (
    .clk(clk),
    .reset_n(rst_b),
    .zeroize(zeroize_reg),

    .mode(mode[g_inst]),
    .ntt_enable(ntt_enable[g_inst]),
    .mlkem(mlkem_mode[g_inst]),
    .ntt_mem_base_addr(ntt_mem_base_addr[g_inst]),
    .pwo_mem_base_addr(pwo_mem_base_addr[g_inst]),
    .accumulate(accumulate[g_inst]),
    .sampler_valid(sampler_valid[g_inst]),
    .shuffle_en(ntt_shuffling_en[g_inst]),
    .random(rand_bits[5:0]),
    .masking_en(ntt_masking_en[g_inst]),
    .rnd_i(ntt_random_en[g_inst] ? ntt_rand_bits : (RND_W-6)'(0)), //(ntt_rand_bits & {(RND_W-6){ntt_random_en[g_inst]}}),
    //NTT mem IF
    .mem_wr_req(ntt_mem_wr_req[g_inst]),
    .mem_rd_req(ntt_mem_rd_req[g_inst]),
    .mem_wr_data(ntt_mem_wr_data[g_inst]),
    .mem_rd_data(ntt_mem_rd_data[g_inst]),
    //PWM mem IF
    .pwm_a_rd_req(pwm_a_rd_req[g_inst]),
    .pwm_b_rd_req(pwm_b_rd_req[g_inst]),
    .pwm_a_rd_data(pwm_a_rd_data[g_inst]),
    .pwm_b_rd_data(sampler_ntt_mode[g_inst] ? ABR_MEM_MASKED_DATA_WIDTH'(sampler_ntt_data) : pwm_b_rd_data[g_inst]),
    .ntt_busy(ntt_busy[g_inst]),
    .ntt_done()
  );
  end
endgenerate

//aux functions
power2round_top
power2round_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .enable(power2round_enable),
  .done(power2round_done),

  .src_base_addr(aux_src0_base_addr),
  .mem_a_rd_req(pwr2rnd_mem_rd_req[0]),
  .mem_rd_data_a(pwr2rnd_mem_rd_data[0]),
  .mem_b_rd_req(pwr2rnd_mem_rd_req[1]),
  .mem_rd_data_b(pwr2rnd_mem_rd_data[1]),

  .pk_t1_wren(pk_t1_wren),
  .pk_t1_wr_addr(pk_t1_wr_addr),
  .pk_t1_wrdata(pk_t1_wrdata),

  .skmem_dest_base_addr(aux_dest_base_addr),
  .skmem_a_wr_req(pwr2rnd_keymem_if[0]),
  .skmem_wr_data_a(pwr2rnd_wr_data[0]),
  .skmem_b_wr_req(pwr2rnd_keymem_if[1]),
  .skmem_wr_data_b(pwr2rnd_wr_data[1])
);

decompose
decompose_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .decompose_enable(decompose_enable),
  .dcmp_mode(decompose_mode),
  .src_base_addr(aux_src0_base_addr),
  .dest_base_addr(aux_dest_base_addr),
  .hint_src_base_addr(aux_src1_base_addr),

  //Output to memory - r0
  .mem_rd_req(decomp_mem_rd_req[0]),
  .mem_wr_req(decomp_mem_wr_req),
  .mem_rd_data(decomp_mem_rd_data[0]),
  .mem_wr_data(decomp_mem_wr_data),

  //Output to memory - h (sigDecode)
  .mem_hint_rd_req(decomp_mem_rd_req[1]),
  .mem_hint_rd_data(decomp_mem_rd_data[1]),

  //Output to z mem - z != 0
  .z_mem_wr_req(w1_mem_wr_req),
  .z_neq_z(w1_mem_wr_data),

  //Output of w1_encode - r1
  .w1_o(decomp_msg_data[0]),
  .buffer_en(decomp_msg_valid),

  .decompose_done(decompose_done)
);

skencode
#(
  .MEM_ADDR_WIDTH(ABR_MEM_ADDR_WIDTH)
)
skencode_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .src_base_addr(aux_src0_base_addr),
  .dest_base_addr(aux_dest_base_addr),

  .skencode_enable(skencode_enable),
  .skencode_done(skencode_done),

  .keymem_a_wr_req(skencode_keymem_if),
  .keymem_a_wr_data(skencode_wr_data),
  .mem_a_rd_req(skencode_mem_rd_req[0]),
  .mem_a_rd_data(skencode_mem_rd_data[0]),
  .mem_b_rd_req(skencode_mem_rd_req[1]),
  .mem_b_rd_data(skencode_mem_rd_data[1])
);

skdecode_top
skdecode_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .skdecode_enable(skdecode_enable),
  .skdecode_done(skdecode_done),

  .keymem_src_base_addr(aux_src0_base_addr), 
  .dest_base_addr(aux_dest_base_addr),

  .keymem_a_rd_req(skdecode_keymem_if[0]),
  .keymem_a_rd_data(skdecode_rd_data[0]),
  .keymem_b_rd_req(skdecode_keymem_if[1]),
  .keymem_b_rd_data(skdecode_rd_data[1]),

  .mem_a_wr_req(skdecode_mem_wr_req[0]),
  .mem_a_wr_data(skdecode_mem_wr_data[0]),
  .mem_b_wr_req(skdecode_mem_wr_req[1]),
  .mem_b_wr_data(skdecode_mem_wr_data[1]),

  .s1_done(),
  .s2_done(),
  .t0_done(),
  .skdecode_error(skdecode_error)
);

makehint
makehint_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .makehint_enable(makehint_enable),
  .makehint_done(makehint_done),

  .mem_base_addr(aux_src0_base_addr),

  .mem_rd_req(makehint_mem_rd_req),
  .r(makehint_mem_rd_data),

  .reg_wren(makehint_reg_wren),
  .reg_wr_addr(makehint_reg_wr_addr),
  .reg_wrdata(makehint_reg_wrdata),

  .z_rd_req(w1_mem_rd_req),
  .z(w1_mem_rd_data),

  .invalid_h(makehint_invalid)
);

norm_check_top
norm_check_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .mode(normcheck_mode),
  .norm_check_enable(normcheck_enable),

  .randomness(rand_bits[5:0]),

  .norm_check_ready(),
  .norm_check_done(normcheck_done),
  
  .mem_base_addr(aux_src0_base_addr),
  .mem_rd_req(normcheck_mem_rd_req),
  .mem_rd_data(normcheck_mem_rd_data),

  .invalid(normcheck_invalid)

);

sigencode_z_top
sigencode_z_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),
  
  .sigencode_z_enable(sigencode_enable),
  .sigencode_z_done(sigencode_done),

  .src_base_addr(aux_src0_base_addr),
  .sigmem_dest_base_addr(aux_dest_base_addr),

  .mem_a_rd_req(sigencode_mem_rd_req[0]),
  .mem_a_rd_data(sigencode_mem_rd_data[0]),
  .mem_b_rd_req(sigencode_mem_rd_req[1]),
  .mem_b_rd_data(sigencode_mem_rd_data[1]),
  
  .sigmem_a_wr_req(sigencode_mem_wr_req),
  .sigmem_a_wr_data(sigencode_mem_wr_data[0]),
  .sigmem_b_wr_req(),
  .sigmem_b_wr_data(sigencode_mem_wr_data[1])
);

pkdecode 
#(
  .API_ADDR_WIDTH(8)
)
pkdecode_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .pkdecode_enable(pkdecode_enable),
  .pkdecode_done(pkdecode_done),

  .dest_base_addr(aux_dest_base_addr),

  .API_rd_address(pkdecode_rd_addr),
  .API_rd_data(pkdecode_rd_data),

  .mem_a_wr_req(pkdecode_mem_wr_req[0]),
  .mem_a_wr_data(pkdecode_mem_wr_data[0]),
  .mem_b_wr_req(pkdecode_mem_wr_req[1]),
  .mem_b_wr_data(pkdecode_mem_wr_data[1])
);

sigdecode_z_top
sigdecode_z_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .sigdecode_z_enable(sigdecode_z_enable),
  .sigdecode_z_done(sigdecode_z_done),

  .dest_base_addr(aux_dest_base_addr),

  .mem_a_wr_req(sigdecode_z_mem_wr_req[0]),
  .mem_a_wr_data(sigdecode_z_mem_wr_data[0]),
  .mem_b_wr_req(sigdecode_z_mem_wr_req[1]),
  .mem_b_wr_data(sigdecode_z_mem_wr_data[1]),

  .sigmem_a_rd_req(sigdecode_z_mem_rd_req),
  .sigmem_a_rd_data(sigdecode_z_mem_rd_data[0]),
  .sigmem_b_rd_req(),
  .sigmem_b_rd_data(sigdecode_z_mem_rd_data[1])
);

sigdecode_h
sigdecode_h_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .sigdecode_h_enable(sigdecode_h_enable),
  .sigdecode_h_done(sigdecode_h_done),

  .dest_base_addr(aux_dest_base_addr),

  .encoded_h_i(signature_h),
  .mem_wr_req(sigdecode_h_mem_wr_req),
  .mem_wr_data(sigdecode_h_mem_wr_data),

  .sigdecode_h_error(sigdecode_h_invalid)
);

compress_top
compress_top_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .mode(compress_mode),
  .compare_mode(compress_compare_mode),
  .num_poly(compress_num_poly),
  .src_base_addr(aux_src0_base_addr),
  .dest_base_addr(aux_dest_base_addr),

  .compress_enable(compress_enable),
  .compress_done(compress_done),
  .compare_failed(compress_compare_failed),

  .mem_rd_req(compress_mem_rd_req),
  .mem_rd_data(compress_mem_rd_data),

  .api_rw_en(compress_api_rw_en),
  .api_rw_addr(compress_api_rw_addr),
  .api_wr_data(compress_api_wr_data),
  .api_rd_data(compress_api_rd_data)
);

decompress_top
decompress_top_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .mode(decompress_mode),
  .num_poly(decompress_num_poly),
  .src_base_addr(aux_src0_base_addr),
  .dest_base_addr(aux_dest_base_addr),

  .decompress_enable(decompress_enable),
  .decompress_done(decompress_done),

  .mem_wr_req(decompress_mem_wr_req),
  .mem_wr_data(decompress_mem_wr_data),
  .api_rd_en(decompress_api_rd_en),
  .api_rd_addr(decompress_api_rd_addr),
  .api_rd_data(decompress_api_rd_data)
);

abr_prim_lfsr
#(
  .LfsrType("FIB_XNOR"),
  .LfsrDw(LFSR_W),
  .StateOutDw(LFSR_W)
) abr_prim_lfsr_inst0 
(
  .clk_i(clk),
  .rst_b(rst_b),
  .seed_en_i(lfsr_enable),
  .seed_i(lfsr_seed[0]),
  .lfsr_en_i(1'b1),
  .entropy_i('0),
  .state_o(rand_bits[LFSR_W-1:0])
);

abr_prim_lfsr
#(
  .LfsrType("FIB_XNOR"),
  .LfsrDw(LFSR_W),
  .StateOutDw(LFSR_W)
) abr_prim_lfsr_inst1 
(
  .clk_i(clk),
  .rst_b(rst_b),
  .seed_en_i(lfsr_enable),
  .seed_i(lfsr_seed[1]),
  .lfsr_en_i(1'b1),
  .entropy_i('0),
  .state_o(rand_bits[RND_W-1 : LFSR_W])
);

always_comb begin
  abr_memory_export.w1_mem_we_i = (w1_mem_wr_req.rd_wr_en == RW_WRITE) | zeroize_mem_we;
  abr_memory_export.w1_mem_waddr_i = (w1_mem_wr_req.addr[ABR_MEM_W1_ADDR_W-1:0]) | 
                                       ({ABR_MEM_W1_ADDR_W{zeroize_mem_we}} & zeroize_mem_addr[ABR_MEM_W1_ADDR_W-1:0]);
  abr_memory_export.w1_mem_wdata_i = zeroize_mem_we ? '0 : w1_mem_wr_data;
  abr_memory_export.w1_mem_re_i = w1_mem_rd_req.rd_wr_en == RW_READ;
  abr_memory_export.w1_mem_raddr_i = w1_mem_rd_req.addr[ABR_MEM_W1_ADDR_W-1:0];
  w1_mem_rd_data = abr_memory_export.w1_mem_rdata_o;
end

//Decode request to sample in ball memory
logic [ABR_NUM_NTT-1:0] sib_mem_re, sib_mem_re_f;
always_comb begin
  sib_mem_rd_req.addr = '0;
  for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
    sib_mem_re[ntt] = (ntt_mem_rd_req[ntt].rd_wr_en == RW_READ) & (ntt_mem_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == 3'b100);

    sib_mem_rd_req.addr |= {ABR_MEM_ADDR_WIDTH{sib_mem_re[ntt]}} & ntt_mem_rd_req[ntt].addr;
  end
  //if any request, set to read else idle
  sib_mem_rd_req.rd_wr_en = |sib_mem_re ? RW_READ : RW_IDLE;
end


//MUX memory accesses
logic [3:1] abr_mem_re;
logic [3:1][ABR_MEM_ADDR_WIDTH-4:0] abr_mem_raddr;
logic [2:1][ABR_MEM_DATA_WIDTH-1:0] abr_mem_rdata;
logic [3:3][ABR_MEM_MASKED_DATA_WIDTH-1:0] abr_mem_masked_rdata;
logic [1:0] abr_mem_re0_bank;
logic [1:0][ABR_MEM_ADDR_WIDTH-5:0] abr_mem_raddr0_bank;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem_rdata0_bank;
logic [3:1] abr_mem_we;
logic [3:1][ABR_MEM_ADDR_WIDTH-4:0] abr_mem_waddr;
logic [2:1][ABR_MEM_DATA_WIDTH-1:0] abr_mem_wdata;
logic [3:3][ABR_MEM_MASKED_DATA_WIDTH-1:0] abr_mem_masked_wdata;
logic [1:0] abr_mem_we0_bank;
logic [1:0][ABR_MEM_ADDR_WIDTH-5:0] abr_mem_waddr0_bank;
logic [1:0][ABR_MEM_DATA_WIDTH-1:0] abr_mem_wdata0_bank;

logic [3:1] sampler_mem_we;
logic [ABR_NUM_NTT-1:0][3:0] ntt_mem_we;
logic [3:0] ntt_mem_we_mux;
logic [1:0] ntt_mem_we0_bank;
logic [3:1] decomp_mem_we;
logic [1:0] sampler_mem_we0_bank;
logic [1:0] decomp_mem_we0_bank;
logic [1:0] skdecode_mem_we0_bank;
logic [1:0] pkdecode_mem_we0_bank;
logic [1:0] sigdecode_z_mem_we0_bank;
logic [3:1] sigdecode_h_mem_we;
logic [1:0] sigdecode_h_mem_we0_bank;
logic [1:0] decompress_mem_we0_bank;

logic [ABR_NUM_NTT-1:0][3:0] ntt_mem_re,ntt_mem_re_f;
logic [ABR_NUM_NTT-1:0][3:0] pwo_a_mem_re,pwo_a_mem_re_f;
logic [ABR_NUM_NTT-1:0][3:0] pwo_b_mem_re,pwo_b_mem_re_f;
logic [3:0] ntt_mem_re_mux;
logic [3:0] pwo_a_mem_re_mux;
logic [3:0] pwo_b_mem_re_mux;
logic [1:0][3:1] decomp_mem_re,decomp_mem_re_f;
logic [3:1] normcheck_mem_re,normcheck_mem_re_f;
logic [3:1] compress_mem_re,compress_mem_re_f;
logic [3:1] makehint_mem_re;
logic [ABR_NUM_NTT-1:0][1:0] ntt_mem_re0_bank,ntt_mem_re0_bank_f;
logic [ABR_NUM_NTT-1:0][1:0] pwo_a_mem_re0_bank,pwo_a_mem_re0_bank_f;
logic [ABR_NUM_NTT-1:0][1:0] pwo_b_mem_re0_bank,pwo_b_mem_re0_bank_f;
logic [1:0] ntt_mem_re0_bank_mux;
logic [1:0] pwo_a_mem_re0_bank_mux;
logic [1:0] pwo_b_mem_re0_bank_mux;
logic [1:0][1:0] decomp_mem_re0_bank,decomp_mem_re0_bank_f;
logic [1:0] normcheck_mem_re0_bank,normcheck_mem_re0_bank_f;
logic [1:0] compress_mem_re0_bank,compress_mem_re0_bank_f;
logic [1:0] skencode_mem_re0_bank;
logic [1:0] sigencode_mem_re0_bank;
logic [1:0] pwr2rnd_mem_re0_bank;

//NTT Muxes
always_comb begin
  ntt_mem_we_mux = '0;
  ntt_mem_re_mux = '0;
  pwo_a_mem_re_mux = '0;
  pwo_b_mem_re_mux = '0;
  ntt_mem_wr_req_mux  = '0;
  ntt_mem_wr_data_mux = '0;
  ntt_mem_rd_req_mux  = '0;
  pwm_a_rd_req_mux    = '0;
  pwm_b_rd_req_mux    = '0;
  for (int ntt= 0; ntt < ABR_NUM_NTT; ntt++) begin
    for (int i = 0; i < 4; i++) begin
      ntt_mem_we[ntt][i] = (ntt_mem_wr_req[ntt].rd_wr_en == RW_WRITE) & (ntt_mem_wr_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      ntt_mem_re[ntt][i] = (ntt_mem_rd_req[ntt].rd_wr_en == RW_READ) & (ntt_mem_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_a_mem_re[ntt][i] = (pwm_a_rd_req[ntt].rd_wr_en == RW_READ) & (pwm_a_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_b_mem_re[ntt][i] = (ntt_shuffling_en[ntt] ? ~sampler_ntt_dv_f[ntt] : ~sampler_ntt_dv[ntt]) & (pwm_b_rd_req[ntt].rd_wr_en == RW_READ) & (pwm_b_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);

      ntt_mem_we_mux[i] |= ntt_mem_we[ntt][i];
      ntt_mem_re_mux[i] |= ntt_mem_re[ntt][i];
      pwo_a_mem_re_mux[i] |= pwo_a_mem_re[ntt][i];
      pwo_b_mem_re_mux[i] |= pwo_b_mem_re[ntt][i];

      ntt_mem_wr_req_mux[i]  |= ({ABR_MEM_ADDR_WIDTH{ntt_mem_we[ntt][i]}}   & ntt_mem_wr_req[ntt].addr);
      ntt_mem_rd_req_mux[i]  |= ({ABR_MEM_ADDR_WIDTH{ntt_mem_re[ntt][i]}}   & ntt_mem_rd_req[ntt].addr);
      pwm_a_rd_req_mux[i]    |= ({ABR_MEM_ADDR_WIDTH{pwo_a_mem_re[ntt][i]}} & pwm_a_rd_req[ntt].addr);
      pwm_b_rd_req_mux[i]    |= ({ABR_MEM_ADDR_WIDTH{pwo_b_mem_re[ntt][i]}} & pwm_b_rd_req[ntt].addr);
    end

    for (int i = 0; i < 3; i++) begin
      ntt_mem_wr_data_mux[i] |= ({ABR_MEM_DATA_WIDTH{ntt_mem_we[ntt][i]}}   & ntt_mem_wr_data[ntt][ABR_MEM_DATA_WIDTH-1:0]);
    end
  end
end

//Write Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    if (i == 0) begin
      for (int bank = 0; bank < 2; bank++) begin
        ntt_mem_we0_bank[bank] = ntt_mem_we_mux[i] & (ntt_mem_wr_req_mux[i][0] == bank);
        sampler_mem_we0_bank[bank] = sampler_mem_dv & (sampler_mem_addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (sampler_mem_addr[0] == bank);
        decomp_mem_we0_bank[bank] = (decomp_mem_wr_req.rd_wr_en == RW_WRITE) & (decomp_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_wr_req.addr[0] == bank);
        sigdecode_h_mem_we0_bank[bank] = (sigdecode_h_mem_wr_req.rd_wr_en == RW_WRITE) & (sigdecode_h_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (sigdecode_h_mem_wr_req.addr[0] == bank);
        skdecode_mem_we0_bank[bank] = (skdecode_mem_wr_req[bank].rd_wr_en == RW_WRITE);
        pkdecode_mem_we0_bank[bank] = (pkdecode_mem_wr_req[bank].rd_wr_en == RW_WRITE);
        sigdecode_z_mem_we0_bank[bank] = (sigdecode_z_mem_wr_req[bank].rd_wr_en == RW_WRITE);
        decompress_mem_we0_bank[bank] = (decompress_mem_wr_req.rd_wr_en == RW_WRITE) & (decompress_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (decompress_mem_wr_req.addr[0] == bank);

        abr_mem_we0_bank[bank] = sampler_mem_we0_bank[bank] | ntt_mem_we0_bank[bank] | decompress_mem_we0_bank[bank] |
                                   decomp_mem_we0_bank[bank] | skdecode_mem_we0_bank[bank] | pkdecode_mem_we0_bank[bank] |
                                   sigdecode_h_mem_we0_bank[bank] | sigdecode_z_mem_we0_bank[bank] | zeroize_mem_we;

        abr_mem_waddr0_bank[bank] = ({ABR_MEM_ADDR_WIDTH-4{sampler_mem_we0_bank[bank]}}     & sampler_mem_addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{ntt_mem_we0_bank[bank]}}         & ntt_mem_wr_req_mux[0][ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{decomp_mem_we0_bank[bank]}}      & decomp_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{decompress_mem_we0_bank[bank]}}  & decompress_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{sigdecode_h_mem_we0_bank[bank]}} & sigdecode_h_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{skdecode_mem_we0_bank[bank]}}    & skdecode_mem_wr_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{pkdecode_mem_we0_bank[bank]}}    & pkdecode_mem_wr_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{sigdecode_z_mem_we0_bank[bank]}} & sigdecode_z_mem_wr_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{zeroize_mem_we}} & (zeroize_mem_addr[ABR_MEM_ADDR_WIDTH-5:0]));

        abr_mem_wdata0_bank[bank] = ({ABR_MEM_DATA_WIDTH{sampler_mem_we0_bank[bank]}}     & sampler_mem_data) |
                                      ({ABR_MEM_DATA_WIDTH{ntt_mem_we0_bank[bank]}}         & ntt_mem_wr_data_mux[0][ABR_MEM_DATA_WIDTH-1:0]) |
                                      ({ABR_MEM_DATA_WIDTH{decomp_mem_we0_bank[bank]}}      & decomp_mem_wr_data) |
                                      ({ABR_MEM_DATA_WIDTH{decompress_mem_we0_bank[bank]}}  & decompress_mem_wr_data) |
                                      ({ABR_MEM_DATA_WIDTH{sigdecode_h_mem_we0_bank[bank]}} & sigdecode_h_mem_wr_data) |
                                      ({ABR_MEM_DATA_WIDTH{skdecode_mem_we0_bank[bank]}}    & skdecode_mem_wr_data[bank]) |
                                      ({ABR_MEM_DATA_WIDTH{pkdecode_mem_we0_bank[bank]}}    & pkdecode_mem_wr_data[bank]) |
                                      ({ABR_MEM_DATA_WIDTH{sigdecode_z_mem_we0_bank[bank]}} & sigdecode_z_mem_wr_data[bank]);
      end
    end else begin
      sampler_mem_we[i] = sampler_mem_dv & (sampler_mem_addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      decomp_mem_we[i] = (decomp_mem_wr_req.rd_wr_en == RW_WRITE) & (decomp_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      sigdecode_h_mem_we[i] = (sigdecode_h_mem_wr_req.rd_wr_en == RW_WRITE) & (sigdecode_h_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
  
      abr_mem_we[i] = sampler_mem_we[i] | ntt_mem_we_mux[i] | decomp_mem_we[i] | sigdecode_h_mem_we[i] | zeroize_mem_we;
      abr_mem_waddr[i] = ({ABR_MEM_ADDR_WIDTH-3{sampler_mem_we[i]}}     & sampler_mem_addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{ntt_mem_we_mux[i]}}     & ntt_mem_wr_req_mux[i][ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{decomp_mem_we[i]}}      & decomp_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{sigdecode_h_mem_we[i]}} & sigdecode_h_mem_wr_req.addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{zeroize_mem_we}}        & zeroize_mem_addr[ABR_MEM_ADDR_WIDTH-4:0]);

    end
  end
end

//Write Data Muxes
always_comb begin
  for (int i = 1; i < ABR_MEM_MASKED_INST; i++) begin
    abr_mem_wdata[i] = ({ABR_MEM_DATA_WIDTH{sampler_mem_we[i]}}     & sampler_mem_data) |
                         ({ABR_MEM_DATA_WIDTH{ntt_mem_we_mux[i]}}     & ntt_mem_wr_data_mux[i][ABR_MEM_DATA_WIDTH-1:0]) |
                         ({ABR_MEM_DATA_WIDTH{decomp_mem_we[i]}}      & decomp_mem_wr_data) |
                         ({ABR_MEM_DATA_WIDTH{sigdecode_h_mem_we[i]}} & sigdecode_h_mem_wr_data);
  end
  abr_mem_masked_wdata = '0;
  for (int ntt= 0; ntt < ABR_NUM_NTT; ntt++) begin
    abr_mem_masked_wdata[ABR_MEM_MASKED_INST] |= ({ABR_MEM_MASKED_DATA_WIDTH{ntt_mem_we[ntt][ABR_MEM_MASKED_INST]}} & ntt_mem_wr_data[ntt]);
  end
end

//Read Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    if (i == 0) begin
      ntt_mem_re0_bank_mux = '0;
      pwo_a_mem_re0_bank_mux = '0;
      pwo_b_mem_re0_bank_mux = '0;
      for (int bank = 0; bank < 2; bank++) begin
        for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
          ntt_mem_re0_bank[ntt][bank]   = (ntt_mem_rd_req[ntt].rd_wr_en == RW_READ) & (ntt_mem_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (ntt_mem_rd_req[ntt].addr[0] == bank);
          pwo_a_mem_re0_bank[ntt][bank] = (pwm_a_rd_req[ntt].rd_wr_en == RW_READ) & (pwm_a_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_a_rd_req[ntt].addr[0] == bank);
          pwo_b_mem_re0_bank[ntt][bank] = (ntt_shuffling_en[ntt] ? ~sampler_ntt_dv_f[ntt] : ~sampler_ntt_dv[ntt]) & (pwm_b_rd_req[ntt].rd_wr_en == RW_READ) & (pwm_b_rd_req[ntt].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_b_rd_req[ntt].addr[0] == bank);
          ntt_mem_re0_bank_mux[bank] |= ntt_mem_re0_bank[ntt][bank];
          pwo_a_mem_re0_bank_mux[bank] |= pwo_a_mem_re0_bank[ntt][bank];
          pwo_b_mem_re0_bank_mux[bank] |= pwo_b_mem_re0_bank[ntt][bank];
        end
    
        decomp_mem_re0_bank[0][bank] = (decomp_mem_rd_req[0].rd_wr_en == RW_READ) & (decomp_mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_rd_req[0].addr[0] == bank);
        decomp_mem_re0_bank[1][bank] = (decomp_mem_rd_req[1].rd_wr_en == RW_READ) & (decomp_mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_rd_req[1].addr[0] == bank);
        normcheck_mem_re0_bank[bank] = (normcheck_mem_rd_req.rd_wr_en == RW_READ) & (normcheck_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (normcheck_mem_rd_req.addr[0] == bank);
        compress_mem_re0_bank[bank]  = (compress_mem_rd_req.rd_wr_en == RW_READ) & (compress_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]) & (compress_mem_rd_req.addr[0] == bank);
        skencode_mem_re0_bank[bank]  = (skencode_mem_rd_req[bank].rd_wr_en == RW_READ);
        sigencode_mem_re0_bank[bank] = (sigencode_mem_rd_req[bank].rd_wr_en == RW_READ);
        pwr2rnd_mem_re0_bank[bank]   = (pwr2rnd_mem_rd_req[bank].rd_wr_en == RW_READ);

        abr_mem_re0_bank[bank] = ntt_mem_re0_bank_mux[bank] | pwo_a_mem_re0_bank_mux[bank] | pwo_b_mem_re0_bank_mux[bank] |
                                   decomp_mem_re0_bank[0][bank] | decomp_mem_re0_bank[1][bank] | 
                                   skencode_mem_re0_bank[bank] | normcheck_mem_re0_bank[bank] |
                                   sigencode_mem_re0_bank[bank] | pwr2rnd_mem_re0_bank[bank] |
                                   compress_mem_re0_bank[bank];
        abr_mem_raddr0_bank[bank] = ({ABR_MEM_ADDR_WIDTH-4{ntt_mem_re0_bank_mux[bank]}}   & ntt_mem_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{pwo_a_mem_re0_bank_mux[bank]}} & pwm_a_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:1])   |
                                      ({ABR_MEM_ADDR_WIDTH-4{pwo_b_mem_re0_bank_mux[bank]}} & pwm_b_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:1])   |
                                      ({ABR_MEM_ADDR_WIDTH-4{decomp_mem_re0_bank[0][bank]}} & decomp_mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{decomp_mem_re0_bank[1][bank]}} & decomp_mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{skencode_mem_re0_bank[bank]}}  & skencode_mem_rd_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{normcheck_mem_re0_bank[bank]}} & normcheck_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{sigencode_mem_re0_bank[bank]}} & sigencode_mem_rd_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1])|
                                      ({ABR_MEM_ADDR_WIDTH-4{pwr2rnd_mem_re0_bank[bank]}}   & pwr2rnd_mem_rd_req[bank].addr[ABR_MEM_ADDR_WIDTH-4:1]) |
                                      ({ABR_MEM_ADDR_WIDTH-4{compress_mem_re0_bank[bank]}} & compress_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-4:1]);
      end
    end else begin
      decomp_mem_re[0][i] = (decomp_mem_rd_req[0].rd_wr_en == RW_READ) & (decomp_mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      decomp_mem_re[1][i] = (decomp_mem_rd_req[1].rd_wr_en == RW_READ) & (decomp_mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      normcheck_mem_re[i] = (normcheck_mem_rd_req.rd_wr_en == RW_READ) & (normcheck_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      makehint_mem_re[i]  = (makehint_mem_rd_req.rd_wr_en == RW_READ)  & (makehint_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);
      compress_mem_re[i]  = (compress_mem_rd_req.rd_wr_en == RW_READ) & (compress_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-1:ABR_MEM_ADDR_WIDTH-3] == i[2:0]);

      abr_mem_re[i] = ntt_mem_re_mux[i] | pwo_a_mem_re_mux[i] | pwo_b_mem_re_mux[i] |
                        decomp_mem_re[0][i] | decomp_mem_re[1][i] | 
                        normcheck_mem_re[i] | makehint_mem_re[i] | compress_mem_re[i];
      abr_mem_raddr[i] = ({ABR_MEM_ADDR_WIDTH-3{ntt_mem_re_mux[i]}}   & ntt_mem_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:0])   |
                           ({ABR_MEM_ADDR_WIDTH-3{pwo_a_mem_re_mux[i]}} & pwm_a_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{pwo_b_mem_re_mux[i]}} & pwm_b_rd_req_mux[i][ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{decomp_mem_re[0][i]}} & decomp_mem_rd_req[0].addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{decomp_mem_re[1][i]}} & decomp_mem_rd_req[1].addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{normcheck_mem_re[i]}} & normcheck_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{makehint_mem_re[i]}}  & makehint_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-4:0]) |
                           ({ABR_MEM_ADDR_WIDTH-3{compress_mem_re[i]}} & compress_mem_rd_req.addr[ABR_MEM_ADDR_WIDTH-4:0]);
      end
  end
end

//Align read enables
always_ff @(posedge clk or negedge rst_b) begin : read_mux_flops
  if (!rst_b) begin
    ntt_mem_re_f <= 0;
    pwo_a_mem_re_f <= 0;
    pwo_b_mem_re_f <= 0;
    decomp_mem_re_f <= 0;
    normcheck_mem_re_f <= 0;
    compress_mem_re_f <= 0;
    ntt_mem_re0_bank_f <= 0;
    pwo_a_mem_re0_bank_f <= 0;
    pwo_b_mem_re0_bank_f <= 0;
    decomp_mem_re0_bank_f <= 0;
    normcheck_mem_re0_bank_f <= 0;
    compress_mem_re0_bank_f <= 0;
    sib_mem_re_f <= 0;
  end
  else if (zeroize_reg) begin
    ntt_mem_re_f <= 0;
    pwo_a_mem_re_f <= 0;
    pwo_b_mem_re_f <= 0;
    decomp_mem_re_f <= 0;
    normcheck_mem_re_f <= 0;
    compress_mem_re_f <= 0;
    ntt_mem_re0_bank_f <= 0;
    pwo_a_mem_re0_bank_f <= 0;
    pwo_b_mem_re0_bank_f <= 0;
    decomp_mem_re0_bank_f <= 0;
    normcheck_mem_re0_bank_f <= 0;
    compress_mem_re0_bank_f <= 0;
    sib_mem_re_f <= 0;
  end
  else begin
    ntt_mem_re_f <= ntt_mem_re;
    pwo_a_mem_re_f<= pwo_a_mem_re;
    pwo_b_mem_re_f <= pwo_b_mem_re;
    decomp_mem_re_f <= decomp_mem_re;
    normcheck_mem_re_f <= normcheck_mem_re;
    compress_mem_re_f <= compress_mem_re;
    ntt_mem_re0_bank_f <= ntt_mem_re0_bank;
    pwo_a_mem_re0_bank_f <= pwo_a_mem_re0_bank;
    pwo_b_mem_re0_bank_f <= pwo_b_mem_re0_bank;
    decomp_mem_re0_bank_f <= decomp_mem_re0_bank;
    normcheck_mem_re0_bank_f <= normcheck_mem_re0_bank;
    compress_mem_re0_bank_f <= compress_mem_re0_bank;
    sib_mem_re_f <= sib_mem_re;
  end
end  

//Read data muxes
always_comb begin
  ntt_mem_rd_data = 0;
  pwm_a_rd_data = 0;
  pwm_b_rd_data = 0;
  decomp_mem_rd_data = 0;
  normcheck_mem_rd_data = 0;
  compress_mem_rd_data = 0;

  for (int i = 0; i < ABR_MEM_MASKED_INST; i++) begin
    if (i == 0) begin
      for (int bank = 0; bank < 2; bank++) begin
        for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
          ntt_mem_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{ntt_mem_re0_bank_f[ntt][bank]}} & abr_mem_rdata0_bank[bank]);
          pwm_a_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{pwo_a_mem_re0_bank_f[ntt][bank]}} & abr_mem_rdata0_bank[bank]);
          pwm_b_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{pwo_b_mem_re0_bank_f[ntt][bank]}} & abr_mem_rdata0_bank[bank]);
        end
        decomp_mem_rd_data[0] |= ({ABR_MEM_DATA_WIDTH{decomp_mem_re0_bank_f[0][bank]}} & abr_mem_rdata0_bank[bank]);
        decomp_mem_rd_data[1] |= ({ABR_MEM_DATA_WIDTH{decomp_mem_re0_bank_f[1][bank]}} & abr_mem_rdata0_bank[bank]);
        normcheck_mem_rd_data |= ({ABR_MEM_DATA_WIDTH{normcheck_mem_re0_bank_f[bank]}} & abr_mem_rdata0_bank[bank]);
        compress_mem_rd_data |= ({ABR_MEM_DATA_WIDTH{compress_mem_re0_bank_f[bank]}} & abr_mem_rdata0_bank[bank]);
      end
    end else begin
      for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
        ntt_mem_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{ntt_mem_re_f[ntt][i]}} & abr_mem_rdata[i]);
        pwm_a_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{pwo_a_mem_re_f[ntt][i]}} & abr_mem_rdata[i]);
        pwm_b_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{pwo_b_mem_re_f[ntt][i]}} & abr_mem_rdata[i]);
      end
      decomp_mem_rd_data[0] |= ({ABR_MEM_DATA_WIDTH{decomp_mem_re_f[0][i]}} & abr_mem_rdata[i]);
      decomp_mem_rd_data[1] |= ({ABR_MEM_DATA_WIDTH{decomp_mem_re_f[1][i]}} & abr_mem_rdata[i]);
      normcheck_mem_rd_data |= ({ABR_MEM_DATA_WIDTH{normcheck_mem_re_f[i]}} & abr_mem_rdata[i]);
      compress_mem_rd_data |= ({ABR_MEM_DATA_WIDTH{compress_mem_re_f[i]}} & abr_mem_rdata[i]);
    end
  end
  //Masked memory uses full width
  for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
    ntt_mem_rd_data[ntt] |= ({ABR_MEM_MASKED_DATA_WIDTH{ntt_mem_re_f[ntt][3]}} & abr_mem_masked_rdata[3]);
    pwm_a_rd_data[ntt]   |= ({ABR_MEM_MASKED_DATA_WIDTH{pwo_a_mem_re_f[ntt][3]}} & abr_mem_masked_rdata[3]);
    pwm_b_rd_data[ntt]   |= ({ABR_MEM_MASKED_DATA_WIDTH{pwo_b_mem_re_f[ntt][3]}} & abr_mem_masked_rdata[3]);
  end
  for (int ntt = 0; ntt < ABR_NUM_NTT; ntt++) begin
    ntt_mem_rd_data[ntt][ABR_MEM_DATA_WIDTH-1:0] |= ({ABR_MEM_DATA_WIDTH{sib_mem_re_f[ntt]}} & sib_mem_rd_data);
  end
end

always_comb skencode_mem_rd_data = abr_mem_rdata0_bank;
always_comb makehint_mem_rd_data = abr_mem_rdata[1];
always_comb sigencode_mem_rd_data = abr_mem_rdata0_bank;
always_comb pwr2rnd_mem_rd_data = abr_mem_rdata0_bank;

///Memory instance 0 bank 0
always_comb abr_memory_export.mem_inst0_bank0_we_i = (abr_mem_we0_bank[0]);
always_comb abr_memory_export.mem_inst0_bank0_waddr_i = (abr_mem_waddr0_bank[0][ABR_MEM_INST0_ADDR_W-1:0]);
always_comb abr_memory_export.mem_inst0_bank0_wdata_i = (abr_mem_wdata0_bank[0]);
always_comb abr_memory_export.mem_inst0_bank0_re_i = zeroize_mem_re ? 1'b1: (abr_mem_re0_bank[0]);
always_comb abr_memory_export.mem_inst0_bank0_raddr_i = zeroize_mem_re ? '0: (abr_mem_raddr0_bank[0][ABR_MEM_INST0_ADDR_W-1:0]);
always_comb abr_mem_rdata0_bank[0] = abr_memory_export.mem_inst0_bank0_rdata_o;

//Memory instance 0 bank 1
always_comb abr_memory_export.mem_inst0_bank1_we_i = (abr_mem_we0_bank[1]);
always_comb abr_memory_export.mem_inst0_bank1_waddr_i = (abr_mem_waddr0_bank[1][ABR_MEM_INST0_ADDR_W-1:0]);
always_comb abr_memory_export.mem_inst0_bank1_wdata_i = (abr_mem_wdata0_bank[1]);
always_comb abr_memory_export.mem_inst0_bank1_re_i = zeroize_mem_re ? 1'b1: (abr_mem_re0_bank[1]);
always_comb abr_memory_export.mem_inst0_bank1_raddr_i = zeroize_mem_re ? '0: (abr_mem_raddr0_bank[1][ABR_MEM_INST0_ADDR_W-1:0]);
always_comb abr_mem_rdata0_bank[1] = abr_memory_export.mem_inst0_bank1_rdata_o;

//Memory instance 1
always_comb abr_memory_export.mem_inst1_we_i = (abr_mem_we[1]);
always_comb abr_memory_export.mem_inst1_waddr_i = (abr_mem_waddr[1][ABR_MEM_INST1_ADDR_W-1:0]);
always_comb abr_memory_export.mem_inst1_wdata_i = (abr_mem_wdata[1]);
always_comb abr_memory_export.mem_inst1_re_i = zeroize_mem_re ? 1'b1: (abr_mem_re[1]);
always_comb abr_memory_export.mem_inst1_raddr_i = zeroize_mem_re ? '0: (abr_mem_raddr[1][ABR_MEM_INST1_ADDR_W-1:0]);
always_comb abr_mem_rdata[1] = abr_memory_export.mem_inst1_rdata_o;

//Memory instance 2
always_comb abr_memory_export.mem_inst2_we_i = (abr_mem_we[2]);
always_comb abr_memory_export.mem_inst2_waddr_i = (abr_mem_waddr[2][ABR_MEM_INST2_ADDR_W-1:0]);
always_comb abr_memory_export.mem_inst2_wdata_i = (abr_mem_wdata[2]);
always_comb abr_memory_export.mem_inst2_re_i = zeroize_mem_re ? 1'b1: (abr_mem_re[2]);
always_comb abr_memory_export.mem_inst2_raddr_i = zeroize_mem_re ? '0: (abr_mem_raddr[2][ABR_MEM_INST2_ADDR_W-1:0]);
always_comb abr_mem_rdata[2] = abr_memory_export.mem_inst2_rdata_o;

//Memory instance 3
always_comb abr_memory_export.mem_inst3_we_i = (abr_mem_we[3]);
always_comb abr_memory_export.mem_inst3_waddr_i = (abr_mem_waddr[3][ABR_MEM_INST3_ADDR_W-1:0]);
always_comb abr_memory_export.mem_inst3_wdata_i = (abr_mem_masked_wdata[3]);
always_comb abr_memory_export.mem_inst3_re_i = zeroize_mem_re ? 1'b1: (abr_mem_re[3]);
always_comb abr_memory_export.mem_inst3_raddr_i = zeroize_mem_re ? '0: (abr_mem_raddr[3][ABR_MEM_INST3_ADDR_W-1:0]);
always_comb abr_mem_masked_rdata[3] = abr_memory_export.mem_inst3_rdata_o;

//SK Memory Bank 0
always_comb abr_memory_export.sk_mem_bank0_we_i = sk_bank0_mem_if.we_i;
always_comb abr_memory_export.sk_mem_bank0_waddr_i = sk_bank0_mem_if.waddr_i;
always_comb abr_memory_export.sk_mem_bank0_wdata_i = sk_bank0_mem_if.wdata_i;
always_comb abr_memory_export.sk_mem_bank0_re_i = zeroize_mem_re ? 1'b1: sk_bank0_mem_if.re_i;
always_comb abr_memory_export.sk_mem_bank0_raddr_i = zeroize_mem_re ? '0: sk_bank0_mem_if.raddr_i;
always_comb sk_bank0_mem_if.rdata_o = abr_memory_export.sk_mem_bank0_rdata_o;

//SK Memory Bank 1
always_comb abr_memory_export.sk_mem_bank1_we_i = sk_bank1_mem_if.we_i;
always_comb abr_memory_export.sk_mem_bank1_waddr_i = sk_bank1_mem_if.waddr_i;
always_comb abr_memory_export.sk_mem_bank1_wdata_i = sk_bank1_mem_if.wdata_i;
always_comb abr_memory_export.sk_mem_bank1_re_i = zeroize_mem_re ? 1'b1: sk_bank1_mem_if.re_i;
always_comb abr_memory_export.sk_mem_bank1_raddr_i = zeroize_mem_re ? '0: sk_bank1_mem_if.raddr_i;
always_comb sk_bank1_mem_if.rdata_o = abr_memory_export.sk_mem_bank1_rdata_o;

//Sig Z Memory
always_comb abr_memory_export.sig_z_mem_we_i = sig_z_mem_if.we_i;
always_comb abr_memory_export.sig_z_mem_waddr_i = sig_z_mem_if.waddr_i;
always_comb abr_memory_export.sig_z_mem_wdata_i = sig_z_mem_if.wdata_i;
always_comb abr_memory_export.sig_z_mem_wstrobe_i = sig_z_mem_if.wstrobe_i;
always_comb abr_memory_export.sig_z_mem_re_i = zeroize_mem_re ? 1'b1: sig_z_mem_if.re_i;
always_comb abr_memory_export.sig_z_mem_raddr_i = zeroize_mem_re ? '0: sig_z_mem_if.raddr_i;
always_comb sig_z_mem_if.rdata_o = abr_memory_export.sig_z_mem_rdata_o;

//PK Memory
always_comb abr_memory_export.pk_mem_we_i = pk_mem_if.we_i;
always_comb abr_memory_export.pk_mem_waddr_i = pk_mem_if.waddr_i;
always_comb abr_memory_export.pk_mem_wdata_i = pk_mem_if.wdata_i;
always_comb abr_memory_export.pk_mem_wstrobe_i = pk_mem_if.wstrobe_i;
always_comb abr_memory_export.pk_mem_re_i = zeroize_mem_re ? 1'b1: pk_mem_if.re_i;
always_comb abr_memory_export.pk_mem_raddr_i = zeroize_mem_re ? '0: pk_mem_if.raddr_i;
always_comb pk_mem_if.rdata_o = abr_memory_export.pk_mem_rdata_o;

`ABR_ASSERT_MUTEX(ERR_MEM_0_0_RD_ACCESS_MUTEX, {ntt_mem_re0_bank_mux[0],pwo_a_mem_re0_bank_mux[0],pwo_b_mem_re0_bank_mux[0],
                                                decomp_mem_re0_bank[0][0],decomp_mem_re0_bank[1][0], pwr2rnd_mem_re0_bank[0],
                                                skencode_mem_re0_bank[0], normcheck_mem_re0_bank[0], sigencode_mem_re0_bank[0],
                                                compress_mem_re0_bank[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_0_1_RD_ACCESS_MUTEX, {ntt_mem_re0_bank_mux[1],pwo_a_mem_re0_bank_mux[1],pwo_b_mem_re0_bank_mux[1],
                                                decomp_mem_re0_bank[0][1],decomp_mem_re0_bank[1][1], pwr2rnd_mem_re0_bank[1], 
                                                skencode_mem_re0_bank[1],normcheck_mem_re0_bank[1],sigencode_mem_re0_bank[1],
                                                compress_mem_re0_bank[1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_1_RD_ACCESS_MUTEX, {ntt_mem_re_mux[1],pwo_a_mem_re_mux[1],pwo_b_mem_re_mux[1],compress_mem_re[1],
                                              normcheck_mem_re[1], decomp_mem_re[0][1],decomp_mem_re[1][1],makehint_mem_re[1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_RD_ACCESS_MUTEX, {ntt_mem_re_mux[2],pwo_a_mem_re_mux[2],pwo_b_mem_re_mux[2],compress_mem_re[2],
                                              normcheck_mem_re[2], decomp_mem_re[0][2],decomp_mem_re[1][2],makehint_mem_re[2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_RD_ACCESS_MUTEX, {ntt_mem_re_mux[3],pwo_a_mem_re_mux[3],pwo_b_mem_re_mux[3],compress_mem_re[3],
                                              normcheck_mem_re[3], decomp_mem_re[0][3],decomp_mem_re[1][3],makehint_mem_re[3]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_0_0_WR_ACCESS_MUTEX, {sampler_mem_we0_bank[0],ntt_mem_we0_bank[0],decomp_mem_we0_bank[0],decompress_mem_we0_bank[0],
                                                skdecode_mem_we0_bank[0], pkdecode_mem_we0_bank[0], sigdecode_h_mem_we0_bank[0],
                                                sigdecode_z_mem_we0_bank[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_0_1_WR_ACCESS_MUTEX, {sampler_mem_we0_bank[1],ntt_mem_we0_bank[1],decomp_mem_we0_bank[1],decompress_mem_we0_bank[1],
                                                skdecode_mem_we0_bank[1], pkdecode_mem_we0_bank[1], sigdecode_h_mem_we0_bank[1],
                                                sigdecode_z_mem_we0_bank[1]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_1_WR_ACCESS_MUTEX, {sampler_mem_we[1],ntt_mem_we_mux[1],decomp_mem_we[1],sigdecode_h_mem_we[1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_WR_ACCESS_MUTEX, {sampler_mem_we[2],ntt_mem_we_mux[2],decomp_mem_we[2],sigdecode_h_mem_we[2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_WR_ACCESS_MUTEX, {sampler_mem_we[3],ntt_mem_we_mux[3],decomp_mem_we[3],sigdecode_h_mem_we[3]}, clk, !rst_b)

`ABR_ASSERT_KNOWN(ERR_MEM_0_0_WDATA_X, {abr_mem_wdata0_bank[0]}, clk, !rst_b, abr_mem_we0_bank[0])
`ABR_ASSERT_KNOWN(ERR_MEM_0_1_WDATA_X, {abr_mem_wdata0_bank[1]}, clk, !rst_b, abr_mem_we0_bank[1])
`ABR_ASSERT_KNOWN(ERR_MEM_1_WDATA_X, {abr_mem_wdata[1]}, clk, !rst_b, abr_mem_we[1])
`ABR_ASSERT_KNOWN(ERR_MEM_2_WDATA_X, {abr_mem_wdata[2]}, clk, !rst_b, abr_mem_we[2])
`ABR_ASSERT_KNOWN(ERR_MEM_3_WDATA_X, {abr_mem_masked_wdata[3]}, clk, !rst_b, abr_mem_we[3])

`ABR_ASSERT_KNOWN(ERR_MEM_0_RDATA_X, {ntt_mem_rd_data}, clk, !rst_b)
`ABR_ASSERT_KNOWN(ERR_MEM_1_RDATA_X, {pwm_a_rd_data}, clk, !rst_b)
`ABR_ASSERT_KNOWN(ERR_MEM_2_RDATA_X, {pwm_b_rd_data}, clk, !rst_b)

//Only NTT reads/writes to MEM 3
`ABR_ASSERT_NEVER(ERR_MEM_3_WR, (sampler_mem_we[3] | decomp_mem_we[3] | sigdecode_h_mem_we[3]), clk, !rst_b)
`ABR_ASSERT_NEVER(ERR_MEM_3_RD, (compress_mem_re_f[3] | normcheck_mem_re_f[3] | decomp_mem_re_f[0][3] | decomp_mem_re_f[1][3]), clk, !rst_b)

  abr_prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o;
  logic clk_i;

  assign clk_i = clk;

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3FsmCheck_A,
  sampler_top_inst.sha3_inst.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(KeccakRoundFsmCheck_A,
  sampler_top_inst.sha3_inst.u_keccak.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_FSM_ERROR_TRIGGER_ALERT(SHA3padFsmCheck_A,
  sampler_top_inst.sha3_inst.u_pad.u_state_regs, alert_tx_o[1])

  `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(WrMsgCountCheck_A,
  sampler_top_inst.sha3_inst.u_pad.u_wrmsg_count, alert_tx_o[1])

  `ABR_ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(RoundCountCheck_A,
  sampler_top_inst.sha3_inst.u_keccak.u_round_count, alert_tx_o[1])

endmodule
