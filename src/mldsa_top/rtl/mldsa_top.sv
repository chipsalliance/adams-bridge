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
`include "config_defines.svh"
`include "abr_prim_assert.sv"

module mldsa_top
  import abr_prim_alert_pkg::*;
  import mldsa_reg_pkg::*;
  import mldsa_params_pkg::*;
  import mldsa_ctrl_pkg::*;
  import mldsa_sampler_pkg::*;
  import abr_sha3_pkg::*;
  import ntt_defines_pkg::*;
  import decompose_defines_pkg::*;
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

  output logic                      error_intr,
  output logic                      notif_intr


  );

  localparam DATA_WIDTH = 32;

//Signal Declarations
  logic zeroize_reg;
  logic [1:0] cmd_reg;

  mldsa_sampler_mode_e       sampler_mode;
  logic                      sha3_start;
  logic                      msg_start;
  logic                      msg_valid;
  logic                      msg_rdy;
  logic [MsgStrbW-1:0]       msg_strobe;
  logic [MsgWidth-1:0]       msg_data[Sha3Share];
  logic                      sampler_start;
  logic [MLDSA_MEM_ADDR_WIDTH-1:0] dest_base_addr;

  logic                        sampler_busy;
  logic                        sampler_state_dv;
  logic [abr_sha3_pkg::StateW-1:0] sampler_state_data[Sha3Share];

  logic sampler_mem_dv;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] sampler_mem_data;
  logic [MLDSA_MEM_ADDR_WIDTH-1:0] sampler_mem_addr;

  logic [1:0]                                  sampler_ntt_dv;
  logic [1:0]                                  sampler_ntt_mode;
  logic [1:0]                                  sampler_valid;
  logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] sampler_ntt_data;

  mldsa_ntt_mode_e [1:0] ntt_mode;
  mode_t [1:0] mode;
  logic [1:0] accumulate;
  logic [1:0] ntt_enable;
  ntt_mem_addr_t [1:0] ntt_mem_base_addr;
  pwo_mem_addr_t [1:0] pwo_mem_base_addr;
  mem_if_t [1:0] ntt_mem_wr_req;
  mem_if_t [1:0] ntt_mem_rd_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] ntt_mem_wr_data;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] ntt_mem_rd_data;
  mem_if_t [1:0] pwm_a_rd_req;
  mem_if_t [1:0] pwm_b_rd_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] pwm_a_rd_data;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] pwm_b_rd_data;
  logic [1:0] ntt_done;
  logic [1:0] ntt_busy;

  mem_if_t w1_mem_wr_req;
  logic [3:0] w1_mem_wr_data;
  mem_if_t w1_mem_rd_req;
  logic [3:0] w1_mem_rd_data;

  logic decomp_msg_valid;
  logic [MsgWidth-1:0] decomp_msg_data[Sha3Share];

  logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_src0_base_addr;
  logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_src1_base_addr;
  logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0] aux_dest_base_addr;

  logic power2round_enable, power2round_done;
  mem_if_t [1:0] pwr2rnd_mem_rd_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] pwr2rnd_mem_rd_data;
  mem_if_t [1:0] pwr2rnd_keymem_if;
  logic [1:0] [DATA_WIDTH-1:0] pwr2rnd_wr_data;
  logic pk_t1_wren;
  logic [7:0][9:0] pk_t1_wrdata; // TODO: change to parameter
  logic [7:0] pk_t1_wr_addr; // TODO: change to parameter

  logic decompose_enable, decompose_done;
  mem_if_t decomp_mem_wr_req;
  mem_if_t [1:0] decomp_mem_rd_req;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] decomp_mem_wr_data;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] decomp_mem_rd_data;
  logic decompose_mode;

  logic skencode_enable, skencode_done;
  mem_if_t skencode_keymem_if;
  logic [DATA_WIDTH-1:0] skencode_wr_data;
  mem_if_t [1:0] skencode_mem_rd_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] skencode_mem_rd_data;

  logic skdecode_enable, skdecode_done;
  mem_if_t [1:0] skdecode_keymem_if;
  logic [1:0][DATA_WIDTH-1:0] skdecode_rd_data;
  mem_if_t [1:0] skdecode_mem_wr_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] skdecode_mem_wr_data;

  logic makehint_enable, makehint_done;
  logic makehint_invalid;
  mem_if_t makehint_mem_rd_req;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] makehint_mem_rd_data;
  logic makehint_reg_wren;
  logic [3:0][7:0] makehint_reg_wrdata;
  logic [MLDSA_MEM_ADDR_WIDTH-1:0] makehint_reg_wr_addr;

  logic normcheck_enable;
  logic normcheck_done;
  logic [1:0] normcheck_mode;
  logic [MLDSA_MEM_ADDR_WIDTH-1:0] normcheck_src_addr;
  logic normcheck_invalid;
  mem_if_t normcheck_mem_rd_req;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] normcheck_mem_rd_data;

  logic sigencode_enable, sigencode_done;
  mem_if_t [1:0] sigencode_mem_rd_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] sigencode_mem_rd_data;
  mem_if_t sigencode_mem_wr_req;
  logic [1:0][3:0][19:0] sigencode_mem_wr_data;

  logic pkdecode_enable, pkdecode_done;
  mem_if_t [1:0] pkdecode_mem_wr_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] pkdecode_mem_wr_data;
  logic [7:0] pkdecode_rd_addr;
  logic [7:0][T1_COEFF_W-1:0] pkdecode_rd_data;

  logic sigdecode_z_enable, sigdecode_z_done;
  mem_if_t [1:0] sigdecode_z_mem_wr_req;
  logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] sigdecode_z_mem_wr_data;
  mem_if_t sigdecode_z_mem_rd_req;
  logic [1:0][3:0][19:0] sigdecode_z_mem_rd_data;

  logic sigdecode_h_enable, sigdecode_h_done;
  logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0] signature_h;
  logic sigdecode_h_invalid;
  mem_if_t sigdecode_h_mem_wr_req;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] sigdecode_h_mem_wr_data;

  mem_if_t                       sib_mem_rd_req;
  logic [MLDSA_MEM_DATA_WIDTH-1:0] sib_mem_rd_data;

  logic lfsr_enable;
  logic [1:0][LFSR_W-1:0] lfsr_seed;
  logic [RND_W-1:0] rand_bits;

  //gasket to assemble reg requests
  logic mldsa_reg_dv;
  logic mldsa_reg_hold;
  logic mldsa_reg_rd_ack, mldsa_reg_wr_ack;
  logic [CLIENT_DATA_WIDTH-1:0] mldsa_reg_rdata;
  logic [AHB_ADDR_WIDTH-1:0]    mldsa_reg_addr;
  logic [CLIENT_DATA_WIDTH-1:0] mldsa_reg_wdata;
  logic                         mldsa_reg_write;

  logic mldsa_reg_err, mldsa_reg_read_err, mldsa_reg_write_err;

  mldsa_reg__in_t mldsa_reg_hwif_in;
  mldsa_reg__out_t mldsa_reg_hwif_out;

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
    .dv(mldsa_reg_dv),
    .hld(mldsa_reg_hold),
    .err(mldsa_reg_err),
    .write(mldsa_reg_write),
    .wdata(mldsa_reg_wdata),
    .addr(mldsa_reg_addr[AHB_ADDR_WIDTH-1:0]),

    .rdata(mldsa_reg_rdata)
);

always_comb mldsa_reg_err = (mldsa_reg_rd_ack & mldsa_reg_read_err) | (mldsa_reg_wr_ack & mldsa_reg_write_err);
always_comb mldsa_reg_hold = mldsa_reg_dv & ~(mldsa_reg_rd_ack | mldsa_reg_wr_ack); //FIXME can we do this without dv?

mldsa_reg mldsa_reg_inst (
  .clk(clk),
  .rst(rst_b),

  .s_cpuif_req(mldsa_reg_dv),
  .s_cpuif_req_is_wr(mldsa_reg_write),
  .s_cpuif_addr(mldsa_reg_addr[MLDSA_REG_ADDR_WIDTH-1:0]),
  .s_cpuif_wr_data(mldsa_reg_wdata),
  .s_cpuif_wr_biten('1),
  .s_cpuif_req_stall_wr(),
  .s_cpuif_req_stall_rd(),
  .s_cpuif_rd_ack(mldsa_reg_rd_ack),
  .s_cpuif_rd_err(mldsa_reg_read_err),
  .s_cpuif_rd_data(mldsa_reg_rdata),
  .s_cpuif_wr_ack(mldsa_reg_wr_ack),
  .s_cpuif_wr_err(mldsa_reg_write_err),

  .hwif_in(mldsa_reg_hwif_in),
  .hwif_out(mldsa_reg_hwif_out)
);

mldsa_ctrl mldsa_control_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

`ifdef RV_FPGA_SCA
  .NTT_trigger(NTT_trigger),
  .PWM_trigger(PWM_trigger),
  .PWA_trigger(PWA_trigger),
  .INTT_trigger(INTT_trigger),
`endif

  //control interface
  .mldsa_reg_hwif_in_o(mldsa_reg_hwif_in),
  .mldsa_reg_hwif_out_i(mldsa_reg_hwif_out),

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
  .normcheck_src_addr_o(normcheck_src_addr),
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

  .lfsr_enable_o(lfsr_enable),
  .lfsr_seed_o(lfsr_seed),

  .error_intr(error_intr),
  .notif_intr(notif_intr)

);

mldsa_sampler_top sampler_top_inst
(
  .clk(clk),
  .rst_b(rst_b),
  .zeroize(zeroize_reg),

  .sampler_mode_i(sampler_mode),
  .sha3_start_i(sha3_start), //start the sha3 engine
  .msg_start_i(msg_start), //start a new message
  .msg_valid_i(msg_valid | decomp_msg_valid), //msg interface valid //FIXME
  .msg_rdy_o(msg_rdy),  //msg interface rdy (~hold)
  .msg_strobe_i(decomp_msg_valid ? '1 : msg_strobe), //msg byte enables //FIXME
  .msg_data_i(decomp_msg_valid ? decomp_msg_data : msg_data), //msg data/ /FIXME

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

assign sampler_ntt_dv[1] = 0; //no sampler interface to secondary ntt

generate
  for (genvar g_inst = 0; g_inst < 2; g_inst++) begin : ntt_gen
    //NTT
    //gasket here, create common interfaces?
    always_comb begin
      mode[g_inst] = '0;
      accumulate[g_inst] = '0;
      sampler_valid[g_inst] = 0;
      sampler_ntt_mode[g_inst] = 0;

      unique case (ntt_mode[g_inst]) inside
        MLDSA_NTT_NONE: begin
        end
        MLDSA_NTT: begin
          mode[g_inst] = ct;
        end
        MLDSA_INTT: begin
          mode[g_inst] = gs;
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
        end
        MLDSA_PWM_ACCUM: begin
          mode[g_inst] = pwm;
          accumulate[g_inst] = 1;
          sampler_valid[g_inst] = 1;
        end
        MLDSA_PWA: begin
          mode[g_inst] = pwa;
          sampler_valid[g_inst] = 1;
        end
        MLDSA_PWS: begin
          mode[g_inst] = pws;
          sampler_valid[g_inst] = 1;
        end
        default: begin
        end
      endcase 
    end

  ntt_top #(
    .REG_SIZE(REG_SIZE),
    .MLDSA_Q(MLDSA_Q),
    .MLDSA_N(MLDSA_N),
    .MEM_ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH)
  )
  ntt_top_inst0 (
    .clk(clk),
    .reset_n(rst_b),
    .zeroize(zeroize_reg),

    .mode(mode[g_inst]),
    .ntt_enable(ntt_enable[g_inst]),
    .ntt_mem_base_addr(ntt_mem_base_addr[g_inst]),
    .pwo_mem_base_addr(pwo_mem_base_addr[g_inst]),
    .accumulate(accumulate[g_inst]),
    .sampler_valid(sampler_valid[g_inst]),
    //NTT mem IF
    .mem_wr_req(ntt_mem_wr_req[g_inst]),
    .mem_rd_req(ntt_mem_rd_req[g_inst]),
    .mem_wr_data(ntt_mem_wr_data[g_inst]),
    .mem_rd_data(ntt_mem_rd_data[g_inst]),
    //PWM mem IF
    .pwm_a_rd_req(pwm_a_rd_req[g_inst]),
    .pwm_b_rd_req(pwm_b_rd_req[g_inst]),
    .pwm_a_rd_data(pwm_a_rd_data[g_inst]),
    .pwm_b_rd_data(sampler_ntt_mode[g_inst] ? sampler_ntt_data : pwm_b_rd_data[g_inst]),
    .ntt_busy(ntt_busy[g_inst]),
    .ntt_done(ntt_done[g_inst])
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

  .src_base_addr(aux_src0_base_addr[0]),
  .mem_a_rd_req(pwr2rnd_mem_rd_req[0]),
  .mem_rd_data_a(pwr2rnd_mem_rd_data[0]),
  .mem_b_rd_req(pwr2rnd_mem_rd_req[1]),
  .mem_rd_data_b(pwr2rnd_mem_rd_data[1]),

  .pk_t1_wren(pk_t1_wren),
  .pk_t1_wr_addr(pk_t1_wr_addr),
  .pk_t1_wrdata(pk_t1_wrdata),

  .skmem_dest_base_addr(aux_dest_base_addr[0]),
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
  .src_base_addr(aux_src0_base_addr[0]),
  .dest_base_addr(aux_dest_base_addr[0]),
  .hint_src_base_addr(aux_src1_base_addr[0]),

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

  //TODO: check what high level controller requirement is
  .decompose_done(decompose_done),
  .w1_encode_done()
);

skencode
#(
  .MEM_ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH)
)
skencode_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .src_base_addr(aux_src0_base_addr[0]),
  .dest_base_addr(aux_dest_base_addr[0]),

  .skencode_enable(skencode_enable),
  .skencode_done(skencode_done),
  .skencode_error(),

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

  .keymem_src_base_addr(aux_src0_base_addr[1]), 
  .dest_base_addr(aux_dest_base_addr[1]),

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
  .skdecode_error()
);

makehint
makehint_inst
(
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .makehint_enable(makehint_enable),
  .makehint_done(makehint_done),

  .mem_base_addr(aux_src0_base_addr[1]),
  .dest_base_addr('0),

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
  .norm_check_ready(),
  .norm_check_done(normcheck_done),
  
  .mem_base_addr(normcheck_src_addr),
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

  .src_base_addr(aux_src0_base_addr[1]),
  .sigmem_dest_base_addr(aux_dest_base_addr[1]),

  .mem_a_rd_req(sigencode_mem_rd_req[0]),
  .mem_a_rd_data(sigencode_mem_rd_data[0]),
  .mem_b_rd_req(sigencode_mem_rd_req[1]),
  .mem_b_rd_data(sigencode_mem_rd_data[1]),
  
  .sigmem_a_wr_req(sigencode_mem_wr_req),
  .sigmem_a_wr_data(sigencode_mem_wr_data[0]),
  .sigmem_b_wr_req(), //fixme single interface
  .sigmem_b_wr_data(sigencode_mem_wr_data[1])
);

pkdecode 
#(
  .API_ADDR_WIDTH(8) //FIXME
)
pkdecode_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .pkdecode_enable(pkdecode_enable),
  .pkdecode_done(pkdecode_done),

  .src_base_addr('0), //fixme remove - api register reads, no need for base address
  .dest_base_addr(aux_dest_base_addr[0]),

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

  .sigmem_src_base_addr('0), //fixme remove, reads dedicated memory
  .dest_base_addr(aux_dest_base_addr[0]),

  .mem_a_wr_req(sigdecode_z_mem_wr_req[0]),
  .mem_a_wr_data(sigdecode_z_mem_wr_data[0]),
  .mem_b_wr_req(sigdecode_z_mem_wr_req[1]),
  .mem_b_wr_data(sigdecode_z_mem_wr_data[1]),

  .sigmem_a_rd_req(sigdecode_z_mem_rd_req),
  .sigmem_a_rd_data(sigdecode_z_mem_rd_data[0]),
  .sigmem_b_rd_req(), //fixme switch to single interface
  .sigmem_b_rd_data(sigdecode_z_mem_rd_data[1])
);

sigdecode_h
sigdecode_h_inst (
  .clk(clk),
  .reset_n(rst_b),
  .zeroize(zeroize_reg),

  .sigdecode_h_enable(sigdecode_h_enable),
  .sigdecode_h_done(sigdecode_h_done),

  .dest_base_addr(aux_dest_base_addr[0]),

  .encoded_h_i(signature_h),
  .mem_wr_req(sigdecode_h_mem_wr_req),
  .mem_wr_data(sigdecode_h_mem_wr_data),

  .sigdecode_h_error(sigdecode_h_invalid)
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

//w1 memory
`ABR_MEM_TEST(512, 4)
mldsa_w1_mem_inst
(
  .clk_i(clk),
  .we_i(w1_mem_wr_req.rd_wr_en == RW_WRITE),
  .waddr_i(w1_mem_wr_req.addr[8:0]), //FIXME params
  .wdata_i(w1_mem_wr_data),
  .re_i(w1_mem_rd_req.rd_wr_en == RW_READ),
  .raddr_i(w1_mem_rd_req.addr[8:0]),
  .rdata_o(w1_mem_rd_data)
);

//Decode request to sample in ball memory
logic [1:0] sib_mem_re, sib_mem_re_f;
always_comb sib_mem_re[0] = (ntt_mem_rd_req[0].rd_wr_en == RW_READ) & (ntt_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == 3'b100);
always_comb sib_mem_re[1] = (ntt_mem_rd_req[1].rd_wr_en == RW_READ) & (ntt_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == 3'b100);

always_comb sib_mem_rd_req.addr = sib_mem_re[0] ? ntt_mem_rd_req[0].addr :
                                  sib_mem_re[1] ? ntt_mem_rd_req[1].addr : '0;
always_comb sib_mem_rd_req.rd_wr_en = sib_mem_re[0] ? ntt_mem_rd_req[0].rd_wr_en : 
                                      sib_mem_re[1] ? ntt_mem_rd_req[1].rd_wr_en : RW_IDLE;


//MUX memory accesses
logic [3:1] mldsa_mem_re;
logic [3:1][MLDSA_MEM_ADDR_WIDTH-4:0] mldsa_mem_raddr;
logic [3:1][MLDSA_MEM_DATA_WIDTH-1:0] mldsa_mem_rdata;
logic [1:0] mldsa_mem_re0_bank;
logic [1:0][MLDSA_MEM_ADDR_WIDTH-4:0] mldsa_mem_raddr0_bank;
logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] mldsa_mem_rdata0_bank;
logic [3:1] mldsa_mem_we;
logic [3:1][MLDSA_MEM_ADDR_WIDTH-4:0] mldsa_mem_waddr;
logic [3:1][MLDSA_MEM_DATA_WIDTH-1:0] mldsa_mem_wdata;
logic [1:0] mldsa_mem_we0_bank;
logic [1:0][MLDSA_MEM_ADDR_WIDTH-4:0] mldsa_mem_waddr0_bank;
logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] mldsa_mem_wdata0_bank;

//FIXME common memory ports to make muxing easier
//this is better - common interfaces will help clean this up further

logic [3:1] sampler_mem_we;
logic [1:0][3:1] ntt_mem_we;
logic [3:1] decomp_mem_we;
logic [1:0] sampler_mem_we0_bank;
logic [1:0][1:0] ntt_mem_we0_bank;
logic [1:0] decomp_mem_we0_bank;
logic [1:0] skdecode_mem_we0_bank;
logic [1:0] pkdecode_mem_we0_bank;
logic [1:0] sigdecode_z_mem_we0_bank;
logic [3:1] sigdecode_h_mem_we;
logic [1:0] sigdecode_h_mem_we0_bank;

logic [1:0][3:1] ntt_mem_re,ntt_mem_re_f;
logic [1:0][3:1] pwo_a_mem_re,pwo_a_mem_re_f;
logic [1:0][3:1] pwo_b_mem_re,pwo_b_mem_re_f;
logic [1:0][3:1] decomp_mem_re,decomp_mem_re_f;
logic [3:1] normcheck_mem_re,normcheck_mem_re_f;
logic [3:1] makehint_mem_re;
logic [1:0][1:0] ntt_mem_re0_bank,ntt_mem_re0_bank_f;
logic [1:0][1:0] pwo_a_mem_re0_bank,pwo_a_mem_re0_bank_f;
logic [1:0][1:0] pwo_b_mem_re0_bank,pwo_b_mem_re0_bank_f;
logic [1:0][1:0] decomp_mem_re0_bank,decomp_mem_re0_bank_f;
logic [1:0] normcheck_mem_re0_bank,normcheck_mem_re0_bank_f;
logic [1:0] skencode_mem_re0_bank;
logic [1:0] sigencode_mem_re0_bank;
logic [1:0] pwr2rnd_mem_re0_bank;

//Write Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    if (i == 0) begin
      for (int bank = 0; bank < 2; bank++) begin
        sampler_mem_we0_bank[bank] = sampler_mem_dv & (sampler_mem_addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (sampler_mem_addr[0] == bank);
        ntt_mem_we0_bank[0][bank] = (ntt_mem_wr_req[0].rd_wr_en == RW_WRITE) & (ntt_mem_wr_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (ntt_mem_wr_req[0].addr[0] == bank);
        ntt_mem_we0_bank[1][bank] = (ntt_mem_wr_req[1].rd_wr_en == RW_WRITE) & (ntt_mem_wr_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (ntt_mem_wr_req[1].addr[0] == bank);
        decomp_mem_we0_bank[bank] = (decomp_mem_wr_req.rd_wr_en == RW_WRITE) & (decomp_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_wr_req.addr[0] == bank);
        sigdecode_h_mem_we0_bank[bank] = (sigdecode_h_mem_wr_req.rd_wr_en == RW_WRITE) & (sigdecode_h_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (sigdecode_h_mem_wr_req.addr[0] == bank);
        skdecode_mem_we0_bank[bank] = (skdecode_mem_wr_req[bank].rd_wr_en == RW_WRITE);
        pkdecode_mem_we0_bank[bank] = (pkdecode_mem_wr_req[bank].rd_wr_en == RW_WRITE);
        sigdecode_z_mem_we0_bank[bank] = (sigdecode_z_mem_wr_req[bank].rd_wr_en == RW_WRITE);

        mldsa_mem_we0_bank[bank] = sampler_mem_we0_bank[bank] | ntt_mem_we0_bank[0][bank] | ntt_mem_we0_bank[1][bank] | 
                                 decomp_mem_we0_bank[bank] | skdecode_mem_we0_bank[bank] | pkdecode_mem_we0_bank[bank] |
                                 sigdecode_h_mem_we0_bank[bank] | sigdecode_z_mem_we0_bank[bank] ;

        mldsa_mem_waddr0_bank[bank] = ({MLDSA_MEM_ADDR_WIDTH-3{sampler_mem_we0_bank[bank] }} & sampler_mem_addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_we0_bank[0][bank]  }} & ntt_mem_wr_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_we0_bank[1][bank]  }} & ntt_mem_wr_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_we0_bank[bank]  }} & decomp_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{sigdecode_h_mem_we0_bank[bank]  }} & sigdecode_h_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{skdecode_mem_we0_bank[bank]}} & skdecode_mem_wr_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pkdecode_mem_we0_bank[bank]}} & pkdecode_mem_wr_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{sigdecode_z_mem_we0_bank[bank]}} & sigdecode_z_mem_wr_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0]);

        mldsa_mem_wdata0_bank[bank] = ({MLDSA_MEM_DATA_WIDTH{sampler_mem_we0_bank[bank] }} & sampler_mem_data) |
                                    ({MLDSA_MEM_DATA_WIDTH{ntt_mem_we0_bank[0][bank]  }} & ntt_mem_wr_data[0]) |
                                    ({MLDSA_MEM_DATA_WIDTH{ntt_mem_we0_bank[1][bank]  }} & ntt_mem_wr_data[1]) |
                                    ({MLDSA_MEM_DATA_WIDTH{decomp_mem_we0_bank[bank]  }} & decomp_mem_wr_data) |
                                    ({MLDSA_MEM_DATA_WIDTH{sigdecode_h_mem_we0_bank[bank]}} & sigdecode_h_mem_wr_data) |
                                    ({MLDSA_MEM_DATA_WIDTH{skdecode_mem_we0_bank[bank]}} & skdecode_mem_wr_data[bank]) |
                                    ({MLDSA_MEM_DATA_WIDTH{pkdecode_mem_we0_bank[bank]}} & pkdecode_mem_wr_data[bank]) |
                                    ({MLDSA_MEM_DATA_WIDTH{sigdecode_z_mem_we0_bank[bank]}} & sigdecode_z_mem_wr_data[bank]);
      end
    end else begin
      sampler_mem_we[i] = sampler_mem_dv & (sampler_mem_addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      ntt_mem_we[0][i] = (ntt_mem_wr_req[0].rd_wr_en == RW_WRITE) & (ntt_mem_wr_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      ntt_mem_we[1][i] = (ntt_mem_wr_req[1].rd_wr_en == RW_WRITE) & (ntt_mem_wr_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      decomp_mem_we[i] = (decomp_mem_wr_req.rd_wr_en == RW_WRITE) & (decomp_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      sigdecode_h_mem_we[i] = (sigdecode_h_mem_wr_req.rd_wr_en == RW_WRITE) & (sigdecode_h_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
  
      mldsa_mem_we[i] = sampler_mem_we[i] | ntt_mem_we[0][i] | ntt_mem_we[1][i] | decomp_mem_we[i] | sigdecode_h_mem_we[i];
      mldsa_mem_waddr[i] = ({MLDSA_MEM_ADDR_WIDTH-3{sampler_mem_we[i]}} & sampler_mem_addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_we[0][i]}}  & ntt_mem_wr_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_we[1][i]}}  & ntt_mem_wr_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_we[i]}}  & decomp_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{sigdecode_h_mem_we[i]}} & sigdecode_h_mem_wr_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]);

      mldsa_mem_wdata[i] = ({MLDSA_MEM_DATA_WIDTH{sampler_mem_we[i]}}     & sampler_mem_data) |
                         ({MLDSA_MEM_DATA_WIDTH{ntt_mem_we[0][i]}}      & ntt_mem_wr_data[0]) |
                         ({MLDSA_MEM_DATA_WIDTH{ntt_mem_we[1][i]}}      & ntt_mem_wr_data[1]) |
                         ({MLDSA_MEM_DATA_WIDTH{decomp_mem_we[i]}}      & decomp_mem_wr_data) |
                         ({MLDSA_MEM_DATA_WIDTH{sigdecode_h_mem_we[i]}} & sigdecode_h_mem_wr_data);
    end
  end
end

//Read Muxes
always_comb begin
  for (int i = 0; i < 4; i++) begin
    if (i == 0) begin
      for (int bank = 0; bank < 2; bank++) begin
        ntt_mem_re0_bank[0][bank]   = (ntt_mem_rd_req[0].rd_wr_en == RW_READ) & (ntt_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (ntt_mem_rd_req[0].addr[0] == bank);
        pwo_a_mem_re0_bank[0][bank] = (pwm_a_rd_req[0].rd_wr_en == RW_READ) & (pwm_a_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_a_rd_req[0].addr[0] == bank);
        pwo_b_mem_re0_bank[0][bank] = ~sampler_ntt_dv & (pwm_b_rd_req[0].rd_wr_en == RW_READ) & (pwm_b_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_b_rd_req[0].addr[0] == bank);
    
        ntt_mem_re0_bank[1][bank]   = (ntt_mem_rd_req[1].rd_wr_en == RW_READ) & (ntt_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (ntt_mem_rd_req[1].addr[0] == bank);
        pwo_a_mem_re0_bank[1][bank] = (pwm_a_rd_req[1].rd_wr_en == RW_READ) & (pwm_a_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_a_rd_req[1].addr[0] == bank);
        pwo_b_mem_re0_bank[1][bank] = (pwm_b_rd_req[1].rd_wr_en == RW_READ) & (pwm_b_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (pwm_b_rd_req[1].addr[0] == bank);
    
        decomp_mem_re0_bank[0][bank]   = (decomp_mem_rd_req[0].rd_wr_en == RW_READ) & (decomp_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_rd_req[0].addr[0] == bank);
        decomp_mem_re0_bank[1][bank]   = (decomp_mem_rd_req[1].rd_wr_en == RW_READ) & (decomp_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (decomp_mem_rd_req[1].addr[0] == bank);
        normcheck_mem_re0_bank[bank] = (normcheck_mem_rd_req.rd_wr_en == RW_READ) & (normcheck_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]) & (normcheck_mem_rd_req.addr[0] == bank);
        skencode_mem_re0_bank[bank] = (skencode_mem_rd_req[bank].rd_wr_en == RW_READ);
        sigencode_mem_re0_bank[bank] = (sigencode_mem_rd_req[bank].rd_wr_en == RW_READ);
        pwr2rnd_mem_re0_bank[bank] = (pwr2rnd_mem_rd_req[bank].rd_wr_en == RW_READ);

        mldsa_mem_re0_bank[bank] = ntt_mem_re0_bank[0][bank] | pwo_a_mem_re0_bank[0][bank] | pwo_b_mem_re0_bank[0][bank] |
                                 ntt_mem_re0_bank[1][bank] | pwo_a_mem_re0_bank[1][bank] | pwo_b_mem_re0_bank[1][bank] |
                                 decomp_mem_re0_bank[0][bank] | decomp_mem_re0_bank[1][bank] | 
                                 skencode_mem_re0_bank[bank] | normcheck_mem_re0_bank[bank] |
                                 sigencode_mem_re0_bank[bank] | pwr2rnd_mem_re0_bank[bank];
        mldsa_mem_raddr0_bank[bank] = ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_re0_bank[0][bank]}}    & ntt_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pwo_a_mem_re0_bank[0][bank]}} & pwm_a_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pwo_b_mem_re0_bank[0][bank]}} & pwm_b_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_re0_bank[1][bank]}}   & ntt_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pwo_a_mem_re0_bank[1][bank]}} & pwm_a_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pwo_b_mem_re0_bank[1][bank]}} & pwm_b_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_re0_bank[0][bank]}}   & decomp_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_re0_bank[1][bank]}}   & decomp_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{skencode_mem_re0_bank[bank]}} & skencode_mem_rd_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{normcheck_mem_re0_bank[bank]}} & normcheck_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                                    ({MLDSA_MEM_ADDR_WIDTH-3{sigencode_mem_re0_bank[bank]}} & sigencode_mem_rd_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0])|
                                    ({MLDSA_MEM_ADDR_WIDTH-3{pwr2rnd_mem_re0_bank[bank]}} & pwr2rnd_mem_rd_req[bank].addr[MLDSA_MEM_ADDR_WIDTH-4:0]);
      end
    end else begin
      ntt_mem_re[0][i]   = (ntt_mem_rd_req[0].rd_wr_en == RW_READ) & (ntt_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_a_mem_re[0][i] = (pwm_a_rd_req[0].rd_wr_en == RW_READ) & (pwm_a_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_b_mem_re[0][i] = ~sampler_ntt_dv & (pwm_b_rd_req[0].rd_wr_en == RW_READ) & (pwm_b_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
  
      ntt_mem_re[1][i]   = (ntt_mem_rd_req[1].rd_wr_en == RW_READ) & (ntt_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_a_mem_re[1][i] = (pwm_a_rd_req[1].rd_wr_en == RW_READ) & (pwm_a_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      pwo_b_mem_re[1][i] = (pwm_b_rd_req[1].rd_wr_en == RW_READ) & (pwm_b_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
  
      decomp_mem_re[0][i]   = (decomp_mem_rd_req[0].rd_wr_en == RW_READ) & (decomp_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      decomp_mem_re[1][i]   = (decomp_mem_rd_req[1].rd_wr_en == RW_READ) & (decomp_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      normcheck_mem_re[i] = (normcheck_mem_rd_req.rd_wr_en == RW_READ) & (normcheck_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);
      makehint_mem_re[i] = (makehint_mem_rd_req.rd_wr_en == RW_READ) & (makehint_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-1:MLDSA_MEM_ADDR_WIDTH-3] == i[2:0]);

      mldsa_mem_re[i] = ntt_mem_re[0][i] | pwo_a_mem_re[0][i] | pwo_b_mem_re[0][i] |
                      ntt_mem_re[1][i] | pwo_a_mem_re[1][i] | pwo_b_mem_re[1][i] |
                      decomp_mem_re[0][i] | decomp_mem_re[1][i] | 
                      normcheck_mem_re[i] | makehint_mem_re[i];
      mldsa_mem_raddr[i] = ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_re[0][i]}}   & ntt_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                         ({MLDSA_MEM_ADDR_WIDTH-3{pwo_a_mem_re[0][i]}} & pwm_a_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{pwo_b_mem_re[0][i]}} & pwm_b_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{ntt_mem_re[1][i]}}   & ntt_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0])   |
                         ({MLDSA_MEM_ADDR_WIDTH-3{pwo_a_mem_re[1][i]}} & pwm_a_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{pwo_b_mem_re[1][i]}} & pwm_b_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_re[0][i]}}   & decomp_mem_rd_req[0].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{decomp_mem_re[1][i]}}   & decomp_mem_rd_req[1].addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{normcheck_mem_re[i]}} & normcheck_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]) |
                         ({MLDSA_MEM_ADDR_WIDTH-3{makehint_mem_re[i]}} & makehint_mem_rd_req.addr[MLDSA_MEM_ADDR_WIDTH-4:0]);
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
    ntt_mem_re0_bank_f <= 0;
    pwo_a_mem_re0_bank_f <= 0;
    pwo_b_mem_re0_bank_f <= 0;
    decomp_mem_re0_bank_f <= 0;
    normcheck_mem_re0_bank_f <= 0;
    sib_mem_re_f <= 0;
  end
  else begin
    ntt_mem_re_f <= ntt_mem_re;
    pwo_a_mem_re_f<= pwo_a_mem_re;
    pwo_b_mem_re_f <= pwo_b_mem_re;
    decomp_mem_re_f <= decomp_mem_re;
    normcheck_mem_re_f <= normcheck_mem_re;
    ntt_mem_re0_bank_f <= ntt_mem_re0_bank;
    pwo_a_mem_re0_bank_f <= pwo_a_mem_re0_bank;
    pwo_b_mem_re0_bank_f <= pwo_b_mem_re0_bank;
    decomp_mem_re0_bank_f <= decomp_mem_re0_bank;
    normcheck_mem_re0_bank_f <= normcheck_mem_re0_bank;
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

  for (int i = 0; i < 4; i++) begin
    if (i == 0) begin
      for (int bank = 0; bank < 2; bank++) begin
        for (int j = 0; j < 2; j++) begin
          ntt_mem_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{ntt_mem_re0_bank_f[j][bank]}} & mldsa_mem_rdata0_bank[bank]);
          pwm_a_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{pwo_a_mem_re0_bank_f[j][bank]}} & mldsa_mem_rdata0_bank[bank]);
          pwm_b_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{pwo_b_mem_re0_bank_f[j][bank]}} & mldsa_mem_rdata0_bank[bank]);
        end
        decomp_mem_rd_data[0] |= ({MLDSA_MEM_DATA_WIDTH{decomp_mem_re0_bank_f[0][bank]}} & mldsa_mem_rdata0_bank[bank]);
        decomp_mem_rd_data[1] |= ({MLDSA_MEM_DATA_WIDTH{decomp_mem_re0_bank_f[1][bank]}} & mldsa_mem_rdata0_bank[bank]);
        normcheck_mem_rd_data |= ({MLDSA_MEM_DATA_WIDTH{normcheck_mem_re0_bank_f[bank]}} & mldsa_mem_rdata0_bank[bank]);
      end
    end else begin
      for (int j = 0; j < 2; j++) begin
        ntt_mem_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{ntt_mem_re_f[j][i]}} & mldsa_mem_rdata[i]);
        pwm_a_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{pwo_a_mem_re_f[j][i]}} & mldsa_mem_rdata[i]);
        pwm_b_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{pwo_b_mem_re_f[j][i]}} & mldsa_mem_rdata[i]);
      end
      decomp_mem_rd_data[0] |= ({MLDSA_MEM_DATA_WIDTH{decomp_mem_re_f[0][i]}} & mldsa_mem_rdata[i]);
      decomp_mem_rd_data[1] |= ({MLDSA_MEM_DATA_WIDTH{decomp_mem_re_f[1][i]}} & mldsa_mem_rdata[i]);
      normcheck_mem_rd_data |= ({MLDSA_MEM_DATA_WIDTH{normcheck_mem_re_f[i]}} & mldsa_mem_rdata[i]);
    end
  end
  for (int j = 0; j < 2; j++) begin
    ntt_mem_rd_data[j] |= ({MLDSA_MEM_DATA_WIDTH{sib_mem_re_f[j]}} & sib_mem_rd_data);
  end
end

always_comb skencode_mem_rd_data = mldsa_mem_rdata0_bank;
always_comb makehint_mem_rd_data = mldsa_mem_rdata[1];
always_comb sigencode_mem_rd_data = mldsa_mem_rdata0_bank;
always_comb pwr2rnd_mem_rd_data = mldsa_mem_rdata0_bank;

`ABR_MEM(MLDSA_MEM_INST0_DEPTH/2,MLDSA_MEM_DATA_WIDTH)
mldsa_ram_inst0_bank0
(
  .clk_i(clk),
  .we_i(mldsa_mem_we0_bank[0]),
  .waddr_i(mldsa_mem_waddr0_bank[0][MLDSA_MEM_INST0_ADDR_W-1:1]),
  .wdata_i(mldsa_mem_wdata0_bank[0]),
  .re_i(mldsa_mem_re0_bank[0]),
  .raddr_i(mldsa_mem_raddr0_bank[0][MLDSA_MEM_INST0_ADDR_W-1:1]),
  .rdata_o(mldsa_mem_rdata0_bank[0])
);
`ABR_MEM(MLDSA_MEM_INST0_DEPTH/2,MLDSA_MEM_DATA_WIDTH)
mldsa_ram_inst0_bank1
(
  .clk_i(clk),
  .we_i(mldsa_mem_we0_bank[1]),
  .waddr_i(mldsa_mem_waddr0_bank[1][MLDSA_MEM_INST0_ADDR_W-1:1]),
  .wdata_i(mldsa_mem_wdata0_bank[1]),
  .re_i(mldsa_mem_re0_bank[1]),
  .raddr_i(mldsa_mem_raddr0_bank[1][MLDSA_MEM_INST0_ADDR_W-1:1]),
  .rdata_o(mldsa_mem_rdata0_bank[1])
);

`ABR_MEM(MLDSA_MEM_INST1_DEPTH,MLDSA_MEM_DATA_WIDTH)
mldsa_ram_inst1
(
  .clk_i(clk),
  .we_i(mldsa_mem_we[1]),
  .waddr_i(mldsa_mem_waddr[1][MLDSA_MEM_INST1_ADDR_W-1:0]),
  .wdata_i(mldsa_mem_wdata[1]),
  .re_i(mldsa_mem_re[1]),
  .raddr_i(mldsa_mem_raddr[1][MLDSA_MEM_INST1_ADDR_W-1:0]),
  .rdata_o(mldsa_mem_rdata[1])
);

`ABR_MEM(MLDSA_MEM_INST2_DEPTH,MLDSA_MEM_DATA_WIDTH)
mldsa_ram_inst2
(
  .clk_i(clk),
  .we_i(mldsa_mem_we[2]),
  .waddr_i(mldsa_mem_waddr[2][MLDSA_MEM_INST2_ADDR_W-1:0]),
  .wdata_i(mldsa_mem_wdata[2]),
  .re_i(mldsa_mem_re[2]),
  .raddr_i(mldsa_mem_raddr[2][MLDSA_MEM_INST2_ADDR_W-1:0]),
  .rdata_o(mldsa_mem_rdata[2])
);

`ABR_MEM(MLDSA_MEM_INST3_DEPTH,MLDSA_MEM_DATA_WIDTH)
mldsa_ram_inst3
(
  .clk_i(clk),
  .we_i(mldsa_mem_we[3]),
  .waddr_i(mldsa_mem_waddr[3][MLDSA_MEM_INST3_ADDR_W-1:0]),
  .wdata_i(mldsa_mem_wdata[3]),
  .re_i(mldsa_mem_re[3]),
  .raddr_i(mldsa_mem_raddr[3][MLDSA_MEM_INST3_ADDR_W-1:0]),
  .rdata_o(mldsa_mem_rdata[3])
);




`ABR_ASSERT_MUTEX(ERR_MEM_0_0_RD_ACCESS_MUTEX, {ntt_mem_re0_bank[0][0],pwo_a_mem_re0_bank[0][0],pwo_b_mem_re0_bank[0][0],ntt_mem_re0_bank[1][0],
                                                pwo_a_mem_re0_bank[1][0],pwo_b_mem_re0_bank[1][0],decomp_mem_re0_bank[0][0],decomp_mem_re0_bank[1][0],
                                                skencode_mem_re0_bank[0], normcheck_mem_re0_bank[0], sigencode_mem_re0_bank[0], pwr2rnd_mem_re0_bank[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_0_1_RD_ACCESS_MUTEX, {ntt_mem_re0_bank[0][1],pwo_a_mem_re0_bank[0][1],pwo_b_mem_re0_bank[0][1],ntt_mem_re0_bank[1][1],
                                                pwo_a_mem_re0_bank[1][1],pwo_b_mem_re0_bank[1][1],decomp_mem_re0_bank[0][1],decomp_mem_re0_bank[1][1], 
                                                skencode_mem_re0_bank[1],normcheck_mem_re0_bank[1],sigencode_mem_re0_bank[1], pwr2rnd_mem_re0_bank[1]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_1_RD_ACCESS_MUTEX, {ntt_mem_re[0][1],pwo_a_mem_re[0][1],pwo_b_mem_re[0][1],ntt_mem_re[1][1],pwo_a_mem_re[1][1],pwo_b_mem_re[1][1],
                                                normcheck_mem_re[1], decomp_mem_re[0][1],decomp_mem_re[1][1],makehint_mem_re[1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_RD_ACCESS_MUTEX, {ntt_mem_re[0][2],pwo_a_mem_re[0][2],pwo_b_mem_re[0][2],ntt_mem_re[1][2],pwo_a_mem_re[1][2],pwo_b_mem_re[1][2],
                                                normcheck_mem_re[2], decomp_mem_re[0][2],decomp_mem_re[1][2],makehint_mem_re[2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_RD_ACCESS_MUTEX, {ntt_mem_re[0][3],pwo_a_mem_re[0][3],pwo_b_mem_re[0][3],ntt_mem_re[1][3],pwo_a_mem_re[1][3],pwo_b_mem_re[1][3],
                                                normcheck_mem_re[3], decomp_mem_re[0][3],decomp_mem_re[1][3],makehint_mem_re[3]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_0_0_WR_ACCESS_MUTEX, {sampler_mem_we0_bank[0],ntt_mem_we0_bank[0][0],ntt_mem_we0_bank[1][0],decomp_mem_we0_bank[0],
                                                skdecode_mem_we0_bank[0], pkdecode_mem_we0_bank[0], sigdecode_h_mem_we0_bank[0],
                                                sigdecode_z_mem_we0_bank[0]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_0_1_WR_ACCESS_MUTEX, {sampler_mem_we0_bank[1],ntt_mem_we0_bank[0][1],ntt_mem_we0_bank[1][1],decomp_mem_we0_bank[1],
                                                skdecode_mem_we0_bank[1], pkdecode_mem_we0_bank[1], sigdecode_h_mem_we0_bank[1],
                                                sigdecode_z_mem_we0_bank[1]}, clk, !rst_b)

`ABR_ASSERT_MUTEX(ERR_MEM_1_WR_ACCESS_MUTEX, {sampler_mem_we[1],ntt_mem_we[0][1],ntt_mem_we[1][1],decomp_mem_we[1], sigdecode_h_mem_we[1]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_2_WR_ACCESS_MUTEX, {sampler_mem_we[2],ntt_mem_we[0][2],ntt_mem_we[1][2],decomp_mem_we[2], sigdecode_h_mem_we[2]}, clk, !rst_b)
`ABR_ASSERT_MUTEX(ERR_MEM_3_WR_ACCESS_MUTEX, {sampler_mem_we[3],ntt_mem_we[0][3],ntt_mem_we[1][3],decomp_mem_we[3], sigdecode_h_mem_we[3]}, clk, !rst_b)

`ABR_ASSERT_KNOWN(ERR_MEM_0_0_WDATA_X, {mldsa_mem_wdata0_bank[0]}, clk, !rst_b, mldsa_mem_we0_bank[0])
`ABR_ASSERT_KNOWN(ERR_MEM_0_1_WDATA_X, {mldsa_mem_wdata0_bank[1]}, clk, !rst_b, mldsa_mem_we0_bank[1])
`ABR_ASSERT_KNOWN(ERR_MEM_1_WDATA_X, {mldsa_mem_wdata[1]}, clk, !rst_b, mldsa_mem_we[1])
`ABR_ASSERT_KNOWN(ERR_MEM_2_WDATA_X, {mldsa_mem_wdata[2]}, clk, !rst_b, mldsa_mem_we[2])
`ABR_ASSERT_KNOWN(ERR_MEM_3_WDATA_X, {mldsa_mem_wdata[3]}, clk, !rst_b, mldsa_mem_we[3])

`ABR_ASSERT_KNOWN(ERR_MEM_0_RDATA_X, {ntt_mem_rd_data}, clk, !rst_b)
`ABR_ASSERT_KNOWN(ERR_MEM_1_RDATA_X, {pwm_a_rd_data}, clk, !rst_b)
`ABR_ASSERT_KNOWN(ERR_MEM_2_RDATA_X, {pwm_b_rd_data}, clk, !rst_b)


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