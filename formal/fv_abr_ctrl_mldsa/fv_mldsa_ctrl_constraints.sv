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


module fv_mldsa_ctrl_constraints 
    import mldsa_reg_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_sampler_pkg::*;
    import mldsa_ctrl_pkg::*;
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    // Parameters
    parameter ADAMSBRIDGE_CNTRL_RDY_DELAY       = 1,
    parameter ADAMSBRIDGE_AUX_DLY               = 2,
    parameter ADAMSBRIDGE_BUSY_CNTR             = 2,
    parameter AHB_ADDR_WIDTH                    = 32,
    parameter AHB_DATA_WIDTH                    = 64,
    parameter CLIENT_DATA_WIDTH                 = 32
)(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic                                                         pi_clk,
    input logic                                                         pi_rst_b,
    input logic                                                         po_zeroize,

    input mldsa_reg__in_t                                               po_abr_reg_hwif_in_o,
    input mldsa_reg__out_t                                              pi_abr_reg_hwif_out_i,

    //sampler interface
    input mldsa_sampler_mode_e                                          po_sampler_mode_o,
    input logic                                                         po_sha3_start_o,
    input logic                                                         po_msg_start_o,
    input logic                                                         po_msg_valid_o,
    input logic                                                         pi_msg_rdy_i,
    input logic [MsgStrbW-1:0]                                          po_msg_strobe_o,
    input logic [MsgWidth-1:0]                                          po_msg_data_o[Sha3Share],
    input logic                                                         po_sampler_start_o,

    input logic                                                         pi_sampler_busy_i,
    input logic                                                         pi_sampler_state_dv_i,
    input logic [abr_sha3_pkg::StateW-1:0]                              pi_sampler_state_data_i [Sha3Share],

    input logic [MLDSA_MEM_ADDR_WIDTH-1:0]                              po_dest_base_addr_o,

    //ntt interfaces
    input logic [1:0]                                                   po_ntt_enable_o,
    input mldsa_ntt_mode_e [1:0]                                        po_ntt_mode_o,
    input ntt_mem_addr_t [1:0]                                          po_ntt_mem_base_addr_o,
    input pwo_mem_addr_t [1:0]                                          po_pwo_mem_base_addr_o,
    input logic [1:0]                                                   pi_ntt_busy_i,

    //aux interfaces
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0]                         po_aux_src0_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0]                         po_aux_src1_base_addr_o,
    input logic [1:0][MLDSA_MEM_ADDR_WIDTH-1:0]                         po_aux_dest_base_addr_o,

    input logic                                                         po_power2round_enable_o,
    input mem_if_t [1:0]                                                pi_pwr2rnd_keymem_if_i,
    input logic [1:0] [DATA_WIDTH-1:0]                                  pi_pwr2rnd_wr_data_i,
    input logic                                                         pi_pk_t1_wren_i,
    input logic [7:0][9:0]                                              pi_pk_t1_wrdata_i,
    input logic [7:0]                                                   pi_pk_t1_wr_addr_i,
    input logic                                                         pi_power2round_done_i,

    input logic                                                         po_decompose_enable_o,
    input logic                                                         po_decompose_mode_o,
    input logic                                                         pi_decompose_done_i,

    input logic                                                         po_skencode_enable_o,
    input mem_if_t                                                      pi_skencode_keymem_if_i,
    input logic [DATA_WIDTH-1:0]                                        pi_skencode_wr_data_i,
    input logic                                                         pi_skencode_done_i,

    input logic                                                         po_skdecode_enable_o,
    input mem_if_t [1:0]                                                pi_skdecode_keymem_if_i,
    input logic [1:0][DATA_WIDTH-1:0]                                   po_skdecode_rd_data_o,
    input logic                                                         pi_skdecode_done_i,
     input logic                                                        pi_skdecode_error_i,

    input logic                                                         po_makehint_enable_o,
    input logic                                                         pi_makehint_invalid_i,
    input logic                                                         pi_makehint_done_i,
    input logic                                                         pi_makehint_reg_wren_i,
    input logic [3:0][7:0]                                              pi_makehint_reg_wrdata_i,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0]                              pi_makehint_reg_wr_addr_i,

    input logic                                                         po_normcheck_enable_o,
    input logic [1:0]                                                   po_normcheck_mode_o,
    input logic [MLDSA_MEM_ADDR_WIDTH-1:0]                              po_normcheck_src_addr_o,
    input logic                                                         pi_normcheck_invalid_i,
    input logic                                                         pi_normcheck_done_i,

    input logic                                                         po_sigencode_enable_o,
    input mem_if_t                                                      pi_sigencode_wr_req_i,
    input logic [1:0][3:0][19:0]                                        pi_sigencode_wr_data_i,
    input logic                                                         pi_sigencode_done_i,

    input logic                                                         po_pkdecode_enable_o,
    input logic [7:0]                                                   pi_pkdecode_rd_addr_i,
    input logic [7:0][T1_COEFF_W-1:0]                                   po_pkdecode_rd_data_o,
    input logic                                                         pi_pkdecode_done_i,


    input logic                                                         po_sigdecode_h_enable_o, 
    input logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0]                  po_signature_h_o,
    input logic                                                         pi_sigdecode_h_invalid_i,
    input logic                                                         pi_sigdecode_h_done_i,

    input logic                                                         po_sigdecode_z_enable_o, 
    input mem_if_t                                                      pi_sigdecode_z_rd_req_i,
    input logic [1:0][3:0][19:0]                                        po_sigdecode_z_rd_data_o,
    input logic                                                         pi_sigdecode_z_done_i,

    input logic                                                         po_lfsr_enable_o,
    input logic [1:0][LFSR_W-1:0]                                       po_lfsr_seed_o,
    input logic                                                         po_sk_bank0_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                                po_sk_bank0_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                                        po_sk_bank0_mem_if_wdata_i,
    input logic                                                         po_sk_bank0_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                                po_sk_bank0_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                                        pi_sk_bank0_mem_if_rdata_o,
    input logic                                                         po_sk_bank1_mem_if_we_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                                po_sk_bank1_mem_if_waddr_i,
    input logic [DATA_WIDTH-1:0]                                        po_sk_bank1_mem_if_wdata_i,
    input logic                                                         po_sk_bank1_mem_if_re_i,
    input logic [SK_MEM_BANK_ADDR_W-1:0]                                po_sk_bank1_mem_if_raddr_i,
    input logic [DATA_WIDTH-1:0]                                        pi_sk_bank1_mem_if_rdata_o,

    input logic                                                         po_sig_z_mem_if_we_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                                  po_sig_z_mem_if_waddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                                  po_sig_z_mem_if_wdata_i,
    input logic [SIG_Z_MEM_DATA_W/8-1:0]                                po_sig_z_mem_if_wstrobe_i,
    input logic                                                         po_sig_z_mem_if_re_i,
    input logic [SIG_Z_MEM_ADDR_W-1:0]                                  po_sig_z_mem_if_raddr_i,
    input logic [SIG_Z_MEM_DATA_W-1:0]                                  pi_sig_z_mem_if_rdata_o,
    input logic                                                         po_pk_mem_if_we_i,
    input logic [PK_ADDR_W-1:0]                                         po_pk_mem_if_waddr_i,
    input logic [PK_MEM_DATA_W-1:0]                                     po_pk_mem_if_wdata_i,
    input logic [PK_MEM_DATA_W/8-1:0]                                   po_pk_mem_if_wstrobe_i,
    input logic                                                         po_pk_mem_if_re_i,
    input logic [PK_ADDR_W-1:0]                                         po_pk_mem_if_raddr_i,
    input logic [PK_MEM_DATA_W-1:0]                                     pi_pk_mem_if_rdata_o,

    input mem_if_t                                                      zeroize_mem_o,

    `ifdef CALIPTRA
    // KV interface
    input kv_read_t                                                     kv_read,
    input kv_rd_resp_t                                                  kv_rd_resp,
    //PCR Signing
    input pcr_signing_t                                                 pcr_signing_data,
    `endif

    input logic                                                         pi_debugUnlock_or_scan_mode_switch,
    input logic                                                         po_busy_o,

    //Interrupts
    input logic                                                         po_error_intr,
    input logic                                                         po_notif_intr
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking


    //-------------------------Constrain primary inputs-------------------------------------
     logic sigdecode_z_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_z_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigdecode_z_en <= 1'b0;
            end else if (po_sigdecode_z_enable_o) begin
                sigdecode_z_en <= 1'b1;
            end else if (pi_sigdecode_z_done_i) begin
                sigdecode_z_en <= 1'b0;
            end
        end

      assume_sigdecode_z_done: assume property(
            pi_sigdecode_z_done_i |-> (sigdecode_z_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_sigdecode_z_done_eventually: assume property(
                s_eventually(pi_sigdecode_z_done_i)
            );
    `else
     assume_sigdecode_z_done_in_dly: assume property (
        po_sigdecode_z_enable_o 
        |->
        ## ADAMSBRIDGE_AUX_DLY pi_sigdecode_z_done_i
     );
     `endif

      logic sigdecode_h_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigdecode_h_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigdecode_h_en <= 1'b0;
            end else if (po_sigdecode_h_enable_o) begin
                sigdecode_h_en <= 1'b1;
            end else if (pi_sigdecode_h_done_i) begin
                sigdecode_h_en <= 1'b0;
            end
        end

      assume_sigdecode_h_done: assume property(
            pi_sigdecode_h_done_i |-> (sigdecode_h_en)
        );
     `ifdef EVENTUAL_ASSUME
        assume_sigdecode_h_done_eventually: assume property(
               s_eventually(pi_sigdecode_h_done_i)
           );
         `else

        assume_sigdecode_h_done_in_dly: assume property (
            po_sigdecode_h_enable_o 
            |->
            ## ADAMSBRIDGE_AUX_DLY pi_sigdecode_h_done_i
        );
        `endif
     logic pkdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pkdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                pkdecode_en <= 1'b0;
            end else if (po_pkdecode_enable_o) begin
                pkdecode_en <= 1'b1;
            end else if (pi_pkdecode_done_i) begin
                pkdecode_en <= 1'b0;
            end
        end

      assume_pkdecode_done: assume property(
            pi_pkdecode_done_i |-> (pkdecode_en)
        );
    `ifdef EVENTUAL_ASSUME
      assume_pkdecode_done_eventually: assume property(
            s_eventually(pi_pkdecode_done_i)
        );
    `else
     assume_pkdecode_done_in_dly: assume property (
        po_pkdecode_enable_o 
        |->
        ## ADAMSBRIDGE_AUX_DLY pi_pkdecode_done_i
     );
        `endif

        logic sigencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sigencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                sigencode_en <= 1'b0;
            end else if (po_sigencode_enable_o) begin
                sigencode_en <= 1'b1;
            end else if (pi_sigencode_done_i) begin
                sigencode_en <= 1'b0;
            end
        end

      assume_sigencode_done: assume property(
            pi_sigencode_done_i |-> (sigencode_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_sigencode_done_eventually: assume property(
            s_eventually(pi_sigencode_done_i)
        );
    `else

    assume_sigencode_done_in_dly: assume property (
        po_sigencode_enable_o 
        |->
        ## ADAMSBRIDGE_AUX_DLY pi_sigencode_done_i
     );
    `endif

    logic sampler_enabled;
    logic [ADAMSBRIDGE_BUSY_CNTR-1:0] sampler_busy_cntr;
    always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sampler_enabled_tracking
        if (!pi_rst_b || po_zeroize) begin
            sampler_enabled <= 1'b0;
            sampler_busy_cntr <= '0;
        end else begin
            if (po_sampler_start_o) begin
                sampler_enabled <= 1'b1;
                sampler_busy_cntr <= ADAMSBRIDGE_BUSY_CNTR;
            end else if (sampler_enabled &&( sampler_busy_cntr == '0)) begin
                sampler_enabled <= 1'b0;
            end
            if(sampler_enabled &&( sampler_busy_cntr != '0)) begin
                sampler_busy_cntr <= sampler_busy_cntr -1;
            end
        end
    end

    assume_sampler_busy_i_2: assume property(
        pi_sampler_busy_i == sampler_enabled
    );


    logic [1:0] ntt_enabled;
    logic [1:0][ADAMSBRIDGE_BUSY_CNTR-1:0] ntt_busy_cntr;

    for (genvar i = 0; i < 2; i++) begin
        always_ff @(posedge pi_clk, negedge pi_rst_b) begin : ntt_enabled_tracking
            if (!pi_rst_b) begin
                ntt_enabled[i] <= 1'b0;
                ntt_busy_cntr[i] <= '0;
            end else begin
                if (po_ntt_enable_o[i]) begin
                    ntt_enabled[i] <= 1'b1;
                    ntt_busy_cntr[i] <= ADAMSBRIDGE_BUSY_CNTR;
                end else if (ntt_enabled[i] && ( ntt_busy_cntr[i]=='0)) begin
                    ntt_enabled[i] <= 1'b0;
                end
                if(ntt_enabled[i] && ( ntt_busy_cntr[i]!='0)) begin
                    ntt_busy_cntr[i] <= ntt_busy_cntr[i] -1;
                end
            end
        end

        assume_ntt_busy_i_2: assume property(
           pi_ntt_busy_i[i] == (ntt_enabled[i])
        );


    end

    logic normcheck_enabled;

    always_ff @(posedge pi_clk) begin : normcheck_enabled_tracking
        if (!pi_rst_b) begin
            normcheck_enabled <= 1'b0;
        end else if (po_normcheck_enable_o) begin
            normcheck_enabled <= 1'b1;
        end else if (pi_normcheck_done_i) begin
            normcheck_enabled <= 1'b0;
        end
    end

     assume_normcheck_invalid_i: assume property(
        // disable iff(!pi_rst_b)
        !pi_normcheck_done_i
    |->
        $stable(pi_normcheck_invalid_i)
    );

     assume_normcheck_done: assume property(
            pi_normcheck_done_i |-> (normcheck_enabled )
        );
    `ifdef EVENTUAL_ASSUME
     assume_normcheck_done_eventually: assume property(
            s_eventually(pi_normcheck_done_i)
        );
    `else
    assume_normcheck_done_in_dly: assume property (
        po_normcheck_enable_o
        |->
        ## ADAMSBRIDGE_AUX_DLY pi_normcheck_done_i
     );
     `endif
    logic makehint_enabled;

    always_ff @(posedge pi_clk) begin : makehint_enabled_tracking
        if (!pi_rst_b) begin
            makehint_enabled <= 1'b0;
        end else if (po_makehint_enable_o) begin
            makehint_enabled <= 1'b1;
        end else if (pi_makehint_done_i) begin
            makehint_enabled <= 1'b0;
        end
    end

    assume_makehint_invalid_i: assume property(
        // disable iff(!pi_rst_b)
        !pi_makehint_done_i
    |->
        $stable(pi_makehint_invalid_i)
    );

     assume_makehint_done: assume property(
            pi_makehint_done_i |-> (makehint_enabled )
        );
         assume_makehint_wren: assume property(
            pi_makehint_reg_wren_i |-> (makehint_enabled )
        );

    `ifdef EVENTUAL_ASSUME
     assume_makehint_done_eventually: assume property(
           s_eventually (pi_makehint_done_i)
        );
    `else
     assume_makehint_done_in_dly: assume property (
        po_makehint_enable_o
        |->
        ##ADAMSBRIDGE_AUX_DLY pi_makehint_done_i
     );
    `endif
    assume_makehint_req_addr_range: assume property(
        pi_makehint_reg_wr_addr_i >= 0 && pi_makehint_reg_wr_addr_i < SIGNATURE_H_NUM_DWORDS
    );

   

 logic pwr2rnd_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : pwr2rnd_en_logic
            if (!pi_rst_b || po_zeroize) begin
                pwr2rnd_en <= 1'b0;
            end else if (po_power2round_enable_o) begin
                pwr2rnd_en <= 1'b1;
            end else if (pi_power2round_done_i) begin
                pwr2rnd_en <= 1'b0;
            end
        end

      assume_power2round_done: assume property(
            pi_power2round_done_i |-> (pwr2rnd_en) // dont trigger when enable 
        );

    `ifdef EVENTUAL_ASSUME
      assume_power2round_done_eventually: assume property(
            s_eventually(pi_power2round_done_i) // dont trigger when enable 
        );
    `else

    assume_pwr2rnd_in_2cycles: assume property (
        po_power2round_enable_o 
        |->
        ##ADAMSBRIDGE_AUX_DLY pi_power2round_done_i
    );
    `endif

    assume_pwr2rnd_mem_0: assume property(
        (pi_pwr2rnd_keymem_if_i[0].rd_wr_en == RW_WRITE) |-> (pwr2rnd_en)
    );

     assume_pwr2rnd_mem_1: assume property(
        (pi_pwr2rnd_keymem_if_i[1].rd_wr_en == RW_WRITE) |-> (pwr2rnd_en)
    );
    assume_pwr2rnd_api_wren: assume property(
        (pi_pk_t1_wren_i) |-> (pwr2rnd_en)
    );

 logic decompose_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : decompose_en_logic
            if (!pi_rst_b || po_zeroize) begin
                decompose_en <= 1'b0;
            end else if (po_decompose_enable_o) begin
                decompose_en <= 1'b1;
            end else if (pi_decompose_done_i) begin
                decompose_en <= 1'b0;
            end
        end

      assume_decompose_done: assume property(
            pi_decompose_done_i |-> (decompose_en)
        );
    `ifdef EVENTUAL_ASSUME
      assume_decompose_done_eventually: assume property(
            s_eventually(pi_decompose_done_i)
        );
    `else
    assume_decompose_done_2cycles: assume property (
        po_decompose_enable_o 
        |->
        ##ADAMSBRIDGE_AUX_DLY pi_decompose_done_i
    );
    `endif
   
 logic skencode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skencode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                skencode_en <= 1'b0;
            end else if (po_skencode_enable_o) begin
                skencode_en <= 1'b1;
            end else if (pi_skencode_done_i) begin
                skencode_en <= 1'b0;
            end
        end

      assume_skencode_done: assume property(
            pi_skencode_done_i |-> (skencode_en)
        );
    `ifdef EVENTUAL_ASSUME
        assume_skencode_done_eventually: assume property(
            s_eventually(pi_skencode_done_i)
        );
    `else

    assume_skencode_done_2cycles: assume property (
        po_skencode_enable_o 
        |->
        ##ADAMSBRIDGE_AUX_DLY pi_skencode_done_i
    );
    `endif

    assume_skencode_mem_wr: assume property (
        (pi_skencode_keymem_if_i.rd_wr_en == RW_WRITE) |-> (skencode_en)
    );

 logic skdecode_en;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : skdecode_en_logic
            if (!pi_rst_b || po_zeroize) begin
                skdecode_en <= 1'b0;
            end else if (po_skdecode_enable_o) begin
                skdecode_en <= 1'b1;
            end else if (pi_skdecode_done_i) begin
                skdecode_en <= 1'b0;
            end
        end

      assume_skdecode_done: assume property(
            pi_skdecode_done_i |-> (skdecode_en)
        );

    assume_error_when_enabled_only: assume property(
        pi_skdecode_error_i |-> (skdecode_en)
    );
    `ifdef EVENTUAL_ASSUME
        assume_skdecode_done_eventually: assume property(
            s_eventually(pi_skdecode_done_i)
        );
    `else

    assume_skdecode_done_2cycles: assume property (
        po_skdecode_enable_o 
        |->
        ##ADAMSBRIDGE_AUX_DLY pi_skdecode_done_i
    );
    `endif
        assume_skdecode_mem_0: assume property(
            (pi_skdecode_keymem_if_i[0].rd_wr_en == RW_READ) |-> (skdecode_en)
        );

         assume_skdecode_mem_1: assume property(
            (pi_skdecode_keymem_if_i[1].rd_wr_en == RW_READ) |-> (skdecode_en)
        );

 logic sample_dv;
     always_ff @(posedge pi_clk, negedge pi_rst_b) begin : sample_dv_logic
            if (!pi_rst_b || po_zeroize) begin
                sample_dv <= 1'b0;
            end else if (po_sha3_start_o) begin
                sample_dv <= 1'b1;
            end else if (sampler_busy_cntr==1) begin
                sample_dv <= 1'b0;
            end
        end

      assume_sampler_dv: assume property(
            pi_sampler_state_dv_i |-> (sample_dv && (pi_sampler_busy_i))
        );

    assume_sampler_valid_pulse: assume property(
        pi_sampler_state_dv_i |-> ##1 !pi_sampler_state_dv_i
    );


    assume_sampler_data_stable: assume property(
        !pi_sampler_state_dv_i |-> (pi_sampler_state_data_i[0] == '0)
    );


   
        assume_msg_rdy_eventually: assume property(
            s_eventually(pi_msg_rdy_i)
        );
   
        assume_msg_rdy_: assume property(
            po_msg_valid_o && !pi_msg_rdy_i
            |->
            ##ADAMSBRIDGE_CNTRL_RDY_DELAY pi_msg_rdy_i
        );
    

    // assume_no_op_after_reset: assume property(
    //     $past(!pi_rst_b || mldsa_ctrl.zeroize)
    // |->
    //     $past(pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value ==  3'd0)
    // );

    //-------------------------Constrain abr_reg_hwif_out_i-------------------------------------

    // assume_ctrl_value_i: assume property(
    //     // disable iff(!pi_rst_b)
    //     po_abr_reg_hwif_in_o.MLDSA_CTRL.CTRL.hwclr
    // |->
    //     ##1 pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value == '0
    // );


    assume_hwif_out_value_i_stable: assume property(
        // disable iff(!pi_rst_b)
        !po_abr_reg_hwif_in_o.mldsa_ready
    |->
        ##1 $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.CTRL.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_CTRL.PCR_SIGN.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[0].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[1].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[2].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[3].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[4].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[5].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[6].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[7].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[8].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[9].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[10].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[11].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[12].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[13].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[14].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_ENTROPY[15].ENTROPY.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[0].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[1].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[2].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[3].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[4].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[5].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[6].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SEED[7].SEED.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[0].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[1].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[2].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[3].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[4].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[5].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[6].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_SIGN_RND[7].SIGN_RND.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[0].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[1].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[2].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[3].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[4].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[5].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[6].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[7].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[8].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[9].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[10].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[11].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[12].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[13].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[14].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_MSG[15].MSG.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[0].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[1].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[2].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[3].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[4].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[5].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[6].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[7].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[8].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[9].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[10].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[11].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[12].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[13].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[14].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_VERIFY_RES[15].VERIFY_RES.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[0].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[1].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[2].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[3].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[4].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[5].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[6].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[7].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[8].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[9].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[10].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[11].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[12].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[13].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[14].EXTERNAL_MU.value) &&
            $stable(pi_abr_reg_hwif_out_i.MLDSA_EXTERNAL_MU[15].EXTERNAL_MU.value)
    );


    //-------------------------Constrain memory interface signals-------------------------------------//

    property stable_data_no_req_P(req, data);
        !req
        |=>
        $stable(data)
    ;endproperty

    assume_sk_mem_0_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sk_bank0_mem_if_re_i,pi_sk_bank0_mem_if_rdata_o));
    assume_sk_mem_1_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sk_bank1_mem_if_re_i,pi_sk_bank1_mem_if_rdata_o));
    assume_sig_z_mem_stable_data_no_req_P: assume property(stable_data_no_req_P(po_sig_z_mem_if_re_i,pi_sig_z_mem_if_rdata_o));
    assume_pk_mem_stable_data_no_req_P: assume property(stable_data_no_req_P(po_pk_mem_if_re_i,pi_pk_mem_if_rdata_o));

`ifndef NO_ABSTRACTION
    // Added the snipped signal constraint for the msg_cnt
    logic [MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)] fv_msg_cnt;
    always_ff @( posedge pi_clk, negedge pi_rst_b ) begin : fv_msg_cnt_abs_logic
        if(!pi_rst_b) begin
            fv_msg_cnt <= '0;
        end
        else if(po_zeroize) begin
            fv_msg_cnt <= '0;
        end
        else begin
            if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE) begin
                fv_msg_cnt <= '0;
            end
            else if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && (((fv_msg_cnt == '0)|| (fv_msg_cnt == mldsa_ctrl.prim_instr.length[MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)]-1) || (fv_msg_cnt == mldsa_ctrl.prim_instr.length[MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)])) && pi_msg_rdy_i)) begin
                fv_msg_cnt <= fv_msg_cnt + 1;
            end
            else if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && (fv_msg_cnt == 1) && pi_msg_rdy_i) begin
                fv_msg_cnt <= mldsa_ctrl.prim_instr.length[MLDSA_OPR_WIDTH-1:$clog2(MsgStrbW)]-1;
            end
            else if(mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD && !pi_msg_rdy_i) begin
                fv_msg_cnt <= fv_msg_cnt;
            end
            else begin
                 fv_msg_cnt <= '0;
            end
        end
    end

     property msg_cnt_abstracted_p;
         mldsa_ctrl.msg_cnt == fv_msg_cnt
    ;endproperty
    assume_msg_cnt_abstracted_ASM: assume property(msg_cnt_abstracted_p);

    property abstract_prim_prog_cntr_P;
        (mldsa_ctrl.prim_prog_cntr == MLDSA_RESET) ||
        (mldsa_ctrl.prim_prog_cntr == MLDSA_ZEROIZE) ||
        ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_E)) ||
        ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_E)) ||
        ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_E))
    ;endproperty

    assume_abstract_prim_prog_cntr_ASM: assume property(abstract_prim_prog_cntr_P);

    logic fv_keygen_set;
    logic fv_keygen_signing_set;
    logic fv_signing_set;
    logic fv_verify_set;

    always_comb begin: fv_set_mode_logic
            fv_keygen_set = '0;
            fv_keygen_signing_set = '0;
            fv_signing_set = '0;
            fv_verify_set = '0;
            if((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_E)) begin
                fv_keygen_set = 1;
            end
            if((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_E)) begin
                fv_signing_set = 1;
            end
            if((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_E)) begin
                fv_verify_set = 1;
            end

        end
    property abstract_init_value_prim_prog_cntr_P;
      mldsa_ctrl.keygen_process == fv_keygen_set &&
      mldsa_ctrl.signing_process == fv_signing_set &&
      mldsa_ctrl.verifying_process == fv_verify_set &&
      mldsa_ctrl.keygen_signing_process == (mldsa_ctrl.cmd_reg == MLDSA_KEYGEN_SIGN)
    ;endproperty
    assume_abstract_init_value_prim_prog_cntr_ASM: assume property(abstract_init_value_prim_prog_cntr_P);


    // Post reset it takes 1cycle to update the out of sequencer. Since in the init value abstartcion this 
    //would cause the first cycle to be unconstrained and the data_o could take any value triggering unnecessary
    // state transitions.
    property abstract_reset_value_P;
    $past(!pi_rst_b)
    |->
    mldsa_ctrl.mldsa_seq_prim_inst.data_o == '0
    ;endproperty
    assume_abstract_reset_value_P: assume property(abstract_reset_value_P);
`endif 
    // Required since init value counter can start at a end state and trigger the valid
    // post that valid is resetted only if zeroize and in between cmds it is expected to have a zeroize
    // if thats not the case the proofs will fail, since the valid reg stays asserted.
    property zeroize_post_valid;
        mldsa_ctrl.mldsa_valid_reg
        |=>
        ##ADAMSBRIDGE_AUX_DLY pi_abr_reg_hwif_out_i.MLDSA_CTRL.ZEROIZE.value
    ;endproperty
    assume_zeroize_post_valid: assume property(zeroize_post_valid);


endmodule

