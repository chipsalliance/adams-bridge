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


    module fv_ntt_top_mlkem
        import abr_params_pkg::*;
        import ntt_defines_pkg::*;
    #(
        parameter REG_SIZE         = 24,
        parameter NTT_REG_SIZE     = REG_SIZE-1,
        parameter MLDSA_Q          = 23'd8380417,
        parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
        parameter MLDSA_N          = 256,
        parameter MLDSA_LOGN       = $clog2(MLDSA_N),
        parameter MEM_ADDR_WIDTH   = 15,
        parameter MEM_DATA_WIDTH   = 4*REG_SIZE,
        parameter WIDTH            = 46
        //#$localparams
        //$#//
    ) (
        //#$ports
        input                            pi_clk,
        input                            pi_reset_n,
        input                            pi_zeroize,
        input mode_t                     pi_mode,
        input                            pi_ntt_enable,
        input ntt_mem_addr_t             pi_ntt_mem_base_addr,
        input pwo_mem_addr_t             pi_pwo_mem_base_addr,
        input                            pi_accumulate,
        input                            pi_sampler_valid,
        input                            pi_shuffle_en,
        input                            pi_mlkem,
        input [5:0]                      pi_random,
        input mem_if_t                   po_mem_wr_req,
        input mem_if_t                   po_mem_rd_req,
        input logic [ABR_MEM_DATA_WIDTH-1:0] po_mem_wr_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_mem_rd_data,
        input                            pi_mem_rd_data_valid,
        input mem_if_t                   po_pwm_a_rd_req,
        input mem_if_t                   po_pwm_b_rd_req,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
        input logic                      po_ntt_busy,
        input logic                      po_ntt_done
        //$#//
    );

        default clocking default_clk @(posedge pi_clk); endclocking

    // auxiliary logic fv_ongoing to to be asserted & latched when ntt_enable signal is 1 and
    // deasserted when ntt_done is 1
    logic fv_ongoing;

        always_ff@(posedge pi_clk or negedge pi_reset_n)
        begin
            if(!pi_reset_n || pi_zeroize) begin
                fv_ongoing <= 1'b0;
            end else if(pi_ntt_enable) begin
                fv_ongoing <= 1'b1;
            end else if(po_ntt_done) begin
                fv_ongoing <= 1'b0;
            end
        end

        sequence reset_sequence;
            !pi_reset_n ##1 pi_reset_n;
        endsequence

        //Property to check liveness condition of ntt_busy output signal
        property busy_eventually_not_busy;
            disable iff(!pi_reset_n || pi_zeroize)

        po_ntt_busy
        |=> s_eventually(!po_ntt_busy)
        ;endproperty
        assert_busy_eventually_not_busy : assert property(busy_eventually_not_busy);

       //Connection check for cmd_ctrl busy to ntt_busy
        property cmd_ctrl_busy_to_output;
            disable iff(!pi_reset_n || pi_zeroize)

        ntt_ctrl_inst0.busy
        |-> po_ntt_busy
        ;endproperty
        assert_cmd_ctrl_busy_to_output : assert property(cmd_ctrl_busy_to_output);

        //Connection check for cmd_ctrl done to ntt_done
        property cmd_ctrl_done_to_output;
            disable iff(!pi_reset_n || pi_zeroize)

        ntt_ctrl_inst0.done
        |-> ##1 po_ntt_done
        ;endproperty
        assert_cmd_ctrl_done_to_output : assert property(cmd_ctrl_done_to_output);

        //////////////////////////////
        //////////// Requirement: po_pwm_*_rd_req
        //////////////////////////////
        // Verifies po_pwm_a_rd_req.rd_wr_en/addr (1-cycle delayed) match
        // ntt_ctrl_inst0.pw_rden/pw_mem_rd_addr_a in a pwo mode.
        property check_po_pwm_a_rd_req;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
            ##0 fv_ongoing
        |->
            ##1 po_pwm_a_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_rden ? RW_READ : RW_IDLE)
            ##0 po_pwm_a_rd_req.addr == ntt_ctrl_inst0.pw_mem_rd_addr_a
        ;endproperty
        assert_check_po_pwm_a_rd_req : assert property(check_po_pwm_a_rd_req);

        // Verifies po_pwm_a_rd_req.rd_wr_en/addr go idle/zero when not in a pwo mode.
        property check_po_pwm_a_rd_req_no_pwo;
            disable iff(!pi_reset_n || pi_zeroize)
            !((pi_mode inside {pwm, pwa, pws}) | (pi_mlkem & pi_mode == pairwm))
        |->
            ##1 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
            ##0 po_pwm_a_rd_req.addr ==  'h0
        ;endproperty
        assert_check_po_pwm_a_rd_req_no_pwo : assert property(check_po_pwm_a_rd_req_no_pwo);

        // Verifies po_pwm_a_rd_req.rd_wr_en goes idle when nothing is ongoing.
        property check_po_pwm_a_rd_req_no_ongoing;
            disable iff(!pi_reset_n || pi_zeroize)
            ##0 !fv_ongoing
        |->
            ##0 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
        ;endproperty
        assert_check_po_pwm_a_rd_req_no_ongoing : assert property(check_po_pwm_a_rd_req_no_ongoing);

        // Verifies po_pwm_b_rd_req.rd_wr_en/addr (1-cycle delayed) match
        // ntt_ctrl_inst0.pw_rden/pw_mem_rd_addr_b when shuffle is disabled.
        property check_po_pwm_b_rd_req_no_shuffle;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
            ##0 !pi_shuffle_en
            ##0 (fv_ongoing && !po_ntt_done)
        |->
            ##1 po_pwm_b_rd_req.rd_wr_en == (pi_sampler_valid ? (ntt_ctrl_inst0.pw_rden ? RW_READ
              : RW_IDLE) : RW_IDLE)
            ##0 po_pwm_b_rd_req.addr == (pi_sampler_valid ? ntt_ctrl_inst0.pw_mem_rd_addr_b : 0)
        ;endproperty
        assert_check_po_pwm_b_rd_req_no_shuffle : assert property(check_po_pwm_b_rd_req_no_shuffle);

        // Verifies po_pwm_b_rd_req.rd_wr_en/addr match ntt_ctrl_inst0.pw_rden/pw_mem_rd_addr_b
        // (sampler_valid delayed) when shuffle is enabled.
        property check_po_pwm_b_rd_req_shuffle;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 ((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
            ##1 pi_shuffle_en
        |->
            ##0 po_pwm_b_rd_req.rd_wr_en == ((ntt_ctrl_inst0.pw_rden && $past(pi_sampler_valid) )?
              RW_READ : RW_IDLE)
            ##0 $past(pi_sampler_valid) ? (po_pwm_b_rd_req.addr ==
              ntt_ctrl_inst0.pw_mem_rd_addr_b) : 1'b1
        ;endproperty
        assert_po_pwm_b_rd_req_shuffle : assert property(check_po_pwm_b_rd_req_shuffle);

        // Verifies po_pwm_a_rd_req/po_pwm_b_rd_req rd_wr_en/addr go idle/zero when not in a pwo
        // mode.
        property no_p_mode_no_req;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 !((pi_mode inside {pwm, pwa, pws}) || (pi_mlkem && pi_mode == pairwm))
        |->
            ##1 po_pwm_a_rd_req.rd_wr_en ==  RW_IDLE
            ##0 po_pwm_b_rd_req.rd_wr_en ==  RW_IDLE
            ##0 po_pwm_a_rd_req.addr ==  'h0
            ##0 po_pwm_b_rd_req.addr ==  'h0
        ;endproperty
        assert_no_p_mode_no_req : assert property(no_p_mode_no_req);


        //////////////////////////////
        //////////// Requirement: po_mem_wr
        //////////////////////////////

        logic fv_pwo;
        assign fv_pwo = (pi_mode inside {pwm, pwa, pws} || (pi_mlkem && pi_mode == pairwm));
        // pwo is added with pairwm_mode condition

        // Verifies po_mem_wr_req.rd_wr_en/addr (1-cycle delayed) match
        // ntt_ctrl_inst0.mem_wr_en/mem_wr_addr in ct mode with shuffle disabled.
        property check_mem_wr_req_ct_no_shuffle;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == ct
            ##0 !pi_shuffle_en
        |=>
            ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE)
            ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr ==
              $past(ntt_ctrl_inst0.mem_wr_addr)) : 1'b1
        ;endproperty
        assert_mem_wr_req_ct_no_shuffle : assert property(check_mem_wr_req_ct_no_shuffle);

        // Verifies po_mem_wr_req.rd_wr_en/addr match ntt_ctrl_inst0.mem_wr_en/mem_wr_addr in ct
        // mode with shuffle enabled.
        property check_mem_wr_req_ct_shuffle;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == ct
            ##0 pi_shuffle_en
        |=>
            ##0 po_mem_wr_req.rd_wr_en == (ntt_ctrl_inst0.mem_wr_en ? RW_WRITE : RW_IDLE)
            ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr ==
              ntt_ctrl_inst0.mem_wr_addr) : 1'b1
        ;endproperty
        assert_mem_wr_req_ct_shuffle : assert property(check_mem_wr_req_ct_shuffle);

        // Verifies po_mem_wr_req.rd_wr_en/addr match ntt_ctrl_inst0.mem_wr_en/mem_wr_addr in gs
        // mode.
        property check_mem_wr_req_gs;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == gs
        |=>
            ##0 po_mem_wr_req.rd_wr_en == ((ntt_ctrl_inst0.mem_wr_en) ? RW_WRITE : RW_IDLE)
            ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr ==
              ntt_ctrl_inst0.mem_wr_addr) : 1'b1
        ;endproperty
        assert_mem_wr_req_gs : assert property(check_mem_wr_req_gs);

        // Verifies po_mem_wr_req.rd_wr_en/addr (1-cycle delayed) match
        // ntt_ctrl_inst0.pw_wren/pw_mem_wr_addr_c in pwo mode.
        property check_mem_wr_req_pwo;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 fv_pwo
        |=>
            ##0 po_mem_wr_req.rd_wr_en == ($past(ntt_ctrl_inst0.pw_wren) ? RW_WRITE : RW_IDLE)
            ##0 (po_mem_wr_req.rd_wr_en == RW_WRITE) ? (po_mem_wr_req.addr ==
              $past(ntt_ctrl_inst0.pw_mem_wr_addr_c)) : 1'b1
        ;endproperty
        assert_mem_wr_req_pwo : assert property(check_mem_wr_req_pwo);

        // Verifies po_mem_wr_data matches the flopped hybrid_bf2x2 u/v outputs when writing in ct
        // mode.
        property check_mem_wr_data_ct;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == ct
            ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
            po_mem_wr_data ==  $past({1'b0, hybrid_bf2x2.uv_o.v21_o, 1'b0,
              hybrid_bf2x2.uv_o.u21_o, 1'b0, hybrid_bf2x2.uv_o.v20_o, 1'b0,
              hybrid_bf2x2.uv_o.u20_o})
        ;endproperty
        assert_mem_wr_data_ct : assert property(check_mem_wr_data_ct);

        // Verifies po_mem_wr_data matches buffer_inst0.data_o when writing in gs mode.
        property check_mem_wr_data_gs;
            disable iff(!pi_reset_n || pi_zeroize)

            ##0 pi_mode == gs
            ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
            po_mem_wr_data == buffer_inst0.data_o
        ;endproperty
        assert_mem_wr_data_gs : assert property(check_mem_wr_data_gs);


        logic [(4*REG_SIZE)-1:0] fv_pwm_wr_data;
        assign fv_pwm_wr_data = {1'b0, hybrid_bf2x2.pwo_uv_o.uv3, 1'b0, hybrid_bf2x2.pwo_uv_o.uv2,
          1'b0, hybrid_bf2x2.pwo_uv_o.uv1, 1'b0, hybrid_bf2x2.pwo_uv_o.uv0};

        // Verifies po_mem_wr_data matches the flopped hybrid_bf2x2 pwo outputs when writing in
        // pwm/pwa/pws/pairwm mode.
        property check_mem_wr_data_pwm_pwa_pws;
                disable iff(!pi_reset_n || pi_zeroize)

            ##0 (pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem) || pi_mode == pwa || pi_mode
              == pws
            ##0 po_mem_wr_req.rd_wr_en == RW_WRITE
        |->
            po_mem_wr_data == (pi_shuffle_en ? $past(fv_pwm_wr_data,2) : $past(fv_pwm_wr_data))
        ;endproperty
        assert_mem_wr_data_pwm_pwa_pws : assert property(check_mem_wr_data_pwm_pwa_pws);


        // Property to check pwm_b_rd_data_reg resets to 0
        property check_pwm_b_rd_data_reg_reset;
            $past(!pi_reset_n || pi_zeroize)
        |->
            ntt_top.pwm_b_rd_data_reg == '0
        ;endproperty
        assert_check_pwm_b_rd_data_reg_reset : assert property(check_pwm_b_rd_data_reg_reset);

    //////////////////////////////
    //////////// Requirement: po_mem_rd
    //////////////////////////////

        // Verifies po_mem_rd_req.rd_wr_en/addr match ntt_ctrl_inst0.mem_rd_en/mem_rd_addr in ct
        // or gs mode.
        property check_mem_rd_req_ct_gs;
                disable iff(!pi_reset_n || pi_zeroize)

                ##0 fv_ongoing
                ##0 pi_mode == ct || (pi_mode == gs)
        |->
                ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.mem_rd_en ? RW_READ : RW_IDLE)
                ##0 ntt_ctrl_inst0.mem_rd_en ? (po_mem_rd_req.addr == ntt_ctrl_inst0.mem_rd_addr)
                  : 1'b1
        ;endproperty
        assert_check_mem_rd_req_ct_gs : assert property(check_mem_rd_req_ct_gs);

        // Property to check read enable and addr for pwm/pairwm mode
        property check_mem_rd_req_pwm_dest_mem;
                disable iff(!pi_reset_n || pi_zeroize)

                ##0 fv_ongoing
                ##0 ((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem))
        |->
                ##0 po_mem_rd_req.rd_wr_en == (ntt_ctrl_inst0.pw_rden_dest_mem ? RW_READ : RW_IDLE)
                ##0 (ntt_ctrl_inst0.pw_rden_dest_mem) ? (po_mem_rd_req.addr ==
                  ntt_ctrl_inst0.pw_mem_rd_addr_c) : 1'b1
        ;endproperty
        assert_check_mem_rd_req_pwm_dest_mem : assert property(check_mem_rd_req_pwm_dest_mem);

        // Verifies po_mem_rd_req.rd_wr_en/addr go idle/zero (1-cycle delayed) when not in ct, gs,
        // or pwm/pairwm mode.
        property check_mem_rd_req_other;
                disable iff(!pi_reset_n || pi_zeroize)

                ##0 !((pi_mode == pwm) || ((pi_mode == pairwm) && pi_mlkem) || pi_mode == ct ||
                  pi_mode == gs)
        |=>
                ##0 po_mem_rd_req.rd_wr_en ==  RW_IDLE
                ##0 po_mem_rd_req.addr == 'h0
        ;endproperty
        assert_mem_rd_req_other : assert property(check_mem_rd_req_other);

        // Verifies ntt_ctrl_inst0.mem_rd_en stays asserted for exactly 64 cycles once it rises.
        property num_rd_always_64;
        disable iff(!pi_reset_n || pi_zeroize)
        fv_ongoing &&
        $rose(ntt_ctrl_inst0.mem_rd_en)
        |->
        ntt_ctrl_inst0.mem_rd_en[*64] ##1 !ntt_ctrl_inst0.mem_rd_en
        ;endproperty
        assert_num_rd_always_64 : assert property(num_rd_always_64);

        // Verifies ntt_ctrl_inst0.mem_wr_en stays asserted for exactly 64 cycles once it rises.
        property num_wr_always_64;
        disable iff(!pi_reset_n || pi_zeroize)
        fv_ongoing &&
        $rose(ntt_ctrl_inst0.mem_wr_en)
        |->
        ntt_ctrl_inst0.mem_wr_en[*64] ##1 !ntt_ctrl_inst0.mem_wr_en
        ;endproperty
        assert_num_wr_always_64 : assert property(num_wr_always_64);

        // Verifies ntt_ctrl_inst0.pw_rden stays asserted for 64 cycles until pwo_done, once a pwo
        // round starts.
        property num_pwrd_always_64;
        disable iff(!pi_reset_n || pi_zeroize)
        fv_ongoing &&
        fv_pwo &&
        ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
        (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
        |->
        ntt_ctrl_inst0.pw_rden[->64] s_until (ntt_ctrl_inst0.pwo_done)
        ;endproperty
        assert_num_pwrd_always_64 : assert property(num_pwrd_always_64);

        // Verifies ntt_ctrl_inst0.pw_wren stays asserted for 64 cycles until pwo_done, once a pwo
        // round starts.
        property num_pwwr_always_64;
        disable iff(!pi_reset_n || pi_zeroize)
        fv_ongoing &&
        fv_pwo &&
        ((ntt_ctrl_inst0.arc_IDLE_RD_STAGE) ||
        (ntt_ctrl_inst0.pwo_done && pi_ntt_enable))
        |->
        ntt_ctrl_inst0.pw_wren[->64] s_until (ntt_ctrl_inst0.pwo_done)
        ;endproperty
        assert_num_pwwr_always_64 : assert property(num_pwwr_always_64);



    endmodule

