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

module fv_mldsa_sampler_top_aip
    import mldsa_sampler_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_params_pkg::*;
    import abr_prim_alert_pkg::*;
    import abr_prim_mubi_pkg::*;
(
    ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input    logic                  pi_clk,
    input    logic                  pi_reset_n,
    input    logic                  pi_zeroize,
    input    mldsa_sampler_mode_e   pi_sampler_mode_i,
    input    logic                  pi_sha3_start_i,
    input    logic                  pi_msg_start_i,
    input    logic                  pi_msg_valid_i,
    input    logic                  po_msg_rdy_o,
    input    logic [MsgStrbW-1:0]   pi_msg_strobe_i,
    input    logic [MsgWidth-1:0]   pi_msg_data_i[Sha3Share],
    input    logic                  pi_sampler_start_i,
    input    logic [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr_i,
    input    mem_if_t                          pi_sib_mem_rd_req_i,
    input    logic [MLDSA_MEM_DATA_WIDTH-1:0]       po_sib_mem_rd_data_o,
    input    logic                                  po_sampler_busy_o,
    input    logic                                  po_sampler_ntt_dv_o,
    input    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0]   po_sampler_ntt_data_o,
    input    logic                                          po_sampler_mem_dv_o,
    input    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0]   po_sampler_mem_data_o,
    input    logic [MLDSA_MEM_ADDR_WIDTH-1:0]       po_sampler_mem_addr_o,
    input    logic                                  po_sampler_state_dv_o,
    input    logic [abr_sha3_pkg::StateW-1:0]       po_sampler_state_data_o[Sha3Share]
);

    // Define default clock
    default clocking default_clk @(posedge pi_clk); endclocking

    // constraints
    fv_constraints fv_constraints_i(.*);

    // Checks the case, when no mode has been selected and the signals are reset accordingly
    property mode_mux_NONE_p;
        pi_sampler_mode_i == MLDSA_SAMPLER_NONE
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L256 &&
        mldsa_sampler_top.vld_cycle == 0 &&
        mldsa_sampler_top.sampler_done == 0 &&

        po_sampler_mem_dv_o == 0 &&
        po_sampler_mem_data_o == 0 &&
        po_sampler_mem_addr_o == 0 &&
        po_sampler_state_dv_o == 0 &&
        po_sampler_state_data_o[0] == 0 &&

        mldsa_sampler_top.zeroize_rejb == pi_zeroize &&
        mldsa_sampler_top.zeroize_rejs == pi_zeroize &&
        mldsa_sampler_top.zeroize_exp_mask == pi_zeroize &&
        mldsa_sampler_top.zeroize_sib == pi_zeroize &&
        mldsa_sampler_top.zeroize_sib_mem == pi_zeroize &&
        mldsa_sampler_top.zeroize_sha3 == pi_zeroize &&
        mldsa_sampler_top.zeroize_piso == pi_zeroize &&
        mldsa_sampler_top.piso_mode == 0
        ;
    endproperty
    mode_mux_NONE_a: assert property (disable iff(!pi_reset_n) mode_mux_NONE_p);
    
    // Checks the case, when SHAKE256 mode has been selected and the signals are set according to the mode
    property mode_mux_SHAKE256_p;
        pi_sampler_mode_i == MLDSA_SHAKE256
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L256 &&
        mldsa_sampler_top.sampler_done == mldsa_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == mldsa_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o[0] == mldsa_sampler_top.sha3_state[0] &&

        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.sha3_state_dv
        ;
    endproperty
    mode_mux_SHAKE256_a: assert property (disable iff(!pi_reset_n) mode_mux_SHAKE256_p);

    // Checks the case, when SHAKE128 mode has been selected and the signals are set according to the mode
    property mode_mux_SHAKE128_p;
        pi_sampler_mode_i == MLDSA_SHAKE128
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L128 &&
        mldsa_sampler_top.sampler_done == mldsa_sampler_top.sha3_state_dv &&

        po_sampler_state_dv_o == mldsa_sampler_top.sha3_state_dv &&
        po_sampler_state_data_o[0] == mldsa_sampler_top.sha3_state[0] &&

        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.sha3_state_dv
        ;
    endproperty
    mode_mux_SHAKE128_a: assert property (disable iff(!pi_reset_n) mode_mux_SHAKE128_p);

    // Checks the case, when REJ_SAMPLER mode has been selected and the signals are set according to the mode
    property mode_mux_REJ_SAMPLER_p;
        pi_sampler_mode_i == MLDSA_REJ_SAMPLER
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L128 &&
        mldsa_sampler_top.vld_cycle == mldsa_sampler_top.rejs_dv &&
        mldsa_sampler_top.sampler_done == (mldsa_sampler_top.coeff_cnt == (MLDSA_COEFF_CNT/4)) &&

        mldsa_sampler_top.zeroize_rejs == mldsa_sampler_top.zeroize_rejs | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.zeroize_sha3 | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_piso == mldsa_sampler_top.zeroize_piso | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.piso_mode == 0
        ;
    endproperty
    mode_mux_REJ_SAMPLER_a: assert property (disable iff(!pi_reset_n) mode_mux_REJ_SAMPLER_p);

    // Checks the case, when EXP_MASK mode has been selected and the signals are set according to the mode
    property mode_mux_EXP_MASK_p;
        pi_sampler_mode_i == MLDSA_EXP_MASK
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L256 &&
        mldsa_sampler_top.vld_cycle == mldsa_sampler_top.exp_dv &&
        mldsa_sampler_top.sampler_done == (mldsa_sampler_top.coeff_cnt == (MLDSA_COEFF_CNT/4)) &&

        po_sampler_mem_dv_o == mldsa_sampler_top.exp_dv &&
        po_sampler_mem_data_o == mldsa_sampler_top.exp_data &&
        po_sampler_mem_addr_o == mldsa_sampler_top.dest_addr &&

        mldsa_sampler_top.zeroize_exp_mask == mldsa_sampler_top.zeroize_exp_mask | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.zeroize_sha3 | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_piso == mldsa_sampler_top.zeroize_piso | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.piso_mode == 2
    ;
    endproperty
    mode_mux_EXP_MASK_a: assert property (disable iff(!pi_reset_n) mode_mux_EXP_MASK_p);

    // Checks the case, when REJ_BOUNDED mode has been selected and the signals are set according to the mode
    property mode_mux_REJ_BOUNDED_p;
        pi_sampler_mode_i == MLDSA_REJ_BOUNDED
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L256 &&
        mldsa_sampler_top.vld_cycle == mldsa_sampler_top.rejb_dv &&
        mldsa_sampler_top.sampler_done == (mldsa_sampler_top.coeff_cnt == (MLDSA_COEFF_CNT/4)) &&

        po_sampler_mem_dv_o == mldsa_sampler_top.rejb_dv &&
        po_sampler_mem_data_o == mldsa_sampler_top.rejb_data &&
        po_sampler_mem_addr_o == mldsa_sampler_top.dest_addr &&

        mldsa_sampler_top.zeroize_rejb == mldsa_sampler_top.zeroize_rejb | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.zeroize_sha3 | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_piso == mldsa_sampler_top.zeroize_piso | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.piso_mode == 1
    ;
    endproperty
    mode_mux_REJ_BOUNDED_a: assert property (disable iff(!pi_reset_n) mode_mux_REJ_BOUNDED_p);

    // Checks the case, when SAMPLER_IN_BALL mode has been selected and the signals are set according to the mode
    property mode_mux_SAMPLE_IN_BALL_p;
        pi_sampler_mode_i == MLDSA_SAMPLE_IN_BALL
    |->
        mldsa_sampler_top.mode == abr_sha3_pkg::Shake &&
        mldsa_sampler_top.strength == abr_sha3_pkg::L256 &&
        mldsa_sampler_top.sampler_done == mldsa_sampler_top.sib_done &&

        mldsa_sampler_top.zeroize_sib_mem == pi_sampler_start_i &&
        mldsa_sampler_top.zeroize_sib == mldsa_sampler_top.zeroize_sib | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_sha3 == mldsa_sampler_top.zeroize_sha3 | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.zeroize_piso == mldsa_sampler_top.zeroize_piso | mldsa_sampler_top.sampler_done &&
        mldsa_sampler_top.piso_mode == 3
    ;
    endproperty
    mode_mux_SAMPLE_IN_BALL_a: assert property (disable iff(!pi_reset_n) mode_mux_SAMPLE_IN_BALL_p);

    // Checks if in case of a data_hold signal from REJ_BOUNDED and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_REJ_BOUNDED_vld_hld_p;
        mldsa_sampler_top.rejb_piso_dv &&
        mldsa_sampler_top.rejb_piso_hold &&
        !mldsa_sampler_top.sampler_done
    |->
        ##1
        $stable(mldsa_sampler_top.rejb_piso_data) &&
        mldsa_sampler_top.rejb_piso_dv
    ;
    endproperty
    register_REJ_BOUNDED_vld_hld_a: assert property (disable iff(!pi_reset_n || pi_zeroize) register_REJ_BOUNDED_vld_hld_p);

    // Checks if in case of a data_hold signal from REJ_SAMPLER and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_REJ_SAMPLER_vld_hld_p;    
        mldsa_sampler_top.rejs_piso_dv &&
        mldsa_sampler_top.rejs_piso_hold &&
        !mldsa_sampler_top.sampler_done
    |->
        ##1
        $stable(mldsa_sampler_top.rejs_piso_data) &&
        mldsa_sampler_top.rejs_piso_dv
    ;
    endproperty
    register_REJ_SAMPLER_vld_hld_a: assert property (disable iff(!pi_reset_n || pi_zeroize) register_REJ_SAMPLER_vld_hld_p);


    // Checks if in case of a data_hold signal from SAMPLER_IN_BALL and data valid input signal, the PISO buffer keeps its output data and data valid signal stable.
    property register_SAMPLE_IN_BALL_CTRL_vld_hld_p;
        mldsa_sampler_top.sib_piso_dv && 
        mldsa_sampler_top.sib_piso_hold  &&
        !mldsa_sampler_top.sampler_done
    |-> 
        ##1 
        $stable(mldsa_sampler_top.sib_piso_data) && 
        mldsa_sampler_top.sib_piso_dv
    ;
    endproperty
    register_SAMPLE_IN_BALL_CTRL_vld_hld_a: assert property(disable iff (!pi_reset_n || pi_zeroize) register_SAMPLE_IN_BALL_CTRL_vld_hld_p);

    // Checks that the piso_dv signal is asserted and stays asserted until the sampler is done.
    property register_SAMPLE_IN_BALL_CTRL_vld_stable_p;
        mldsa_sampler_top.sib_piso_dv
    |->
        mldsa_sampler_top.sib_piso_dv until mldsa_sampler_top.sampler_done
    ;
    endproperty
    register_SAMPLE_IN_BALL_CTRL_vld_stable_a: assert property(disable iff (!pi_reset_n || pi_zeroize) register_SAMPLE_IN_BALL_CTRL_vld_stable_p);

    // Checks if there is no data incoming, the design can expect valid data in the future.
    property register_PISO_BITS_p;
        mldsa_sampler_top.abr_piso_inst.buffer_wr_ptr < mldsa_sampler_top.abr_piso_inst.PISO_OUTPUT_RATE0  &&
        !mldsa_sampler_top.sampler_done &&
        pi_sampler_mode_i inside {MLDSA_REJ_SAMPLER,MLDSA_REJ_BOUNDED,MLDSA_EXP_MASK,MLDSA_SAMPLE_IN_BALL}
    |-> 
        s_eventually(mldsa_sampler_top.sha3_state_dv)
    ;
    endproperty
    register_PISO_BITS_a: assert property(disable iff (!pi_reset_n || pi_zeroize) register_PISO_BITS_p);

    // Checks if the piso hold signal is asserted correctly, based on the mode and sampler hold signals
    property signal_PISO_HOLD_p;
        mldsa_sampler_top.piso_hold == (((pi_sampler_mode_i == MLDSA_REJ_SAMPLER)   & mldsa_sampler_top.rejs_piso_hold) |
                                       ((pi_sampler_mode_i == MLDSA_REJ_BOUNDED)    & mldsa_sampler_top.rejb_piso_hold) |
                                       ((pi_sampler_mode_i == MLDSA_EXP_MASK)       & mldsa_sampler_top.exp_piso_hold)  |
                                       ((pi_sampler_mode_i == MLDSA_SAMPLE_IN_BALL) & mldsa_sampler_top.sib_piso_hold))
    ;
    endproperty
    signal_PISO_HOLD_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_PISO_HOLD_p);

    // Checks if REJ_SAMPLER data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_REJS_PISO_DV_p;
        mldsa_sampler_top.rejs_piso_dv == ((pi_sampler_mode_i == MLDSA_REJ_SAMPLER) & mldsa_sampler_top.piso_dv)
    ;
    endproperty
    signal_REJS_PISO_DV_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_REJS_PISO_DV_p);

    // Checks if REJ_BOUNDED data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_REJB_PISO_DV_p;
        mldsa_sampler_top.rejb_piso_dv == ((pi_sampler_mode_i == MLDSA_REJ_BOUNDED) & mldsa_sampler_top.piso_dv)
    ;
    endproperty
    signal_REJB_PISO_DV_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_REJB_PISO_DV_p);

    // Checks if EXP_MASK data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_EXP_PISO_DV_p;
        mldsa_sampler_top.exp_piso_dv == ((pi_sampler_mode_i == MLDSA_EXP_MASK) & mldsa_sampler_top.piso_dv)
    ;
    endproperty
    signal_EXP_PISO_DV_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_EXP_PISO_DV_p);

    // Checks if EXP_MASK input data is extracted correctly from piso output data
    property signal_EXP_PISO_DATA_p;
        mldsa_sampler_top.exp_piso_data == mldsa_sampler_top.piso_data[EXP_PISO_OUTPUT_RATE-1:0];
    
    endproperty
    signal_EXP_PISO_DATA_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_EXP_PISO_DATA_p);

    // Checks if SAMPLE_IN_BALL data valid signals are asserted correctly, based on the mode and the piso data valid signal.
    property signal_SIB_PISO_DV_p;
        mldsa_sampler_top.sib_piso_dv == ((pi_sampler_mode_i == MLDSA_SAMPLE_IN_BALL) & mldsa_sampler_top.piso_dv)
    ;
    endproperty
    signal_SIB_PISO_DV_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SIB_PISO_DV_p);

    // Checks that the sampler_busy_o signal is asserted either through sampler_start_i or the sampler_fsm states.
    property signal_SAMPLER_BUSY_p;
        pi_sampler_start_i ||
        (mldsa_sampler_top.sampler_fsm_ps != mldsa_sampler_top.MLDSA_SAMPLER_IDLE)
    |->
        po_sampler_busy_o
    ;
    endproperty
    signal_SAMPLER_BUSY_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SAMPLER_BUSY_p);

    // Checks if the sampler_busy_o signal is also deasserted at one point.
    property liveness_SAMPLER_BUSY_p;
        po_sampler_busy_o
    |->
        s_eventually(!po_sampler_busy_o)
    ;
    endproperty
    liveness_SAMPLER_BUSY_a: assert property(disable iff (!pi_reset_n || pi_zeroize) liveness_SAMPLER_BUSY_p);

    // Checks that sampler_ntt_dv_o represents the data valid signal from REJ_SAMPLER.
    property signal_SAMPLER_NTT_DV_p;
        po_sampler_ntt_dv_o == mldsa_sampler_top.rejs_dv
    ;
    endproperty
    signal_SAMPLER_NTT_DV_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SAMPLER_NTT_DV_p);

    // Checks that sampler_ntt_data_o represents the output data from REJ_SAMPLER.
    property signal_SAMPLER_NTT_DATA_p;
        po_sampler_ntt_data_o == mldsa_sampler_top.rejs_data
    ;
    endproperty
    signal_SAMPLER_NTT_DATA_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SAMPLER_NTT_DATA_p);

    // Checks that sib_mem_cs_mux is assigned correctly.
    property signal_SIB_MEM_CS_MUX_p;
        mldsa_sampler_top.sib_mem_cs_mux[0] == ((pi_sib_mem_rd_req_i.rd_wr_en == RW_READ) | mldsa_sampler_top.sib_mem_cs[0]) &&
        mldsa_sampler_top.sib_mem_cs_mux[1] == mldsa_sampler_top.sib_mem_cs[1]
    ;
    endproperty
    signal_SIB_MEM_CS_MUX_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SIB_MEM_CS_MUX_p);

    // Checks that sib_mem_addr_mux is assigned correctly.
    property signal_SIB_MEM_ADDR_MUX_p;
        mldsa_sampler_top.sib_mem_addr_mux[0] == ((pi_sib_mem_rd_req_i.rd_wr_en == RW_READ) ? pi_sib_mem_rd_req_i.addr[5:0] : mldsa_sampler_top.sib_mem_addr[0]) &&
        mldsa_sampler_top.sib_mem_addr_mux[1] == mldsa_sampler_top.sib_mem_addr[1]
    ;
    endproperty
    signal_SIB_MEM_ADDR_MUX_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SIB_MEM_ADDR_MUX_p);

   // Checks that sib_mem_rd_data is assigned correctly.
    property signal_SIB_MEM_RD_DATA_p;
        po_sib_mem_rd_data_o == {1'b0,mldsa_sampler_top.sib_mem_rddata[0][3],1'b0,mldsa_sampler_top.sib_mem_rddata[0][2],1'b0,mldsa_sampler_top.sib_mem_rddata[0][1],1'b0,mldsa_sampler_top.sib_mem_rddata[0][0]}
    ;
    endproperty
    signal_SIB_MEM_RD_DATA_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_SIB_MEM_RD_DATA_p);

    // Checks that rejs_data is delayed by one clock cycle.
    property signal_REJS_DATA_p;
        $past(mldsa_sampler_top.rejs_data_q) == mldsa_sampler_top.rejs_data
    ;
    endproperty
    signal_REJS_DATA_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_REJS_DATA_p);

    // Checks, if there is either a sampler_start_i or a sampler_done, the coeff_cnt is set to 0
    property signal_COEFF_CNT_sampler_start_p;
        pi_sampler_start_i || mldsa_sampler_top.sampler_done
    |=>
        mldsa_sampler_top.coeff_cnt == 'd0
    ;
    endproperty
    signal_COEFF_CNT_sampler_start_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_COEFF_CNT_sampler_start_p);

    // Checks, if there is no a sampler_start_i nor a sampler_done, but a vld_cycle, the coeff_cnt increments
    property signal_COEFF_CNT_vld_cycle_p;
        !(pi_sampler_start_i || mldsa_sampler_top.sampler_done) && mldsa_sampler_top.vld_cycle
    |=>
        mldsa_sampler_top.coeff_cnt == $past(mldsa_sampler_top.coeff_cnt) + 'd1
    ;
    endproperty
    signal_COEFF_CNT_vld_cycle_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_COEFF_CNT_vld_cycle_p);

    // Checks, if there is no a sampler_start_i, no sampler_done and no vld_cycle, the coeff_cnt stays stable 
    property signal_COEFF_CNT_no_vld_cycle_p;
        !(pi_sampler_start_i || mldsa_sampler_top.sampler_done) && !mldsa_sampler_top.vld_cycle
    |=>
        mldsa_sampler_top.coeff_cnt == $past(mldsa_sampler_top.coeff_cnt)
    ;
    endproperty
    signal_COEFF_CNT_no_vld_cycle_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_COEFF_CNT_no_vld_cycle_p);

    // Checks, if there is either a sampler_done, the dest_addr is set to 0
    property signal_DEST_ADDR_sampler_done_p;
        mldsa_sampler_top.sampler_done
    |=>
        mldsa_sampler_top.dest_addr == 'd0
    ;
    endproperty
    signal_DEST_ADDR_sampler_done_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_DEST_ADDR_sampler_done_p);

    // Checks, if there is no sampler_done, but a sampler_start_i, the dest_addr is set to dest_base_addr_i
    property signal_DEST_ADDR_sampler_start_p;
        !mldsa_sampler_top.sampler_done && pi_sampler_start_i
    |=>
        mldsa_sampler_top.dest_addr == $past(pi_dest_base_addr_i)
    ;
    endproperty
    signal_DEST_ADDR_sampler_start_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_DEST_ADDR_sampler_start_p);

    // Checks, if there is no sampler_done, no sampler_start_i, but a vld_cycle, the dest_addr increments
    property signal_DEST_ADDR_vld_cycle_p;
        !mldsa_sampler_top.sampler_done && !pi_sampler_start_i && mldsa_sampler_top.vld_cycle
    |=>
        mldsa_sampler_top.dest_addr == 14'($past(mldsa_sampler_top.dest_addr)  + 14'd1)
    ;
    endproperty
    signal_DEST_ADDR_vld_cycle_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_DEST_ADDR_vld_cycle_p);

    // Checks, if there is no sampler_done, no sampler_start_i and no vld_cycle, the dest_addr stays stable
    property signal_DEST_ADDR_no_vld_cycle_p;
        !mldsa_sampler_top.sampler_done && !pi_sampler_start_i && !mldsa_sampler_top.vld_cycle
    |=>
        mldsa_sampler_top.dest_addr == $past(mldsa_sampler_top.dest_addr)
    ;
    endproperty
    signal_DEST_ADDR_no_vld_cycle_a: assert property(disable iff (!pi_reset_n || pi_zeroize) signal_DEST_ADDR_no_vld_cycle_p);

    // Checks that sha3 output is 0, whenever there is no data valid signal asserted.
    property signal_ABR_SHA3_DATA_p;
        !mldsa_sampler_top.sha3_state_dv
    |->
        mldsa_sampler_top.sha3_state[0] == '0
    ;
    endproperty
    signal_ABR_SHA3_DATA_a: assert property(disable iff(!pi_reset_n || pi_zeroize) signal_ABR_SHA3_DATA_p);

    // Checks that all sequential assigned signals are resetted correctly.
    property signal_reset_p;
        $past(!pi_reset_n || pi_zeroize)
    |->
        mldsa_sampler_top.dest_addr == 'd0 &&
        mldsa_sampler_top.coeff_cnt == 'd0 &&
        mldsa_sampler_top.sampler_fsm_ps == mldsa_sampler_top.MLDSA_SAMPLER_IDLE
    ;
    endproperty
    signal_reset_a: assert property(signal_reset_p);

    // Checks that the sampler_fsm signal is updated accordingly.
    property signal_sampler_fsm_p;
        !(!pi_reset_n || pi_zeroize)
    |=>
        mldsa_sampler_top.sampler_fsm_ps == $past(mldsa_sampler_top.sampler_fsm_ns)
    ;
    endproperty
    signal_sampler_fsm_a: assert property(disable iff(!pi_reset_n || pi_zeroize) signal_sampler_fsm_p);

    // Checks that the sampler_fsm signal stays in its specified value range.
    property signal_sampler_fsm_in_range_p;
        mldsa_sampler_top.sampler_fsm_ps inside {mldsa_sampler_top.MLDSA_SAMPLER_IDLE, mldsa_sampler_top.MLDSA_SAMPLER_PROC, mldsa_sampler_top.MLDSA_SAMPLER_WAIT, mldsa_sampler_top.MLDSA_SAMPLER_RUN, mldsa_sampler_top.MLDSA_SAMPLER_DONE}
    ;
    endproperty
    signal_sampler_fsm_in_range_a: assert property(disable iff(!pi_reset_n || pi_zeroize) signal_sampler_fsm_in_range_p);
     

endmodule

// Connect this verification module with the DUV
bind mldsa_sampler_top fv_mldsa_sampler_top_aip mldsa_sampler_top_aip_i(
    .pi_clk(clk),
    .pi_reset_n(rst_b),
    .pi_zeroize(zeroize),
    .pi_sampler_start_i(sampler_start_i),
    .pi_sampler_mode_i(sampler_mode_i),
    .pi_sha3_start_i(sha3_start_i),
    .pi_msg_start_i(msg_start_i),
    .pi_msg_valid_i(msg_valid_i),
    .po_msg_rdy_o(msg_rdy_o),
    .pi_msg_strobe_i(msg_strobe_i),
    .pi_msg_data_i(msg_data_i),
    .pi_dest_base_addr_i(dest_base_addr_i),
    .pi_sib_mem_rd_req_i(sib_mem_rd_req_i),
    .po_sib_mem_rd_data_o(sib_mem_rd_data_o),
    .po_sampler_busy_o(sampler_busy_o),
    .po_sampler_ntt_dv_o(sampler_ntt_dv_o),
    .po_sampler_ntt_data_o(sampler_ntt_data_o),
    .po_sampler_mem_dv_o(sampler_mem_dv_o),
    .po_sampler_mem_data_o(sampler_mem_data_o),
    .po_sampler_mem_addr_o(sampler_mem_addr_o),
    .po_sampler_state_dv_o(sampler_state_dv_o),
    .po_sampler_state_data_o(sampler_state_data_o)
);
