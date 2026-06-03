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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
<<<<<<< HEAD
// | Created on 02.12.2024 at 13:17                    |
=======
// | Created on 13.01.2025 at 12:52                    |
>>>>>>> issue1/adamsbridge_ctrl_esl
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import AdamsBridge_functions::*;
import mldsa_params_pkg::*;
import mldsa_ctrl_pkg::*;


module fv_AdamsBridgeSecondary_ref_wrapper_m;


default clocking default_clk @(posedge (mldsa_ctrl.clk)); endclocking


a_unsigned_15_8 ct_addrs_in;
assign ct_addrs_in = '{
  0: MLDSA_CT_0_BASE, 1: MLDSA_CT_1_BASE, 2: MLDSA_CT_2_BASE, 3: MLDSA_CT_3_BASE,
  4: MLDSA_CT_4_BASE, 5: MLDSA_CT_5_BASE, 6: MLDSA_CT_6_BASE, 7: MLDSA_CT_7_BASE
};

st_FromMakehintType from_makehint;
assign from_makehint = '{
  makehint_wren: mldsa_ctrl.makehint_reg_wren_i,
  makehint_addr: mldsa_ctrl.makehint_reg_wr_addr_i,
  makehint_data: mldsa_ctrl.makehint_reg_wrdata_i
};

a_unsigned_15_8 hint_r_addrs_in;
assign hint_r_addrs_in = '{
  0: MLDSA_HINT_R_0_BASE, 1: MLDSA_HINT_R_1_BASE, 2: MLDSA_HINT_R_2_BASE, 3: MLDSA_HINT_R_3_BASE,
  4: MLDSA_HINT_R_4_BASE, 5: MLDSA_HINT_R_5_BASE, 6: MLDSA_HINT_R_6_BASE, 7: MLDSA_HINT_R_7_BASE
};

a_unsigned_15_7 s1_addrs_in;
assign s1_addrs_in = '{
  0: MLDSA_S1_0_BASE, 1: MLDSA_S1_1_BASE, 2: MLDSA_S1_2_BASE, 3: MLDSA_S1_3_BASE,
  4: MLDSA_S1_4_BASE, 5: MLDSA_S1_5_BASE, 6: MLDSA_S1_6_BASE
};

a_unsigned_15_8 s2_addrs_in;
assign s2_addrs_in = '{
  0: MLDSA_S2_0_BASE, 1: MLDSA_S2_1_BASE, 2: MLDSA_S2_2_BASE, 3: MLDSA_S2_3_BASE,
  4: MLDSA_S2_4_BASE, 5: MLDSA_S2_5_BASE, 6: MLDSA_S2_6_BASE, 7: MLDSA_S2_7_BASE
};

a_unsigned_15_8 t_addrs_in;
assign t_addrs_in = '{
  0: MLDSA_T0_BASE, 1: MLDSA_T1_BASE, 2: MLDSA_T2_BASE, 3: MLDSA_T3_BASE,
  4: MLDSA_T4_BASE, 5: MLDSA_T5_BASE, 6: MLDSA_T6_BASE, 7: MLDSA_T7_BASE
};

a_unsigned_15_8 w0_addrs_in;
assign w0_addrs_in = '{
  0: MLDSA_W0_0_BASE, 1: MLDSA_W0_1_BASE, 2: MLDSA_W0_2_BASE, 3: MLDSA_W0_3_BASE,
  4: MLDSA_W0_4_BASE, 5: MLDSA_W0_5_BASE, 6: MLDSA_W0_6_BASE, 7: MLDSA_W0_7_BASE
};

a_unsigned_15_7 y_addrs_in;
assign y_addrs_in = '{
  0: MLDSA_Y_0_BASE, 1: MLDSA_Y_1_BASE, 2: MLDSA_Y_2_BASE, 3: MLDSA_Y_3_BASE,
  4: MLDSA_Y_4_BASE, 5: MLDSA_Y_5_BASE, 6: MLDSA_Y_6_BASE
};

st_ToMakehintType to_makehint;
assign to_makehint = '{
  source_addr: mldsa_ctrl.aux_src0_base_addr_o[1]
};

st_NormCheckType to_norm_check;
assign to_norm_check = '{
  immediate: mldsa_ctrl.sec_instr.imm[1:0],
  source_addr: mldsa_ctrl.aux_src0_base_addr_o[1]
};

st_NttType to_ntt;
assign to_ntt = '{
  mode: mldsa_ctrl.ntt_mode_o[1],
  operand1: mldsa_ctrl.ntt_mem_base_addr_o[1].src_base_addr,
  operand2: mldsa_ctrl.ntt_mem_base_addr_o[1].interim_base_addr,
  destination: mldsa_ctrl.ntt_mem_base_addr_o[1].dest_base_addr
};

st_SigEncodeType to_sig_encode;
assign to_sig_encode = '{
  source_addr: mldsa_ctrl.aux_src0_base_addr_o[1],
  immediate: mldsa_ctrl.aux_dest_base_addr_o[1]
};

st_SkDecodeType to_sk_decode;
assign to_sk_decode = '{
  source_operand: mldsa_ctrl.aux_src0_base_addr_o[1],
  destination_addr: mldsa_ctrl.aux_dest_base_addr_o[1]
};


fv_AdamsBridgeSecondary_m fv_AdamsBridgeSecondary(
  .rst_n(mldsa_ctrl.rst_b),
  .clk(mldsa_ctrl.clk),

  // Ports
  .c_addr_in(MLDSA_C_BASE),

  .c_ntt_addr_in(MLDSA_C_NTT_BASE),

  .c_valid_in(mldsa_ctrl.c_valid),

  .cs1_addr_in(MLDSA_CS1_BASE),

  .cs2_addr_in(MLDSA_CS2_BASE),

  .ct_addrs_in(ct_addrs_in),

  .from_makehint(from_makehint),

  .hint_r_addrs_in(hint_r_addrs_in),

  .makehint_done_in(mldsa_ctrl.makehint_done_i),

  .makehint_invalid_in(mldsa_ctrl.makehint_invalid_i),

  .norm_check_done_in(mldsa_ctrl.normcheck_done_i),

  .norm_check_invalid(mldsa_ctrl.normcheck_invalid_i),

  .ntt_done_in(!mldsa_ctrl.ntt_busy_i[1]),

  .r0_addr_in(MLDSA_R0_BASE),

  .s1_addrs_in(s1_addrs_in),

  .s2_addrs_in(s2_addrs_in),

  .sig_encode_done_in(mldsa_ctrl.sigencode_done_i),

  .sign_start_in(mldsa_ctrl.cmd_reg == MLDSA_SIGN || (mldsa_ctrl.keygen_signing_process && (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_JUMP_SIGN))),

  .sk_decode_done_in(mldsa_ctrl.skdecode_done_i),

  .sk_s1_offset_in(MLDSA_SK_S1_OFFSET),

  .t_addrs_in(t_addrs_in),

  .temp_addr_in(MLDSA_TEMP0_BASE),

  .w0_addrs_in(w0_addrs_in),

  .w0_valid_in(mldsa_ctrl.w0_valid),

  .y_addrs_in(y_addrs_in),

  .y_valid_in(mldsa_ctrl.y_valid),

  .z_addr_in(MLDSA_Z_BASE),

  .clear_w0_valid_out(mldsa_ctrl.clear_w0_valid),

  .clear_y_valid_out(mldsa_ctrl.clear_y_valid),

  .to_makehint_vld(mldsa_ctrl.makehint_enable_o),
  .to_makehint_rdy(1'b0),
  .to_makehint(to_makehint),

  .to_norm_check_vld(mldsa_ctrl.normcheck_enable[1]),
  .to_norm_check_rdy(1'b0),
  .to_norm_check(to_norm_check),

  .to_ntt_vld(mldsa_ctrl.ntt_enable_o[1]),
  .to_ntt_rdy(1'b0),
  .to_ntt(to_ntt),

  .to_sig_encode_vld(mldsa_ctrl.sigencode_enable_o),
  .to_sig_encode_rdy(1'b0),
  .to_sig_encode(to_sig_encode),

  .to_sk_decode_vld(mldsa_ctrl.skdecode_enable_o),
  .to_sk_decode_rdy(1'b0),
  .to_sk_decode(to_sk_decode),

  // Registers
  .compute_ct_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 38 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 45) ? mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 38 : 0),
  .compute_ct_intt_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 46 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 53) ? mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 46 : 0),
  .compute_r_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102) ? (mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) / 6 : 0),
  .compute_z_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36) ? (mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) / 5 : 0),
  .s1_ntt_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 9 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 15) ? mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_INIT_S - 9 : 0),
  .s2_ntt_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 16 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 23) ? mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_INIT_S - 16 : 0),
  .signature_h(mldsa_ctrl.signature_reg.enc.h),
  .signature_valid(mldsa_ctrl.signature_valid),
  .t_ntt_idx((mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 1 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 8) ? mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_INIT_S - 1 : 0),

  // States
  .secondary_after_clear_w0_valid(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_VALID_S + 104 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_IDLE && $past(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CLEAR_W0)),
  .secondary_after_clear_y_valid(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 38 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 45 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_IDLE && $past(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CLEAR_Y)),
  .secondary_clear_w0_valid(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CLEAR_W0),
  .secondary_clear_y_valid(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CLEAR_Y),
  .secondary_compute_ct(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 38 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 45 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_compute_ct_intt(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 46 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 53 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_compute_ct_intt_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 46 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 53 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_compute_ct_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 38 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 45 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_idle(mldsa_ctrl.sec_prog_cntr == MLDSA_RESET),
  .secondary_makehint(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_VALID_S + 104 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_makehint_start(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_VALID_S + 104 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_ntt_c(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_VALID_S && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_ntt_c_start(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_VALID_S && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_ntt_s1(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 9 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 15 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_ntt_s1_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 9 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 15 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_ntt_s2(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 16 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 23 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_ntt_s2_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 16 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 23 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_ntt_t(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 1 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 8 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_ntt_t_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_INIT_S + 1 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_INIT_S + 8 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_intt(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 1 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_intt_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 1 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_norm_check_ct0(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 4 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_norm_check_ct0_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 4 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_norm_check_r0(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 3 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_norm_check_r0_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 3 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_pwa(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 5 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_pwa_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 5 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_pwm(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 0 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_pwm_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 0 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_r_pws(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 2 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_r_pws_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 55 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 102 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 55) % 6) == 2 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_sk_decode(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_INIT_S && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_sk_decode_start(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_INIT_S && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_wait_for_c(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CHECK_C_VLD),
  .secondary_wait_for_w0(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CHECK_W0_VLD),
  .secondary_wait_for_y_and_w0(mldsa_ctrl.sec_prog_cntr == MLDSA_SIGN_CHECK_Y_VLD),
  .secondary_z_intt(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 1 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_z_intt_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 1 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_z_norm_check(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 3 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_z_norm_check_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 3 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_z_pwa(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 2 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_z_pwa_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 2 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_z_pwm(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 0 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_z_pwm_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 0 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START),
  .secondary_z_sig_encode(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 4 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_DONE),
  .secondary_z_sig_encode_start(mldsa_ctrl.sec_prog_cntr >= MLDSA_SIGN_VALID_S + 2 && mldsa_ctrl.sec_prog_cntr <= MLDSA_SIGN_VALID_S + 36 && ((mldsa_ctrl.sec_prog_cntr - MLDSA_SIGN_VALID_S - 2) % 5) == 4 && mldsa_ctrl.sign_ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)
);


endmodule


bind mldsa_ctrl fv_AdamsBridgeSecondary_ref_wrapper_m fv_AdamsBridgeSecondary_ref_wrapper();
