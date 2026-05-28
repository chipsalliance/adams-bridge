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
// | Created on 07.03.2025 at 14:02                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import mldsa_reg_pkg::*;
import abr_sha3_pkg::*;
import mldsa_sampler_pkg::*;
import mldsa_ctrl_pkg::*;
import mldsa_params_pkg::*;
import ntt_defines_pkg::*;
import AdamsBridge_functions::*;


module fv_mldsa_ctrl_m_m;


default clocking default_clk @(posedge (mldsa_ctrl.clk)); endclocking


st_FromApiType api_in;
assign api_in = '{instr: (mldsa_ctrl.cmd_reg==MLDSA_RESET?NoOp:(mldsa_ctrl.cmd_reg==MLDSA_KEYGEN?Keygen:(mldsa_ctrl.cmd_reg==MLDSA_SIGN?Sign:(mldsa_ctrl.cmd_reg==MLDSA_VERIFY?Verify:(mldsa_ctrl.cmd_reg==MLDSA_KEYGEN_SIGN?KeygenSign:NoOp)))))   , seed: { mldsa_ctrl.seed_reg[7], mldsa_ctrl.seed_reg[6], mldsa_ctrl.seed_reg[5], mldsa_ctrl.seed_reg[4], mldsa_ctrl.seed_reg[3],mldsa_ctrl.seed_reg[2],mldsa_ctrl.seed_reg[1],mldsa_ctrl.seed_reg[0]} , sign_rnd: 0,     tr: mldsa_ctrl.privatekey_reg.enc.tr , pk: 0, sk_in:0  };

st_ToApiType api_out;
assign api_out =  '{tr: mldsa_ctrl.privatekey_reg.enc.tr   , sk_out: mldsa_ctrl.privatekey_reg.raw};

st_DecomposeType to_decompose;
assign to_decompose =  '{source_addr: mldsa_ctrl.aux_src0_base_addr_o[0], destination: mldsa_ctrl.aux_dest_base_addr_o[0] };

st_NormCheckType to_norm_check;
assign to_norm_check = '{immediate:  mldsa_ctrl.prim_instr.imm[1:0] , source_addr: mldsa_ctrl.aux_src0_base_addr_o[0]};

st_NttType to_ntt;
assign to_ntt = '{  mode :((mldsa_ctrl.ntt_mode_o[0] == MLDSA_NTT)?Ntt: (mldsa_ctrl.ntt_mode_o[0] == MLDSA_INTT || mldsa_ctrl.ntt_mode_o[0] ==MLDSA_PWM_INTT)? Intt :(mldsa_ctrl.ntt_mode_o[0] == MLDSA_PWM)? Pwm:(mldsa_ctrl.ntt_mode_o[0] == MLDSA_PWA)? Pwa : (mldsa_ctrl.ntt_mode_o[0] == MLDSA_PWS)? Pws : (mldsa_ctrl.ntt_mode_o[0] == MLDSA_PWM_ACCUM_SMPL)? PwmAccuSampler :(mldsa_ctrl.ntt_mode_o[0] == MLDSA_PWM_SMPL)? PwmSampler : None)  , operand1: mldsa_ctrl.prim_instr.operand1[MLDSA_MEM_ADDR_WIDTH-1:0] , operand2: mldsa_ctrl.prim_instr.operand2[MLDSA_MEM_ADDR_WIDTH-1:0]  , destination: mldsa_ctrl.prim_instr.operand3[MLDSA_MEM_ADDR_WIDTH-1:0]   };

st_PkDecodeType to_pk_decode;
assign to_pk_decode = '{ destination: mldsa_ctrl.aux_dest_base_addr_o};

st_Power2RoundType to_power_2_round;
assign to_power_2_round = '{t_addr: mldsa_ctrl.aux_src0_base_addr_o[0]};

st_SigDecodeType to_sig_decode_h;
assign to_sig_decode_h = '{ destination: mldsa_ctrl.aux_dest_base_addr_o};

st_SigDecodeType to_sig_decode_z;
assign to_sig_decode_z = '{ destination: mldsa_ctrl.aux_dest_base_addr_o};

st_SkEncodeType to_sk_encode;
assign to_sk_encode = '{coeff_addr:mldsa_ctrl.aux_src0_base_addr_o[0]}   /*'{source_operand:mldsa_ctrl.aux_src0_base_addr_o[0] , destination_addr:mldsa_ctrl.aux_dest_base_addr_o[0]}*/;

st_UseHintType to_use_hint;
assign to_use_hint = '{ operand1: mldsa_ctrl.aux_src0_base_addr_o[0] , operand2: mldsa_ctrl.aux_src1_base_addr_o[0]};

st_FromApiType from_api;
assign from_api = '{ instr: (mldsa_ctrl.cmd_reg==MLDSA_RESET?NoOp:(mldsa_ctrl.cmd_reg==MLDSA_KEYGEN?Keygen:(mldsa_ctrl.cmd_reg==MLDSA_SIGN?Sign:(mldsa_ctrl.cmd_reg==MLDSA_VERIFY?Verify:(mldsa_ctrl.cmd_reg==MLDSA_KEYGEN_SIGN?KeygenSign:NoOp))))) , seed: mldsa_ctrl.seed_reg, sign_rnd : mldsa_ctrl.sign_rnd_reg, tr: mldsa_ctrl.privatekey_reg.enc.tr , pk:mldsa_ctrl.publickey_reg.enc.rho, sk_in: 0 };

st_RegsType registers;
assign registers =  '{
rho: mldsa_ctrl.rho_reg ,
rho_prime: mldsa_ctrl.rho_p_reg,
K: mldsa_ctrl.privatekey_reg.enc.K  ,
mu: mldsa_ctrl.mu_reg,
kappa: mldsa_ctrl.kappa_reg ,
c: mldsa_ctrl.signature_reg.enc.c
};

st_ToApiType to_api;
assign to_api =  '{
tr: mldsa_ctrl.privatekey_reg.enc.tr,
sk_out: mldsa_ctrl.privatekey_reg.raw
};


fv_mldsa_ctrl_m fv_mldsa_ctrl(
  .rst_n(mldsa_ctrl.rst_b),
  .clk(mldsa_ctrl.clk),

  // Ports
  .api_in(api_in),

  .as_addr_in(MLDSA_AS0_BASE),

  .as_intt_addr_in(MLDSA_AS0_INTT_BASE),

  .ay0_addr_in(MLDSA_AY0_BASE),

  .az_addr_in(MLDSA_AZ0_BASE),

  .c_addr_in(MLDSA_C_BASE),

  .c_ntt_addr_in(MLDSA_C_NTT_BASE),

  .c_valid_in(mldsa_ctrl.c_valid),

  .counter_in(mldsa_ctrl.counter_reg),

  .ct_addr_in(MLDSA_CT_BASE),

  .decompose_done_in(mldsa_ctrl.decompose_done_i),

  .entropy_in(mldsa_ctrl.lfsr_entropy_reg),

  .from_ext_mu(mldsa_ctrl.external_mu_reg),

  .from_ext_mu_mode_in(mldsa_ctrl.external_mu_mode),

  .from_keccak_piso(mldsa_ctrl.sampler_state_data_i[0]),

  .from_keccak_piso_vld_in(mldsa_ctrl.sampler_state_dv_i),

  .from_keygen_jump_in(mldsa_ctrl.keygen_signing_process),

  .hint_r_addr_in(MLDSA_HINT_R_0_BASE),

  .lfsr_seed_reg_id_in(MLDSA_DEST_LFSR_SEED_REG_ID),

  .msg_prime_in(mldsa_ctrl.msg_p_reg),

  .mu_reg_id_in(MLDSA_DEST_MU_REG_ID),

  .norm_check_done_in(mldsa_ctrl.normcheck_done_i),

  .ntt_done_in(!mldsa_ctrl.ntt_busy_i[0]),

  .pk_decode_done_in(mldsa_ctrl.pkdecode_done_i),

  .pk_ram_data(mldsa_ctrl.pubkey_ram_rdata),

  .power_2_round_done_in(mldsa_ctrl.power2round_done_i),

  .rho_id_in(MLDSA_RHO_ID),

  .rho_k_reg_id_in(MLDSA_DEST_K_RHO_REG_ID),

  .rho_prime_reg_id_in(MLDSA_DEST_RHO_P_REG_ID),

  .s1_addrs_in({MLDSA_S1_6_BASE,MLDSA_S1_5_BASE,MLDSA_S1_4_BASE,MLDSA_S1_3_BASE,MLDSA_S1_2_BASE,MLDSA_S1_1_BASE ,MLDSA_S1_0_BASE}),

  .s1_ntt_addrs_in({MLDSA_S1_6_NTT_BASE,MLDSA_S1_5_NTT_BASE,MLDSA_S1_4_NTT_BASE,MLDSA_S1_3_NTT_BASE,MLDSA_S1_2_NTT_BASE,MLDSA_S1_1_NTT_BASE,MLDSA_S1_0_NTT_BASE}),

  .s2_addrs_in({MLDSA_S2_7_BASE,MLDSA_S2_6_BASE,MLDSA_S2_5_BASE,MLDSA_S2_4_BASE,MLDSA_S2_3_BASE,MLDSA_S2_2_BASE,MLDSA_S2_1_BASE ,MLDSA_S2_0_BASE}),

  .sampler_done_in(!mldsa_ctrl.sampler_busy_i),

  .sampler_offset_f(mldsa_ctrl.sampler_src_offset_f),

  .sig_c_reg_id_in(MLDSA_DEST_SIG_C_REG_ID),

  .sig_decode_h_done_in(mldsa_ctrl.sigdecode_h_done_i),

  .sig_decode_z_done_in(mldsa_ctrl.sigdecode_z_done_i),

  .sig_vld_chk_done_in(mldsa_ctrl.signature_validity_chk_done),

  .sk_encode_done_in(mldsa_ctrl.skencode_done_i),

  .t_addrs_in({MLDSA_T7_BASE,MLDSA_T6_BASE,MLDSA_T5_BASE,MLDSA_T4_BASE,MLDSA_T3_BASE,MLDSA_T2_BASE,MLDSA_T1_BASE ,MLDSA_T0_BASE}),

  .temp_addr_in(((mldsa_ctrl.ntt_mode_o[0] == MLDSA_NTT && mldsa_ctrl.keygen_process) || (mldsa_ctrl.verifying_process)) ?
       MLDSA_TEMP0_BASE :
((mldsa_ctrl.ntt_mode_o[0] == MLDSA_INTT && mldsa_ctrl.keygen_process) || (mldsa_ctrl.signing_process))?
       MLDSA_TEMP3_BASE : MLDSA_TEMP0_BASE),

  .to_keccak_rdy(mldsa_ctrl.msg_rdy_i),

  .tr_reg_id_in(MLDSA_DEST_TR_REG_ID),

  .use_hint_done_in(mldsa_ctrl.decompose_done_i),

  .verify_res_reg_id_in(MLDSA_DEST_VERIFY_RES_REG_ID),

  .w0_addrs_in({MLDSA_W0_7_BASE,MLDSA_W0_6_BASE,MLDSA_W0_5_BASE,MLDSA_W0_4_BASE,MLDSA_W0_3_BASE,MLDSA_W0_2_BASE,MLDSA_W0_1_BASE,MLDSA_W0_0_BASE}),

  .w0_valid_in(mldsa_ctrl.w0_valid),

  .y_addrs_in({MLDSA_Y_6_BASE,MLDSA_Y_5_BASE,MLDSA_Y_4_BASE,MLDSA_Y_3_BASE,MLDSA_Y_2_BASE,MLDSA_Y_1_BASE ,MLDSA_Y_0_BASE}),

  .y_ntt_addrs_in({MLDSA_Y_6_NTT_BASE,MLDSA_Y_5_NTT_BASE,MLDSA_Y_4_NTT_BASE,MLDSA_Y_3_NTT_BASE,MLDSA_Y_2_NTT_BASE,MLDSA_Y_1_NTT_BASE,MLDSA_Y_0_NTT_BASE}),

  .y_valid_in(mldsa_ctrl.y_valid),

  .z_addrs_in({MLDSA_Z_6_BASE,MLDSA_Z_5_BASE,MLDSA_Z_4_BASE,MLDSA_Z_3_BASE,MLDSA_Z_2_BASE,MLDSA_Z_1_BASE,MLDSA_Z_0_BASE}),

  .z_ntt_addrs_in({MLDSA_Z_NTT_6_BASE,MLDSA_Z_NTT_5_BASE,MLDSA_Z_NTT_4_BASE,MLDSA_Z_NTT_3_BASE,MLDSA_Z_NTT_2_BASE,MLDSA_Z_NTT_1_BASE,MLDSA_Z_NTT_0_BASE}),

  .api_out_vld(mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E),
  .api_out(api_out),

  .enable_lfsr(mldsa_ctrl.lfsr_enable_o),

  .msg_start_o(mldsa_ctrl.msg_start_o),

  .set_c_valid_out(mldsa_ctrl.set_c_valid),

  .set_w0_valid_out(mldsa_ctrl.set_w0_valid),

  .set_y_valid_out(mldsa_ctrl.set_y_valid),

  .sha3_start_o(mldsa_ctrl.sha3_start_o),

  .to_decompose_vld(mldsa_ctrl.decompose_enable_o && !(mldsa_ctrl.prim_instr.opcode == MLDSA_UOP_USEHINT)),
  .to_decompose_rdy(1'b0),
  .to_decompose(to_decompose),

  .to_keccak_vld((mldsa_ctrl.msg_valid_o) ),
  .to_keccak(mldsa_ctrl.msg_data_o[0]),

  .to_norm_check_vld(mldsa_ctrl.normcheck_enable[0]),
  .to_norm_check_rdy(1'b0),
  .to_norm_check(to_norm_check),

  .to_ntt_vld(mldsa_ctrl.ntt_enable_o[0]),
  .to_ntt_rdy(1'b0),
  .to_ntt(to_ntt),

  .to_pk_decode_vld(mldsa_ctrl.pkdecode_enable_o),
  .to_pk_decode_rdy(1'b0),
  .to_pk_decode(to_pk_decode),

  .to_power_2_round_vld(mldsa_ctrl.power2round_enable_o),
  .to_power_2_round_rdy(1'b0),
  .to_power_2_round(to_power_2_round),

  .to_sampler_vld(mldsa_ctrl.sampler_start_o),
  .to_sampler_rdy(1'b0),
  .to_sampler(mldsa_ctrl.sampler_mode_o == MLDSA_SHAKE256?
   '{mode: Shake256  , destination: mldsa_ctrl.dest_base_addr_o} :
(mldsa_ctrl.sampler_mode_o == MLDSA_REJ_BOUNDED)?
  '{mode: RejBounded, destination: mldsa_ctrl.dest_base_addr_o}:
(mldsa_ctrl.sampler_mode_o == MLDSA_REJ_SAMPLER)?
   '{mode: RejSampler, destination: mldsa_ctrl.dest_base_addr_o}:
(mldsa_ctrl.sampler_mode_o == MLDSA_SAMPLE_IN_BALL)?
   '{mode: SampleInBall, destination: mldsa_ctrl.dest_base_addr_o}:
(mldsa_ctrl.sampler_mode_o == MLDSA_EXP_MASK)?
   '{mode: ExpMask, destination: mldsa_ctrl.dest_base_addr_o}:
 '0),

  .to_sig_decode_h_vld(mldsa_ctrl.sigdecode_h_enable_o),
  .to_sig_decode_h_rdy(1'b0),
  .to_sig_decode_h(to_sig_decode_h),

  .to_sig_decode_z_vld(mldsa_ctrl.sigdecode_z_enable_o),
  .to_sig_decode_z_rdy(1'b0),
  .to_sig_decode_z(to_sig_decode_z),

  .to_sk_encode_vld(mldsa_ctrl.skencode_enable_o),
  .to_sk_encode_rdy(1'b0),
  .to_sk_encode(to_sk_encode),

  .to_use_hint_vld(mldsa_ctrl.decompose_enable_o && (mldsa_ctrl.prim_instr.opcode == MLDSA_UOP_USEHINT)),
  .to_use_hint_rdy(1'b0),
  .to_use_hint(to_use_hint),

  // Registers
  .as_addr(MLDSA_AS0_BASE),
  .ay0_addr(MLDSA_AY0_BASE),
  .az_addr(MLDSA_AZ0_BASE),
  .counter(mldsa_ctrl.counter_reg),
  .counter_ForStmt_838_9(mldsa_ctrl.counter_reg),
  .entropy(mldsa_ctrl.lfsr_entropy_reg),
  .entropy_ForStmt_828_9(mldsa_ctrl.lfsr_entropy_reg),
  .from_api(from_api),
  .jump_if_invalid(),
  .keygen_ntt_s1_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 19) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 25))?
(mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 19)): 0),
  .keygen_pwm_a_idx( ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 26):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 35):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 44):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 53):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 62):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 71):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 80):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 89): 0),
  .keygen_t_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd34))?
   'd0:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd43))? 
   'd1:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd52))?
   'd2:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd61))?
   'd3:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd70))?
   'd4:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd79))?
   'd5:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd88))?
   'd6:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 'd89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 'd97))?
   'd7: 'd0),
  .msg_prime(mldsa_ctrl.msg_p_reg),
  .msg_prime_ForStmt_1178_9(mldsa_ctrl.msg_p_reg),
  .registers(registers),
  .rejbounded_counter(((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18))?
      (mldsa_ctrl.prim_prog_cntr - (MLDSA_KG_S+ 4)):0
),
  .rho_id(MLDSA_RHO_ID),
  .rho_id_ForStmt_920_11(MLDSA_RHO_ID),
  .rho_id_ForStmt_1272_11(MLDSA_RHO_ID),
  .s1_ntt_addrs_ForStmt_513_11({MLDSA_S1_6_NTT_BASE,MLDSA_S1_5_NTT_BASE,MLDSA_S1_4_NTT_BASE,MLDSA_S1_3_NTT_BASE,MLDSA_S1_2_NTT_BASE,MLDSA_S1_1_NTT_BASE,MLDSA_S1_0_NTT_BASE}),
  .sign_compute_w0_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 7))?
   'd0:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 15) )? 
   'd1:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 23))?
   'd2:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 31))?
   'd3:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 39))?
   'd4:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 47))?
   'd5:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 55))?
   'd6:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 63))?
   'd7: 'd0),
  .sign_compute_w0_y_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6))?
   (mldsa_ctrl.prim_prog_cntr - MLDSA_SIGN_MAKE_W_S):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) )? 
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +8)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +16)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +24)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +32)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +40)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +48)):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))?
   (mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_W_S +56)): 'd0),
  .sign_expand_mask_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_Y_S) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_Y_S+ 6))?
(mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_Y_S)): 0),
  .sign_ntt_y_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_Y_S+ 7) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_Y_S+ 13))?
(mldsa_ctrl.prim_prog_cntr - (MLDSA_SIGN_MAKE_Y_S +7)): 0),
  .sipo_chunk_idx(mldsa_ctrl.sampler_src_offset),
  .to_api(to_api),
  .verify_compute_az_idx(  ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 10):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 20):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 30):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 40):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 50):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 60):
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))?
   mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_EXP_A+ 70): 0),
  .verify_compute_w0_idx(    ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 9))?
  0:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 19))?
  1:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 29))?
  2:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 39))?
   3:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 49))?
   4:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 59))?
  5:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 69))?
  6:
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 79))?
 7: 0),
  .verify_norm_check_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_S+ 2) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_S+ 8))  ?
 mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_S+ 2) :
    0

),
  .verify_ntt_t_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_NTT_T1) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_NTT_T1+ 7)) ?
      mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_NTT_T1):0),
  .verify_ntt_z_idx(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_NTT_Z) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_NTT_Z+ 6)) ?
    mldsa_ctrl.prim_prog_cntr - (MLDSA_VERIFY_NTT_Z):0),
  .vld_lcl_w0(mldsa_ctrl.signature_validity_chk_done),
  .y_ntt_addrs_ForStmt_920_11({MLDSA_Y_6_NTT_BASE,MLDSA_Y_5_NTT_BASE,MLDSA_Y_4_NTT_BASE,MLDSA_Y_3_NTT_BASE,MLDSA_Y_2_NTT_BASE,MLDSA_Y_1_NTT_BASE,MLDSA_Y_0_NTT_BASE}),
  .z_ntt_addrs_ForStmt_1272_11({MLDSA_Z_NTT_6_BASE,MLDSA_Z_NTT_5_BASE,MLDSA_Z_NTT_4_BASE,MLDSA_Z_NTT_3_BASE,MLDSA_Z_NTT_2_BASE,MLDSA_Z_NTT_1_BASE,MLDSA_Z_NTT_0_BASE}),

  // States
  .idle((mldsa_ctrl.prim_prog_cntr == MLDSA_RESET) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)),
  .keygen_compute_t(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 34) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 43) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 52) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 61) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 70) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 79) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 88) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 97) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_compute_t_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 34) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 43) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 52) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 61) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 70) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 79) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 88) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 97) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_compute_tr_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_compute_tr_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_compute_tr_write_pk((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)&& !mldsa_ctrl.msg_done ),
  .keygen_compute_tr_write_pk_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .keygen_compute_tr_write_pk_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_compute_tr_write_pk_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 99)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)),
  .keygen_end_state((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_E) ),
  .keygen_expand_seed_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_expand_seed_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_expand_seed_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_expand_seed_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .keygen_intt_a(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 33) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 42) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 51) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 60) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 69) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 78) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 87) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 96) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_intt_a_idle(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 33) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 42) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 51) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 60) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 69) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 78) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 87) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 96) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .keygen_intt_a_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 33) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 42) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 51) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 60) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 69) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 78) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 87) || (mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 96) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&&  ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .keygen_jump_sign((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_JUMP_SIGN) ),
  .keygen_ntt_s1((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 19) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 25) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_ntt_s1_start((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 19) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 25) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) &&  ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .Keygen_ntt_s1_idle((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 19) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 25) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE) && (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .keygen_power_2_round((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 98)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_power_2_round_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 98)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) && ($past(mldsa_ctrl.ctrl_fsm_ps)==MLDSA_CTRL_IDLE)),
  .keygen_pwm_a((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_pwm_a_rejection_sampling_start((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_pwm_a_start((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) ),
  .keygen_pwm_a_write_immediate((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_last),
  .keygen_pwm_a_write_immediate_msg_done((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .keygen_pwm_a_write_rho((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95)))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_last && !mldsa_ctrl.msg_done ),
  .keygen_pwm_a_write_rho_SHA3_START((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
( (mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95))) 

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_pwm_a_write_rho_start((((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 26) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 32)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 35) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 41)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 44) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 50)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 53) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 59)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 62) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 68)) ||
( (mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 71) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 77)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 80) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 86)) ||
 ((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 89) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 95))) 

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)  && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .keygen_rejbounded_s1((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_rejbounded_s1_start((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_rejbounded_s2((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_rejbounded_s2_start((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_rnd_seed_done((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE) ),
  .keygen_rnd_seed_lfsr((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) && $past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE),
  .keygen_rnd_seed_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_rnd_seed_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)  && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .keygen_rnd_seed_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .keygen_sample_rnd_seed((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_sample_rnd_seed_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_sk_encode((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 100) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .keygen_sk_encode_start((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 100) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .keygen_write_counter((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .keygen_write_counter_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .keygen_write_entropy(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)) && !mldsa_ctrl.msg_done  ),
  .keygen_write_entropy_msg_done(((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)) && mldsa_ctrl.msg_done ),
  .keygen_write_rejbounded_immediate_s1((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)  && mldsa_ctrl.msg_last),
  .keygen_write_rejbounded_immediate_s1_msg_done((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)  && mldsa_ctrl.msg_done),
  .keygen_write_rejbounded_immediate_s2((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)  && mldsa_ctrl.msg_last),
  .keygen_write_rejbounded_immediate_s2_msg_done((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)  && mldsa_ctrl.msg_done),
  .keygen_write_rejbounded_input_s1((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)&& !mldsa_ctrl.msg_last && !mldsa_ctrl.msg_done ),
  .keygen_write_rejbounded_input_s1_SHA3_START((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_write_rejbounded_input_s1_start((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 4) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 10)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .keygen_write_rejbounded_input_s2((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18) 
&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_last && !mldsa_ctrl.msg_done ),
  .keygen_write_rejbounded_input_s2_SHA3_START((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .keygen_write_rejbounded_input_s2_start((mldsa_ctrl.prim_prog_cntr >= MLDSA_KG_S+ 11) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_KG_S+ 18) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .keygen_write_seed((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)&& !mldsa_ctrl.msg_last &&  !mldsa_ctrl.msg_done ),
  .keygen_write_seed_immediate((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_last ),
  .keygen_write_seed_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_KG_S+ 3) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_c( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_c_start( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_lfsr_seed_lfsr( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_lfsr_seed_sampling( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_lfsr_seed_sampling_start( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_lfsr_seed_SHA3_START((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START) ),
  .sign_compute_lfsr_seed_start( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_compute_lfsr_seed_wait((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_compute_lfsr_seed_write_counter((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_lfsr_seed_write_counter_msg_done((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_lfsr_seed_write_entropy((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done  ),
  .sign_compute_lfsr_seed_write_entropy_msg_done((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done ),
  .sign_compute_mu_idle((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .sign_compute_mu_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_mu_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_mu_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_compute_mu_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_compute_mu_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_compute_mu_write_msg_prime((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_mu_write_msg_prime_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_mu_write_tr((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_mu_write_tr_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_MU) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_rho_prime_sampling((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_H_RHO_P+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_rho_prime_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_rho_prime_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P)&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_compute_rho_prime_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P)&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_compute_rho_prime_wait_0((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_compute_rho_prime_wait_1((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_compute_rho_prime_write_K((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_rho_prime_write_K_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_rho_prime_write_mu((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_rho_prime_write_mu_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 2) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_rho_prime_write_sign_rnd((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_compute_rho_prime_write_sign_rnd_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_H_RHO_P+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_w0_intt(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 15) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 23) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 31) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 39) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 47) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 55) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 63) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_w0_intt_idle(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 15) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 23) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 31) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 39) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 47) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 55) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 63) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .sign_compute_w0_intt_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 15) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 23) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 31) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 39) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 47) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 55) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 63) )

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_w0_pwm(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_compute_w0_pwm_samp_ntt(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_w0_pwm_sampling_start(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_compute_w0_pwm_SHA3_START(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_compute_w0_pwm_start(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_compute_w0_pwm_write_immediate(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_last),
  .sign_compute_w0_pwm_write_immediate_msg_done(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_compute_w0_pwm_write_rho(((mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S      ) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 6) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S + 8) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 14) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +16) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 22) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +24) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 30) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +32) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 38) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 46) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +48) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 54) ||
(mldsa_ctrl.prim_prog_cntr >= MLDSA_SIGN_MAKE_W_S +56) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_SIGN_MAKE_W_S+ 62))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_last&& !mldsa_ctrl.msg_done ),
  .sign_decompose_w((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_decompose_w_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_end_of_challenge((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_CHL_E)),
  .sign_end_state((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_E)),
  .sign_expand_mask_done( (mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_LFSR_S+ 2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_expand_mask_sampling(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_expand_mask_sampling_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_expand_mask_SHA3_START(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_expand_mask_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&& (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_expand_mask_write_kappa_immediate(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_last),
  .sign_expand_mask_write_kappa_immediate_msg_done(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_expand_mask_write_rho_prime(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 1) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 2) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 3) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 4) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 5) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 6))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_last && !mldsa_ctrl.msg_done ),
  .sign_load_mu((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 65) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_load_mu_idle((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 65)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .sign_load_mu_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 65) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_load_mu_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 65)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_load_mu_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W_S+ 65)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)  && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_load_mu_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_W) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_ntt_y(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S +7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 8) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 9) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 10) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+11) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 12) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 13))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_ntt_y_idle(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S +7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 8) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 9) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 10) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+11) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 12) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 13))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .sign_ntt_y_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S +7) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 8) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 9) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 10) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+11) || (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 12) ||
 (mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_Y_S+ 13))

&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_check_mode((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_CHECK_MODE)),
  .sign_rnd_seed_lfsr((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S+ 2)  && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) && $past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE),
  .sign_rnd_seed_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_rnd_seed_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)  && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_rnd_seed_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S +1 ) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .sign_sample_in_ball_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_sample_in_ball_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_sample_in_ball_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .sign_sample_in_ball_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .sign_sample_in_ball_write_c((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_sample_in_ball_write_c_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_MAKE_C+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .sign_sample_rnd_seed((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .sign_sample_rnd_seed_start((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S+ 1) && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .sign_set_c_valid((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_SET_C) ),
  .sign_set_w0_valid((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_SET_W0) ),
  .sign_set_y_valid((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_SET_Y) ),
  .sign_wait_for_c_clear((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_CHECK_C_CLR) ),
  .sign_wait_for_w0_clear((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_CHECK_W0_CLR)),
  .sign_wait_for_y_and_w0_clear((mldsa_ctrl.prim_prog_cntr ==MLDSA_SIGN_CHECK_Y_CLR ) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)),
  .sign_write_counter((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)&& !mldsa_ctrl.msg_done ),
  .sign_write_counter_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S+ 1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD)&& mldsa_ctrl.msg_done),
  .sign_write_entropy((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .sign_write_entropy_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_SIGN_S)  &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .verify_check_mode((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_CHECK_MODE)),
  .verify_compute_az_pwm(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_az_pwm_start(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_az_sampling_start(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_az_SHA3_START(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START) ),
  .verify_compute_az_start(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .verify_compute_az_write_immediate(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps ==MLDSA_CTRL_MSG_LOAD ) && mldsa_ctrl.msg_last),
  .verify_compute_az_write_immediate_msg_done(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps ==MLDSA_CTRL_MSG_LOAD ) && mldsa_ctrl.msg_done),
  .verify_compute_az_write_rho(((mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 6) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 10) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 16) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 20) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 26) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 30) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 36) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 40) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 46) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 50) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 56) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 60) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 66) ||
 (mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_EXP_A+ 70) && (mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_EXP_A+ 76))

 && (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_last && !mldsa_ctrl.msg_done ),
  .verify_compute_mu_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_mu_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_mu_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .verify_compute_mu_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .verify_compute_mu_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .verify_compute_mu_write_msg_prime((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .verify_compute_mu_write_msg_prime_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .verify_compute_mu_write_tr((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .verify_compute_mu_write_tr_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_MU) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done ),
  .verify_compute_tr_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_tr_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_tr_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START) ),
  .verify_compute_tr_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)   && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .verify_compute_tr_write_pk((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .verify_compute_tr_write_pk_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_H_TR) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done ),
  .verify_compute_w0_intt(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 9)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 19)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 29)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 39)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 49)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 59)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 69)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 79))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_w0_intt_idle(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 9)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 19)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 29)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 39)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 49)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 59)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 69)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 79))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_IDLE)&&  (mldsa_ctrl.ctrl_fsm_ns != MLDSA_CTRL_IDLE)),
  .verify_compute_w0_intt_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 9)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 19)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 29)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 39)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 49)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 59)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 69)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 79))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_w0_pwm(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 7)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 17)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 27)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 37)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 47)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 57)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 67)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 77))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_w0_pwm_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 7)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 17)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 27)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 37)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 47)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 57)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 67)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 77))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_compute_w0_pws(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 8)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 18)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 28)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 38)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 48)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 58)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 68)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 78))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_compute_w0_pws_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 8)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 18)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 28)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 38)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 48)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 58)| (mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 68)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_EXP_A+ 78))&&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_end_state((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_E)),
  .verify_load_mu((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && !mldsa_ctrl.msg_done ),
  .verify_load_mu_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .verify_load_mu_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START) ),
  .verify_load_mu_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START)  && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .verify_load_mu_wait((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_WAIT)),
  .verify_mu_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+3) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_mu_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+3) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_norm_check((mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_S+8)&&(mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_S+2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_norm_check_start((mldsa_ctrl.prim_prog_cntr <= MLDSA_VERIFY_S+8)&&(mldsa_ctrl.prim_prog_cntr >= MLDSA_VERIFY_S+2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&& ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_ntt_c((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_ntt_c_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&& ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_ntt_t(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+2)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+3)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+4)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+5)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+6)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+7)) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_ntt_t_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+2)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+3)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+4)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+5)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+6)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_T1+7)) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&& ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_ntt_z(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+2)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+3)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+4)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+5)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+6)) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_ntt_z_start(((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+1)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+2)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+3)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+4)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+5)|(mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_NTT_Z+6)) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&& ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_pk_decode((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_pk_decode_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_S) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)&& ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_sample_in_ball_sampling((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_sample_in_ball_sampling_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START)),
  .verify_sample_in_ball_SHA3_START((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_SHA3_START)),
  .verify_sample_in_ball_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_START) && $past(mldsa_ctrl.sha3_start_o) && mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)),
  .verify_sample_in_ball_write_c((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && ! mldsa_ctrl.msg_start_o && !(mldsa_ctrl.sha3_start_o)&& !mldsa_ctrl.msg_done ),
  .verify_sample_in_ball_write_c_msg_done((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_MAKE_C) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_MSG_LOAD) && mldsa_ctrl.msg_done),
  .verify_sig_decode_h((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_sig_decode_h_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) && ($past(mldsa_ctrl.ctrl_fsm_ps) == MLDSA_CTRL_IDLE)),
  .verify_sig_decode_z((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_S+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_sig_decode_z_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_S+1) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) && ($past(mldsa_ctrl.ctrl_fsm_ps) ==MLDSA_CTRL_IDLE)),
  .verify_use_hint((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_DONE)),
  .verify_use_hint_start((mldsa_ctrl.prim_prog_cntr == MLDSA_VERIFY_RES+2) &&  (mldsa_ctrl.ctrl_fsm_ps == MLDSA_CTRL_FUNC_START) )
);


endmodule


bind mldsa_ctrl fv_mldsa_ctrl_m_m fv_mldsa_ctrl_m();
