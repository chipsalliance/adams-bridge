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
// | Created on 22.09.2025 at 08:47                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_reg_pkg::*;
import abr_sha3_pkg::*;
import abr_sampler_pkg::*;
import abr_ctrl_pkg::*;
import abr_params_pkg::*;
import ntt_defines_pkg::*;
import compress_defines_pkg::*;
import decompress_defines_pkg::*;
import mlkem_abr_ctrl_pkg::*;
import mlkem_functions::*;


module fv_mlkem_abr_ctrl_ref_wrapper_m;


default clocking default_clk @(posedge (abr_ctrl.clk)); endclocking


function logic unsigned [3:0] cbd_idx();
if(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)))
return abr_ctrl.abr_prog_cntr - (MLKEM_ENCAPS_S + 5);
else
return 0;
endfunction

function logic unsigned [2:0] mlkem_decap_ntt_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S + 4 && abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_S + 7 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_DECAPS_S + 4);
else 

  return 0;
endfunction

function logic unsigned [1:0] mlkem_decap_pwma_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_DECAPS_S + 9 && abr_ctrl.abr_prog_cntr <= MLKEM_DECAPS_S + 11 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_DECAPS_S + 9);
else 

  return 0;
endfunction

function logic unsigned [2:0] mlkem_encap_ntt_y_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 14 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 17 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_ENCAPS_S + 14);
else 

  return 0;
endfunction

function logic unsigned [2:0] mlkem_encap_pw_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 18 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 23 )
   return 0;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 24 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 29 )
   return 1;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 30 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 35 )
   return 2;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 36 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 41 )
   return 3;
else
  return 0;
endfunction

function logic unsigned [2:0] mlkem_encap_pwa_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_ENCAPS_S + 19) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_ENCAPS_S + 25) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_ENCAPS_S + 31) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_ENCAPS_S + 37) ;
else
  return 0;
endfunction

function logic unsigned [2:0] mlkem_encap_pwma_ty_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 43 && abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 45 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_ENCAPS_S + 43);
else 

  return 0;
endfunction

function logic unsigned [3:0] mlkem_keygen_ntt_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 9 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 16 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_KG_S + 9);
else 

  return 0;
endfunction

function logic unsigned [2:0] mlkem_keygen_pw_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 17 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 21 )
   return 0 ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 22 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 26 )
   return 1 ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 27 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 31)
   return 2 ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 32 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 36 )
   return 3;
else
  return 0;
endfunction

function logic unsigned [2:0] mlkem_keygen_pwa_idx();
if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20 )
   return abr_ctrl.abr_prog_cntr -( MLKEM_KG_S + 18) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_KG_S + 23) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30)
   return abr_ctrl.abr_prog_cntr -(MLKEM_KG_S + 28) ;
else if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33 && abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35 )
   return abr_ctrl.abr_prog_cntr -(MLKEM_KG_S + 33) ;
else
  return 0;
endfunction

function logic unsigned [3:0] N();
if(abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1&& abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8 )
   return abr_ctrl.abr_prog_cntr - (MLKEM_KG_S + 1);
else 
  return 0;
endfunction


st_FromApiType api_in;
assign api_in = '{ instr : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_NONE ? NoOp: 
abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_KEYGEN ? MlkemKeygen : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_ENCAPS ? MlkemEncap : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_DECAPS ? MlkemDecap: abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_KEYGEN_DEC ?MlkemkeygenDecap : NoOp , 
seed: 0,
seed_z: 0,
 rho: 0,
sigma: 0,
sigma_z: 0,
tr: 0
};

st_toCompressType to_compress;
assign to_compress = '{ mode : abr_ctrl.compress_mode_o , poly : abr_ctrl.compress_num_poly_o,
compare_mode_o: abr_ctrl.compress_compare_mode_o , src0 : abr_ctrl.aux_src0_base_addr_o[0] , src1 : abr_ctrl.aux_src1_base_addr_o[0], dest: abr_ctrl.aux_dest_base_addr_o[0]};

st_toDeCompressType to_decompress;
assign to_decompress = '{ mode : abr_ctrl.decompress_mode_o , poly : abr_ctrl.decompress_num_poly_o,src0 : abr_ctrl.aux_src0_base_addr_o[0] , src1 : abr_ctrl.aux_src1_base_addr_o[0], dest: abr_ctrl.aux_dest_base_addr_o[0]};

st_to_keccakType to_keccak;
assign to_keccak = '{data: abr_ctrl.msg_data_o[0], strobe: abr_ctrl.msg_strobe_o};

st_NttType to_ntt;
assign to_ntt = '{  mode :((abr_ctrl.ntt_mode_o == MLKEM_NTT)?Ntt: (abr_ctrl.ntt_mode_o == MLKEM_INTT || abr_ctrl.ntt_mode_o ==MLKEM_PWM_INTT)? Intt :(abr_ctrl.ntt_mode_o == MLKEM_PWM)? Pwm:(abr_ctrl.ntt_mode_o == MLKEM_PWA)? Pwa : (abr_ctrl.ntt_mode_o == MLKEM_PWS)? Pws : (abr_ctrl.ntt_mode_o == MLKEM_PWM_ACCUM_SMPL)? PwmAccuSampler :(abr_ctrl.ntt_mode_o == MLKEM_PWM_SMPL)? PwmSampler : PwmAccum)  , operand1: abr_ctrl.abr_instr.operand1[ABR_OPR_WIDTH-1:0] , operand2: abr_ctrl.abr_instr.operand2[ABR_OPR_WIDTH-1:0]  , destination: abr_ctrl.abr_instr.operand3[ABR_OPR_WIDTH-1:0] , masking_en: abr_ctrl.ntt_masking_en_o, shuffle_en: abr_ctrl.ntt_shuffling_en_o  }
;

st_FromApiType from_api;
assign from_api = '{ instr : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_NONE ? NoOp: 
abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_KEYGEN ? MlkemKeygen : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_ENCAPS ? MlkemEncap : abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_DECAPS ? MlkemDecap: abr_ctrl.abr_reg_hwif_out.MLKEM_CTRL.CTRL.value == MLKEM_KEYGEN_DEC ?MlkemkeygenDecap : NoOp , 
seed: abr_ctrl.mlkem_seed_d_reg,
seed_z: abr_ctrl.abr_scratch_reg.mlkem_enc.seed_z,
 rho: 0,
sigma: 0,
sigma_z: 0,
tr: 0
};


mlkem_abr_ctrl_m mlkem_abr_ctrl(
  .rst_n(abr_ctrl.rst_b),
  .clk(abr_ctrl.clk),

  // Ports
  .api_in(api_in),

  .as_addr_in(MLKEM_AS0_BASE),

  .ay_addr_in(MLKEM_AY0_BASE),

  .compress_done_in(abr_ctrl.compress_done_i),

  .decompress_done_in(abr_ctrl.decompress_done_i),

  .e2_addr_in(MLKEM_E2_BASE),

  .e_addrs_in({MLKEM_E3_BASE,MLKEM_E2_BASE,MLKEM_E1_BASE,MLKEM_E0_BASE}),

  .from_keccak_piso(abr_ctrl.sampler_state_data_i[0]),

  .from_keccak_piso_vld_in(abr_ctrl.sampler_state_dv_i),

  .mlkem_as0_addr_in(MLKEM_AS0_BASE),

  .mlkem_c1_addr_in(MLKEM_DEST_C1_MEM_OFFSET),

  .mlkem_c2_addr_in(MLKEM_DEST_C2_MEM_OFFSET),

  .mlkem_dk_addr_in(MLKEM_DEST_DK_MEM_OFFSET),

  .mlkem_ek_addr_in(MLKEM_DEST_EK_MEM_OFFSET),

  .mlkem_k_r_reg_id_in(MLKEM_DEST_K_R_REG_ID),

  .mlkem_k_reg_id_in(MLKEM_DEST_K_REG_ID),

  .mlkem_msg_mem_addr_in(MLKEM_DEST_MSG_MEM_OFFSET),

  .mlkem_rho_id_in(MLKEM_RHO_ID),

  .mlkem_rho_sigma_reg_id_in(MLKEM_DEST_RHO_SIGMA_REG_ID),

  .mlkem_sigma_id_in(MLKEM_SIGMA_ID),

  .mlkem_src_c1_mem_in(MLKEM_SRC_C1_MEM_OFFSET),

  .mlkem_src_c2_mem_in(MLKEM_SRC_C2_MEM_OFFSET),

  .mlkem_src_dk_mem_in(MLKEM_SRC_DK_MEM_OFFSET),

  .mlkem_src_ek_mem_in(MLKEM_SRC_EK_MEM_OFFSET),

  .mlkem_src_msg_mem_in(MLKEM_SRC_MSG_MEM_OFFSET),

  .mlkem_tr_reg_id_in(MLKEM_DEST_TR_REG_ID),

  .mu_addr_in(MLKEM_MU_BASE),

  .ntt_done_in(!abr_ctrl.ntt_busy_i),

  .s_addrs_in({MLKEM_S3_BASE,MLKEM_S2_BASE,MLKEM_S1_BASE,MLKEM_S0_BASE}),

  .sampler_done_in(!abr_ctrl.sampler_busy_i),

  .su_addr_in(MLKEM_SU_BASE),

  .su_masked_addr_in(MLKEM_SU_MASKED_BASE),

  .t_addrs_in({MLKEM_T3_BASE,MLKEM_T2_BASE,MLKEM_T1_BASE,MLKEM_T0_BASE}),

  .to_keccak_rdy(abr_ctrl.msg_rdy_i),

  .ty_addr_in(MLKEM_TY_BASE),

  .ty_masked_addr_in(MLKEM_TY_MASKED_BASE),

  .u_addrs_in({MLKEM_U3_BASE,MLKEM_U2_BASE,MLKEM_U1_BASE,MLKEM_U0_BASE}),

  .up_addrs_in({MLKEM_UP3_BASE,MLKEM_UP2_BASE,MLKEM_UP1_BASE,MLKEM_UP0_BASE}),

  .v_addr_in(MLKEM_V_BASE),

  .y_addrs_in({MLKEM_Y3_BASE,MLKEM_Y2_BASE,MLKEM_Y1_BASE,MLKEM_Y0_BASE}),

  .regs_api_in(),

  .api_out_vld(),
  .api_out(),

  .msg_start_o(abr_ctrl.msg_start_o),

  .sha3_start_o(abr_ctrl.sha3_start_o),

  .to_compress_vld(abr_ctrl.compress_enable_o),
  .to_compress_rdy(1'b0),
  .to_compress(to_compress),

  .to_decompress_vld(abr_ctrl.decompress_enable_o),
  .to_decompress_rdy(1'b0),
  .to_decompress(to_decompress),

  .to_keccak_vld(abr_ctrl.msg_valid_o),
  .to_keccak(to_keccak),

  .to_ntt_vld(abr_ctrl.ntt_enable_o),
  .to_ntt_rdy(1'b0),
  .to_ntt(to_ntt),

  .to_sampler_vld(abr_ctrl.sampler_start_o),
  .to_sampler_rdy(1'b0),
  .to_sampler(abr_ctrl.sampler_mode_o == ABR_SHA512?  '{mode: Sha512  , destination: abr_ctrl.dest_base_addr_o} :(abr_ctrl.sampler_mode_o == ABR_SHAKE256)? '{mode: Shake256, destination: abr_ctrl.dest_base_addr_o}:(abr_ctrl.sampler_mode_o == MLKEM_REJ_SAMPLER)?   '{mode: RejSampler, destination: abr_ctrl.dest_base_addr_o}:(abr_ctrl.sampler_mode_o == ABR_SHA256)?  '{mode: Sha256, destination: abr_ctrl.dest_base_addr_o}:(abr_ctrl.sampler_mode_o == ABR_CBD_SAMPLER)?   '{mode: Cbd, destination: abr_ctrl.dest_base_addr_o}:'{mode: Cbd, destination: abr_ctrl.dest_base_addr_o}),

  // Registers
  .as_addr(MLKEM_AS0_BASE),
  .ay_addr(MLKEM_AY0_BASE),
  .cbd_idx(cbd_idx()),
  .e2_addr(MLKEM_E_2_BASE),
  .e_addrs({MLKEM_E3_BASE,MLKEM_E2_BASE,MLKEM_E1_BASE,MLKEM_E0_BASE}),
  .from_api(from_api),
  .intermediate_value(),
  .mlkem_c1_addr(MLKEM_DEST_C1_MEM_OFFSET),
  .mlkem_c2_addr(MLKEM_DEST_C2_MEM_OFFSET),
  .mlkem_decap_ntt_idx(mlkem_decap_ntt_idx()),
  .mlkem_decap_pwma_idx(mlkem_decap_pwma_idx()),
  .mlkem_decaps_end_process(!abr_ctrl.mlkem_encaps_process),
  .mlkem_dk_addr(MLKEM_DEST_DK_MEM_OFFSET),
  .mlkem_ek_addr(MLKEM_DEST_EK_MEM_OFFSET),
  .mlkem_encap_ntt_y_idx(mlkem_encap_ntt_y_idx()),
  .mlkem_encap_pw_idx(mlkem_encap_pw_idx()),
  .mlkem_encap_pwa_idx(mlkem_encap_pwa_idx()),
  .mlkem_encap_pwma_ty_idx(mlkem_encap_pwma_ty_idx()),
  .mlkem_k_r_reg_id(MLKEM_DEST_K_R_REG_ID),
  .mlkem_k_reg_id(MLKEM_DEST_K_REG_ID),
  .mlkem_keygen_ntt_idx(mlkem_keygen_ntt_idx()),
  .mlkem_keygen_pw_idx(mlkem_keygen_pw_idx()),
  .mlkem_keygen_pwa_idx(mlkem_keygen_pwa_idx()),
  .mlkem_msg_mem_addr(MLKEM_DEST_MSG_MEM_OFFSET),
  .mlkem_rho_id(MLKEM_RHO_ID),
  .mlkem_rho_sigma_reg_id(MLKEM_DEST_RHO_SIGMA_REG_ID),
  .mlkem_src_c1_mem(MLKEM_SRC_C1_MEM_OFFSET),
  .mlkem_src_c2_mem(MLKEM_SRC_C2_MEM_OFFSET),
  .mlkem_src_dk_mem(MLKEM_SRC_DK_MEM_OFFSET),
  .mlkem_src_ek_mem(MLKEM_SRC_EK_MEM_OFFSET),
  .mlkem_src_msg_mem(MLKEM_SRC_MSG_MEM_OFFSET),
  .mlkem_tr_reg_id(MLKEM_DEST_TR_REG_ID),
  .mu_addr(MLKEM_MU_BASE),
  .N(N()),
  .rho_reg(abr_ctrl.abr_scratch_reg.mlkem_enc.rho),
  .s_addrs({MLKEM_S3_BASE,MLKEM_S2_BASE,MLKEM_S1_BASE,MLKEM_S0_BASE}),
  .sampled_value(),
  .sigma_reg(abr_ctrl.abr_scratch_reg.mlkem_enc.sigma),
  .sipo_chunk_idx(abr_ctrl.sampler_src_offset),
  .sk_ram_data(abr_ctrl.sk_ram_rdata),
  .su_addr(MLKEM_SU_BASE),
  .su_masked_addr(MLKEM_SU_MASKED_BASE),
  .t_addrs({MLKEM_T3_BASE,MLKEM_T2_BASE,MLKEM_T1_BASE,MLKEM_T0_BASE}),
  .tr_reg(abr_ctrl.abr_scratch_reg.mlkem_enc.tr),
  .ty_masked_addr(MLKEM_TY_MASKED_BASE),
  .u_addrs({MLKEM_U3_BASE,MLKEM_U2_BASE,MLKEM_U1_BASE,MLKEM_U0_BASE}),
  .up_addrs({MLKEM_UP3_BASE,MLKEM_UP2_BASE,MLKEM_UP1_BASE,MLKEM_UP0_BASE}),
  .v_addr(MLKEM_V_BASE),
  .y_addrs({MLKEM_Y3_BASE,MLKEM_Y2_BASE,MLKEM_Y1_BASE,MLKEM_Y0_BASE}),

  // States
  .idle((abr_ctrl.abr_prog_cntr == ABR_RESET)),
  .mlkem_decap_compress_msg((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 14) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_compress_msg_idle((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 14) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_decap_compress_msg_start((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 14) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_decap_decompress_s0(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 1) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_decompress_s0_idle(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 1) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_decompress_s0_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 1) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_decompress_u0(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 2) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_decompress_u0_idle(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 2) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)  && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_decompress_u0_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 2) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_decompress_v(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 3) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_decompress_v_idle(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 3) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)  && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_decompress_v_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 3) ) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_ek_sampling(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_decap_ek_sampling_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_decap_intt_su((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 12) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_intt_su_idle((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 12) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_intt_su_start((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 12) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_ntt(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 4) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 5) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 6) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 7)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_ntt_idle(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 4) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 5) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 6) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 7)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)  && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_ntt_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 4) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 5) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 6) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 7)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pwm_su((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 8) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_pwm_su_idle((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 8) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pwm_su_start((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 8) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pwma_su(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 9) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 10) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 11)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_pwma_su_idle(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 9) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 10) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 11)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE) && ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pwma_su_start(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 9) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 10) || (abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 11)) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pws_su((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 13) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE)),
  .mlkem_decap_pws_su_idle((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 13) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)&& ( abr_ctrl.abr_ctrl_fsm_ns == ABR_CTRL_FUNC_START)),
  .mlkem_decap_pws_su_start((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S + 13) && ( abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START)),
  .mlkem_decap_SHA256_START(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_decap_write_ek(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && !abr_ctrl.msg_done),
  .mlkem_decap_write_ek_init(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD) && !abr_ctrl.msg_done),
  .mlkem_decap_write_ek_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && (abr_ctrl.msg_done)),
  .mlkem_decap_write_ek_START(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_S ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_compress_c1(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 50) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_compress_c1_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 50) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)&& ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_compress_c1_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 50) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_compress_c2(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 51) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_compress_c2_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 51) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_compress_c2_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 51) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_compress_first(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 1) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_compress_first_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 1) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_ct_shake256(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_ct_shake256_done(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_decompress_mu(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 47) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_decompress_mu_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 47) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_decompress_mu_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 47) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_decompress_t0(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S ) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_decompress_t0_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S ) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_ek_sampling(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_ek_sampling_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_end(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_E) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_encap_intt(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 22) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 28) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 34) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 40))  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_intt_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 22) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 28) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 34) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 40) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_intt_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 22) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 28) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 34) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 40) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_intt_v(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 46) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_intt_v_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 46) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_intt_v_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 46) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_ld_SHA512_START(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) ) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_encap_ld_SHAKE256_START(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK) )   && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_encap_ntt_y(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 14 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 17)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_ntt_y_idle(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 14 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 17)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)  && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_ntt_y_start(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 14 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 17)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 23) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 29) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 35) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 41) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_pwa_e2(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 48) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_pwa_e2_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 48) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)  && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa_e2_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 48) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 23) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 29) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 35) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 41) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 23) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 29) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 35) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 41) )  &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa_v(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 49) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_pwa_v_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 49) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)  && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwa_v_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 49) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwm(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36))  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_pwm_a((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )   )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_pwm_a_ntt_start((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwm_a_rejection_sampling_start((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_encap_pwm_a_write_immediate((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_last),
  .mlkem_encap_pwm_a_write_immediate_msg_done((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_pwm_a_write_rho((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_encap_pwm_a_write_rho_init((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_encap_pwm_a_write_rho_SHA3_START((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_encap_pwm_a_write_rho_start((((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 19) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 21) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 25) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 27) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 31) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 33) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 37) && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 39) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START) ),
  .mlkem_encap_pwm_ntt_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwm_rejection_sampling_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwm_ty(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 42 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_encap_pwm_ty_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 42 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)  && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START) ),
  .mlkem_encap_pwm_ty_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 42 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_encap_pwm_write_immediate(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_last),
  .mlkem_encap_pwm_write_immediate_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_pwm_write_rho(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_last && !abr_ctrl.msg_done),
  .mlkem_encap_pwm_write_rho_init(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_last && !abr_ctrl.msg_done),
  .mlkem_encap_pwm_write_rho_SHA3_START(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) ) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_encap_pwm_write_rho_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 18) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 24) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 30) || (abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 36) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_pwma_ty(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 43 ) ||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 44 )||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 45 )) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_encap_pwma_ty_idle(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 43 ) ||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 44 )||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 45 )) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_pwma_ty_start(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 43 ) ||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 44 )||(abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 45 )) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_encap_sha512(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_encap_sha512_done(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_encap_SHA256_START(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_encap_write_ct_msg_256(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && !abr_ctrl.msg_done ),
  .mlkem_encap_write_ct_msg_256_init(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)&& !abr_ctrl.msg_done ),
  .mlkem_encap_write_ct_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_write_ek(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_done),
  .mlkem_encap_write_ek_init(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_done),
  .mlkem_encap_write_ek_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_write_ek_START(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 2 ) ) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_write_msg(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_done),
  .mlkem_encap_write_msg_256(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_done),
  .mlkem_encap_write_msg_256_done(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& abr_ctrl.msg_done),
  .mlkem_encap_write_msg_256_init(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_done),
  .mlkem_encap_write_msg_256_START(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_write_msg_256_wait(((abr_ctrl.abr_prog_cntr == MLKEM_DECAPS_CHK + 1) )   && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_WAIT)),
  .mlkem_encap_write_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_write_msg_init(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_done),
  .mlkem_encap_write_msg_START(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 3) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_write_msg_wait(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_WAIT) ),
  .mlkem_encap_write_tr_msg(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_done),
  .mlkem_encap_write_tr_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_write_tr_msg_init(((abr_ctrl.abr_prog_cntr == MLKEM_ENCAPS_S + 4) )  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_done),
  .mlkem_encap_y_e1_e2_msg_start(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13))  && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START)),
  .mlkem_encap_y_e1_e2_SHA3_START(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START)),
  .mlkem_encap_y_e1_e2_sha_sampling(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE)),
  .mlkem_encap_y_e1_e2_sha_sampling_start(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START)),
  .mlkem_encap_y_e1_e2_write(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_encap_y_e1_e2_write_immediate(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_last),
  .mlkem_encap_y_e1_e2_write_msg_done(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_encap_y_e1_e2_write_msg_init(((abr_ctrl.abr_prog_cntr >= MLKEM_ENCAPS_S + 5 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_ENCAPS_S + 13)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_keygen_cbd_msg_start(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START) ),
  .mlkem_keygen_cbd_sampling(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_cbd_sampling_start(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_cbd_SHA3_START(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START) && $past(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)),
  .mlkem_keygen_cbd_write_immediate(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_last),
  .mlkem_keygen_cbd_write_msg(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_keygen_cbd_write_msg_done(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done),
  .mlkem_keygen_cbd_write_msg_init(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 1 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 8)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_keygen_compress_dk(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 38 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_compress_dk_idle(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 38 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)&&  ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_compress_dk_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 38 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_compress_ek(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 37 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_compress_ek_idle(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 37 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_compress_ek_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 37 ) ) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_ek_sampling((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE) ),
  .mlkem_keygen_ek_sampling_start((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_ntt(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 9 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 16)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_ntt_idle(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 9 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 16)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) &&  ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START)),
  .mlkem_keygen_ntt_start(((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 9 )  && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 16)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_Keygen_pwa(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 21 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 26)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 31) || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 36)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_Keygen_pwa_idle(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 21 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 26)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 31) || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 36)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE) && ( (abr_ctrl.abr_ctrl_fsm_ns) == ABR_CTRL_FUNC_START) ),
  .mlkem_Keygen_pwa_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 21 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 26)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 31) || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 36)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_pwm(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_pwm_a((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_DONE) ),
  .mlkem_keygen_pwm_a_rejection_sampling_start((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START),
  .mlkem_keygen_pwm_a_start((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START),
  .mlkem_keygen_pwm_a_write_immediate((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD && abr_ctrl.msg_last),
  .mlkem_keygen_pwm_a_write_immediate_msg_done((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD && abr_ctrl.msg_done),
  .mlkem_keygen_pwm_a_write_rho((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_last && !abr_ctrl.msg_done),
  .mlkem_keygen_pwm_a_write_rho_init((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done),
  .mlkem_keygen_pwm_a_write_rho_SHA3_START((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START) && ( $past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_keygen_pwm_a_write_rho_start((((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 18) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 20) ) || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 23) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 25) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 28) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 30) )  || 
((abr_ctrl.abr_prog_cntr >= MLKEM_KG_S + 33) && (abr_ctrl.abr_prog_cntr <= MLKEM_KG_S + 35) )  )  
&& (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START),
  .mlkem_keygen_pwm_ntt_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_pwm_rejection_sampling_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_pwm_write_immediate(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)  && abr_ctrl.msg_last),
  .mlkem_keygen_pwm_write_immediate_msg_done(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)  && abr_ctrl.msg_done),
  .mlkem_keygen_pwm_write_rho(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_keygen_pwm_write_rho_init(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
&& !abr_ctrl.msg_last && !abr_ctrl.msg_done ),
  .mlkem_keygen_pwm_write_rho_SHA3_START(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_SHA3_START) && $past(abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_IDLE)),
  .mlkem_keygen_pwm_write_rho_start(((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 17 )  || (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +22)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +27)|| (abr_ctrl.abr_prog_cntr == MLKEM_KG_S +32)) &&  ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_START) ),
  .mlkem_keygen_rnd_seed_SHA3_START((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_SHA3_START) && ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_keygen_rnd_seed_start((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_START) ),
  .mlkem_keygen_seed_sha_sampling((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_DONE) ),
  .mlkem_keygen_seed_sha_sampling_start((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_FUNC_START) ),
  .mlkem_keygen_SHA256_START((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_SHA3_START) && ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_IDLE)),
  .mlkem_keygen_write_ek((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_done ),
  .mlkem_keygen_write_ek_init((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && ( (abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)&& ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)
 && !abr_ctrl.msg_done ),
  .mlkem_keygen_write_ek_msg_done((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done ),
  .mlkem_keygen_write_ek_START((abr_ctrl.abr_prog_cntr == MLKEM_KG_S + 39) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_START) ),
  .mlkem_keygen_write_seed((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) && !abr_ctrl.msg_last && !abr_ctrl.msg_done && ($past(abr_ctrl.abr_ctrl_fsm_ps) == ABR_CTRL_MSG_LOAD)),
  .mlkem_keygen_write_seed_immediate((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_last),
  .mlkem_keygen_write_seed_init((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) && !abr_ctrl.msg_last && !abr_ctrl.msg_done && ($past(abr_ctrl.abr_ctrl_fsm_ps) != ABR_CTRL_MSG_LOAD)),
  .mlkem_keygen_write_seed_msg_done((abr_ctrl.abr_prog_cntr == MLKEM_KG_S ) && (abr_ctrl.abr_ctrl_fsm_ps == ABR_CTRL_MSG_LOAD) && abr_ctrl.msg_done)
);


endmodule


bind abr_ctrl fv_mlkem_abr_ctrl_ref_wrapper_m fv_mlkem_abr_ctrl_ref_wrapper();
