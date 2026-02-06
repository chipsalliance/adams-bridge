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
// | Created on 11.09.2025 at 19:50                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import mlkem_abr_ctrl_pkg::*;
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


module mlkem_abr_ctrl_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input st_FromApiType api_in,

  input logic api_out_vld,
  input st_ToApiType api_out,

  input logic unsigned [14:0] mlkem_rho_sigma_reg_id_in,

  input logic unsigned [14:0] mlkem_sigma_id_in,

  input logic unsigned [14:0] mlkem_rho_id_in,

  input logic unsigned [14:0] mlkem_as0_addr_in,

  input logic unsigned [14:0] mlkem_ek_addr_in,

  input logic unsigned [14:0] mlkem_dk_addr_in,

  input logic unsigned [14:0] mlkem_k_r_reg_id_in,

  input logic unsigned [14:0] mlkem_msg_mem_addr_in,

  input logic unsigned [14:0] mlkem_k_reg_id_in,

  input logic unsigned [14:0] mlkem_tr_reg_id_in,

  input logic unsigned [14:0] mlkem_c1_addr_in,

  input logic unsigned [14:0] mlkem_c2_addr_in,

  input logic unsigned [14:0] mlkem_src_dk_mem_in,

  input logic unsigned [14:0] mlkem_src_ek_mem_in,

  input logic unsigned [14:0] mlkem_src_c1_mem_in,

  input logic unsigned [14:0] mlkem_src_c2_mem_in,

  input logic unsigned [14:0] mlkem_src_msg_mem_in,

  input logic unsigned [14:0] su_addr_in,

  input logic unsigned [14:0] su_masked_addr_in,

  input logic unsigned [14:0] v_addr_in,

  input logic unsigned [14:0] ay_addr_in,

  input logic unsigned [14:0] as_addr_in,

  input logic unsigned [14:0] ty_addr_in,

  input logic unsigned [14:0] ty_masked_addr_in,

  input logic unsigned [14:0] e2_addr_in,

  input logic unsigned [14:0] mu_addr_in,

  input a_unsigned_15_4 s_addrs_in,

  input a_unsigned_15_4 e_addrs_in,

  input a_unsigned_15_4 y_addrs_in,

  input a_unsigned_15_4 t_addrs_in,

  input a_unsigned_15_4 u_addrs_in,

  input a_unsigned_15_4 up_addrs_in,

  input logic to_keccak_vld,
  input st_to_keccakType to_keccak,

  input logic to_keccak_rdy,

  input logic unsigned [1599:0] from_keccak_piso,

  input logic from_keccak_piso_vld_in,

  input logic to_sampler_vld,
  input logic to_sampler_rdy,
  input st_ToSamplerType to_sampler,

  input logic sampler_done_in,

  input logic to_ntt_vld,
  input logic to_ntt_rdy,
  input st_NttType to_ntt,

  input logic ntt_done_in,

  input logic to_compress_vld,
  input logic to_compress_rdy,
  input st_toCompressType to_compress,

  input logic compress_done_in,

  input logic to_decompress_vld,
  input logic to_decompress_rdy,
  input st_toDeCompressType to_decompress,

  input logic decompress_done_in,

  input logic sha3_start_o,

  input logic msg_start_o,

  input st_RegsApiType regs_api_in,

  // Registers
  input logic unsigned [3:0] N,
  input logic unsigned [14:0] as_addr,
  input logic unsigned [14:0] ay_addr,
  input logic unsigned [3:0] cbd_idx,
  input logic unsigned [14:0] e2_addr,
  input a_unsigned_15_4 e_addrs,
  input st_FromApiType from_api,
  input logic unsigned [1599:0] intermediate_value,
  input logic unsigned [14:0] mlkem_c1_addr,
  input logic unsigned [14:0] mlkem_c2_addr,
  input logic unsigned [2:0] mlkem_decap_ntt_idx,
  input logic unsigned [1:0] mlkem_decap_pwma_idx,
  input logic mlkem_decaps_end_process,
  input logic unsigned [14:0] mlkem_dk_addr,
  input logic unsigned [14:0] mlkem_ek_addr,
  input logic unsigned [2:0] mlkem_encap_ntt_y_idx,
  input logic unsigned [2:0] mlkem_encap_pw_idx,
  input logic unsigned [2:0] mlkem_encap_pwa_idx,
  input logic unsigned [2:0] mlkem_encap_pwma_ty_idx,
  input logic unsigned [14:0] mlkem_k_r_reg_id,
  input logic unsigned [14:0] mlkem_k_reg_id,
  input logic unsigned [3:0] mlkem_keygen_ntt_idx,
  input logic unsigned [2:0] mlkem_keygen_pw_idx,
  input logic unsigned [2:0] mlkem_keygen_pwa_idx,
  input logic unsigned [14:0] mlkem_msg_mem_addr,
  input logic unsigned [14:0] mlkem_rho_id,
  input logic unsigned [14:0] mlkem_rho_sigma_reg_id,
  input logic unsigned [14:0] mlkem_src_c1_mem,
  input logic unsigned [14:0] mlkem_src_c2_mem,
  input logic unsigned [14:0] mlkem_src_dk_mem,
  input logic unsigned [14:0] mlkem_src_ek_mem,
  input logic unsigned [14:0] mlkem_src_msg_mem,
  input logic unsigned [14:0] mlkem_tr_reg_id,
  input logic unsigned [14:0] mu_addr,
  input logic unsigned [255:0] rho_reg,
  input a_unsigned_15_4 s_addrs,
  input logic unsigned [1599:0] sampled_value,
  input logic unsigned [255:0] sigma_reg,
  input logic unsigned [15:0] sipo_chunk_idx,
  input logic unsigned [63:0] sk_ram_data,
  input logic unsigned [14:0] su_addr,
  input logic unsigned [14:0] su_masked_addr,
  input a_unsigned_15_4 t_addrs,
  input logic unsigned [255:0] tr_reg,
  input logic unsigned [14:0] ty_masked_addr,
  input a_unsigned_15_4 u_addrs,
  input a_unsigned_15_4 up_addrs,
  input logic unsigned [14:0] v_addr,
  input a_unsigned_15_4 y_addrs,

  // States
  input logic idle,
  input logic mlkem_keygen_rnd_seed_SHA3_START,
  input logic mlkem_keygen_rnd_seed_start,
  input logic mlkem_keygen_write_seed_init,
  input logic mlkem_keygen_write_seed,
  input logic mlkem_keygen_write_seed_immediate,
  input logic mlkem_keygen_write_seed_msg_done,
  input logic mlkem_keygen_seed_sha_sampling_start,
  input logic mlkem_keygen_seed_sha_sampling,
  input logic mlkem_keygen_cbd_SHA3_START,
  input logic mlkem_keygen_cbd_msg_start,
  input logic mlkem_keygen_cbd_write_msg_init,
  input logic mlkem_keygen_cbd_write_msg,
  input logic mlkem_keygen_cbd_write_immediate,
  input logic mlkem_keygen_cbd_write_msg_done,
  input logic mlkem_keygen_cbd_sampling_start,
  input logic mlkem_keygen_cbd_sampling,
  input logic mlkem_keygen_ntt_idle,
  input logic mlkem_keygen_ntt_start,
  input logic mlkem_keygen_ntt,
  input logic mlkem_keygen_pwm_write_rho_SHA3_START,
  input logic mlkem_keygen_pwm_write_rho_start,
  input logic mlkem_keygen_pwm_write_rho_init,
  input logic mlkem_keygen_pwm_write_rho,
  input logic mlkem_keygen_pwm_write_immediate,
  input logic mlkem_keygen_pwm_write_immediate_msg_done,
  input logic mlkem_keygen_pwm_rejection_sampling_start,
  input logic mlkem_keygen_pwm_ntt_start,
  input logic mlkem_keygen_pwm,
  input logic mlkem_keygen_pwm_a_write_rho_SHA3_START,
  input logic mlkem_keygen_pwm_a_write_rho_start,
  input logic mlkem_keygen_pwm_a_write_rho_init,
  input logic mlkem_keygen_pwm_a_write_rho,
  input logic mlkem_keygen_pwm_a_write_immediate,
  input logic mlkem_keygen_pwm_a_write_immediate_msg_done,
  input logic mlkem_keygen_pwm_a_rejection_sampling_start,
  input logic mlkem_keygen_pwm_a_start,
  input logic mlkem_keygen_pwm_a,
  input logic mlkem_Keygen_pwa_idle,
  input logic mlkem_Keygen_pwa_start,
  input logic mlkem_Keygen_pwa,
  input logic mlkem_keygen_compress_ek_idle,
  input logic mlkem_keygen_compress_ek_start,
  input logic mlkem_keygen_compress_ek,
  input logic mlkem_keygen_compress_dk_idle,
  input logic mlkem_keygen_compress_dk_start,
  input logic mlkem_keygen_compress_dk,
  input logic mlkem_keygen_SHA256_START,
  input logic mlkem_keygen_write_ek_START,
  input logic mlkem_keygen_write_ek_init,
  input logic mlkem_keygen_write_ek,
  input logic mlkem_keygen_write_ek_msg_done,
  input logic mlkem_keygen_ek_sampling_start,
  input logic mlkem_keygen_ek_sampling,
  input logic mlkem_decap_SHA256_START,
  input logic mlkem_decap_write_ek_START,
  input logic mlkem_decap_write_ek_init,
  input logic mlkem_decap_write_ek,
  input logic mlkem_decap_write_ek_msg_done,
  input logic mlkem_decap_ek_sampling_start,
  input logic mlkem_decap_ek_sampling,
  input logic mlkem_decap_decompress_s0_idle,
  input logic mlkem_decap_decompress_s0_start,
  input logic mlkem_decap_decompress_s0,
  input logic mlkem_decap_decompress_u0_idle,
  input logic mlkem_decap_decompress_u0_start,
  input logic mlkem_decap_decompress_u0,
  input logic mlkem_decap_decompress_v_idle,
  input logic mlkem_decap_decompress_v_start,
  input logic mlkem_decap_decompress_v,
  input logic mlkem_decap_ntt_idle,
  input logic mlkem_decap_ntt_start,
  input logic mlkem_decap_ntt,
  input logic mlkem_decap_pwm_su_idle,
  input logic mlkem_decap_pwm_su_start,
  input logic mlkem_decap_pwm_su,
  input logic mlkem_decap_pwma_su_idle,
  input logic mlkem_decap_pwma_su_start,
  input logic mlkem_decap_pwma_su,
  input logic mlkem_decap_intt_su_idle,
  input logic mlkem_decap_intt_su_start,
  input logic mlkem_decap_intt_su,
  input logic mlkem_decap_pws_su_idle,
  input logic mlkem_decap_pws_su_start,
  input logic mlkem_decap_pws_su,
  input logic mlkem_decap_compress_msg_idle,
  input logic mlkem_decap_compress_msg_start,
  input logic mlkem_decap_compress_msg,
  input logic mlkem_encap_decompress_t0_start,
  input logic mlkem_encap_decompress_t0,
  input logic mlkem_encap_compress_first_start,
  input logic mlkem_encap_compress_first,
  input logic mlkem_encap_SHA256_START,
  input logic mlkem_encap_write_ek_START,
  input logic mlkem_encap_write_ek_init,
  input logic mlkem_encap_write_ek,
  input logic mlkem_encap_write_ek_msg_done,
  input logic mlkem_encap_ek_sampling_start,
  input logic mlkem_encap_ek_sampling,
  input logic mlkem_encap_ld_SHA512_START,
  input logic mlkem_encap_write_msg_START,
  input logic mlkem_encap_write_msg_init,
  input logic mlkem_encap_write_msg,
  input logic mlkem_encap_write_msg_done,
  input logic mlkem_encap_write_msg_wait,
  input logic mlkem_encap_write_tr_msg_init,
  input logic mlkem_encap_write_tr_msg,
  input logic mlkem_encap_write_tr_msg_done,
  input logic mlkem_encap_sha512,
  input logic mlkem_encap_sha512_done,
  input logic mlkem_encap_y_e1_e2_SHA3_START,
  input logic mlkem_encap_y_e1_e2_msg_start,
  input logic mlkem_encap_y_e1_e2_write_msg_init,
  input logic mlkem_encap_y_e1_e2_write,
  input logic mlkem_encap_y_e1_e2_write_immediate,
  input logic mlkem_encap_y_e1_e2_write_msg_done,
  input logic mlkem_encap_y_e1_e2_sha_sampling_start,
  input logic mlkem_encap_y_e1_e2_sha_sampling,
  input logic mlkem_encap_ntt_y_idle,
  input logic mlkem_encap_ntt_y_start,
  input logic mlkem_encap_ntt_y,
  input logic mlkem_encap_pwm_write_rho_SHA3_START,
  input logic mlkem_encap_pwm_write_rho_start,
  input logic mlkem_encap_pwm_write_rho_init,
  input logic mlkem_encap_pwm_write_rho,
  input logic mlkem_encap_pwm_write_immediate,
  input logic mlkem_encap_pwm_write_immediate_msg_done,
  input logic mlkem_encap_pwm_rejection_sampling_start,
  input logic mlkem_encap_pwm_ntt_start,
  input logic mlkem_encap_pwm,
  input logic mlkem_encap_pwm_a_write_rho_SHA3_START,
  input logic mlkem_encap_pwm_a_write_rho_start,
  input logic mlkem_encap_pwm_a_write_rho_init,
  input logic mlkem_encap_pwm_a_write_rho,
  input logic mlkem_encap_pwm_a_write_immediate,
  input logic mlkem_encap_pwm_a_write_immediate_msg_done,
  input logic mlkem_encap_pwm_a_rejection_sampling_start,
  input logic mlkem_encap_pwm_a_ntt_start,
  input logic mlkem_encap_pwm_a,
  input logic mlkem_encap_intt_idle,
  input logic mlkem_encap_intt_start,
  input logic mlkem_encap_intt,
  input logic mlkem_encap_pwa_idle,
  input logic mlkem_encap_pwa_start,
  input logic mlkem_encap_pwa,
  input logic mlkem_encap_pwm_ty_idle,
  input logic mlkem_encap_pwm_ty_start,
  input logic mlkem_encap_pwm_ty,
  input logic mlkem_encap_pwma_ty_idle,
  input logic mlkem_encap_pwma_ty_start,
  input logic mlkem_encap_pwma_ty,
  input logic mlkem_encap_intt_v_idle,
  input logic mlkem_encap_intt_v_start,
  input logic mlkem_encap_intt_v,
  input logic mlkem_encap_decompress_mu_idle,
  input logic mlkem_encap_decompress_mu_start,
  input logic mlkem_encap_decompress_mu,
  input logic mlkem_encap_pwa_e2_idle,
  input logic mlkem_encap_pwa_e2_start,
  input logic mlkem_encap_pwa_e2,
  input logic mlkem_encap_pwa_v_idle,
  input logic mlkem_encap_pwa_v_start,
  input logic mlkem_encap_pwa_v,
  input logic mlkem_encap_compress_c1_idle,
  input logic mlkem_encap_compress_c1_start,
  input logic mlkem_encap_compress_c1,
  input logic mlkem_encap_compress_c2_idle,
  input logic mlkem_encap_compress_c2_start,
  input logic mlkem_encap_compress_c2,
  input logic mlkem_encap_end,
  input logic mlkem_encap_ld_SHAKE256_START,
  input logic mlkem_encap_write_msg_256_START,
  input logic mlkem_encap_write_msg_256_init,
  input logic mlkem_encap_write_msg_256,
  input logic mlkem_encap_write_msg_256_done,
  input logic mlkem_encap_write_msg_256_wait,
  input logic mlkem_encap_write_ct_msg_256_init,
  input logic mlkem_encap_write_ct_msg_256,
  input logic mlkem_encap_write_ct_msg_done,
  input logic mlkem_encap_ct_shake256,
  input logic mlkem_encap_ct_shake256_done
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_15_4 e_addrs_0_i;
assign e_addrs_0_i = '{0: 15'd0,
  1: 15'd0,
  2: 15'd0,
  3: 15'd0
};

st_FromApiType from_api_0_i;
assign from_api_0_i = '{instr: NoOp,
  seed: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0 },
  seed_z: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0 },
  rho: 256'd0,
  sigma: 512'd0,
  sigma_z: 256'd0,
  tr: 512'd0
};

st_toDeCompressType to_decompress_0_i;
assign to_decompress_0_i = '{mode: 2'd3,
  poly: 3'd4,
  src0: mlkem_src_ek_mem_in,
  src1: 15'd0,
  dest: t_addrs_in[64'd0]
};

st_to_keccakType to_keccak_0_i;
assign to_keccak_0_i = '{data: func_concat_seed(from_api.seed, ({ 1'd0, sipo_chunk_idx[1:0]} )),
  strobe: 8'hFF
};

st_to_keccakType to_keccak_1_i;
assign to_keccak_1_i = '{data: 64'h4,
  strobe: 8'h1
};

st_ToSamplerType to_sampler_0_i;
assign to_sampler_0_i = '{mode: Sha512,
  destination: mlkem_rho_sigma_reg_id
};

st_to_keccakType to_keccak_2_i;
assign to_keccak_2_i = '{data: getChunk(({ 20480'd0, sigma_reg} ), ({ 14'd0, sipo_chunk_idx[1:0]} )),
  strobe: 8'hFF
};

st_to_keccakType to_keccak_3_i;
assign to_keccak_3_i = '{data: ({ 60'd0, N} ),
  strobe: 8'h1
};

st_ToSamplerType to_sampler_1_i;
assign to_sampler_1_i = '{mode: Cbd,
  destination: ((({ 60'd0, N} ) < 64'd4) ? s_addrs[N] : e_addrs[{ (({ 60'd0, N} ) - 64'd4) }[1:0]])
};

st_NttType to_ntt_0_i;
assign to_ntt_0_i = '{mode: Ntt,
  operand1: ((({ 60'd0, mlkem_keygen_ntt_idx} ) < 64'd4) ? s_addrs[mlkem_keygen_ntt_idx] : e_addrs[{ (({ 60'd0, mlkem_keygen_ntt_idx} ) - 64'd4) }[1:0]]),
  operand2: 15'd0,
  destination: ((({ 60'd0, mlkem_keygen_ntt_idx} ) < 64'd4) ? s_addrs[mlkem_keygen_ntt_idx] : e_addrs[{ (({ 60'd0, mlkem_keygen_ntt_idx} ) - 64'd4) }[1:0]]),
  masking_en: 0,
  shuffle_en: 1
};

st_to_keccakType to_keccak_4_i;
assign to_keccak_4_i = '{data: getChunk(({ 20480'd0, rho_reg} ), ({ 14'd0, sipo_chunk_idx[1:0]} )),
  strobe: 8'hFF
};

st_to_keccakType to_keccak_5_i;
assign to_keccak_5_i = '{data: ((mlkem_keygen_pw_idx == 3'd0) ? 64'd0 : ({ ({ 53'd0, mlkem_keygen_pw_idx} ), 8'd0} )),
  strobe: 8'h3
};

st_ToSamplerType to_sampler_2_i;
assign to_sampler_2_i = '{mode: RejSampler,
  destination: as_addr
};

st_NttType to_ntt_1_i;
assign to_ntt_1_i = '{mode: PwmSampler,
  operand1: mlkem_rho_id,
  operand2: s_addrs[64'd0],
  destination: as_addr,
  masking_en: 0,
  shuffle_en: 0
};

st_to_keccakType to_keccak_6_i;
assign to_keccak_6_i = '{data: (({ ({ 53'd0, mlkem_keygen_pw_idx} ), 8'd0} ) | (64'd1 + ({ 61'd0, mlkem_keygen_pwa_idx} ))),
  strobe: 8'h3
};

st_NttType to_ntt_2_i;
assign to_ntt_2_i = '{mode: PwmAccuSampler,
  operand1: mlkem_rho_id,
  operand2: s_addrs[2'((mlkem_keygen_pwa_idx + 64'd1))],
  destination: as_addr,
  masking_en: 0,
  shuffle_en: 0
};

st_NttType to_ntt_3_i;
assign to_ntt_3_i = '{mode: Pwa,
  operand1: as_addr,
  operand2: e_addrs[mlkem_keygen_pw_idx],
  destination: t_addrs[mlkem_keygen_pw_idx],
  masking_en: 0,
  shuffle_en: 1
};

st_toCompressType to_compress_0_i;
assign to_compress_0_i = '{mode: 2'd3,
  poly: 3'd4,
  compare_mode_o: 0,
  src0: t_addrs[64'd0],
  src1: 15'd0,
  dest: mlkem_ek_addr
};

st_toCompressType to_compress_1_i;
assign to_compress_1_i = '{mode: 2'd3,
  poly: 3'd4,
  compare_mode_o: 0,
  src0: s_addrs[64'd0],
  src1: 15'd0,
  dest: mlkem_dk_addr
};

st_to_keccakType to_keccak_7_i;
assign to_keccak_7_i = '{data: sk_ram_data,
  strobe: 8'hFF
};

st_to_keccakType to_keccak_8_i;
assign to_keccak_8_i = '{data: getChunk(({ 20480'd0, rho_reg} ), ({ 14'd0, sipo_chunk_idx[1:0]} )),
  strobe: ((sipo_chunk_idx == 16'd196) ? 'h0 : 'hFF)
};

st_ToSamplerType to_sampler_3_i;
assign to_sampler_3_i = '{mode: Sha256,
  destination: mlkem_tr_reg_id
};

st_toDeCompressType to_decompress_1_i;
assign to_decompress_1_i = '{mode: 2'd3,
  poly: 3'd4,
  src0: mlkem_src_ek_mem,
  src1: 15'd0,
  dest: t_addrs[64'd0]
};

st_toDeCompressType to_decompress_2_i;
assign to_decompress_2_i = '{mode: 2'd3,
  poly: 3'd4,
  src0: mlkem_src_dk_mem,
  src1: 15'd0,
  dest: s_addrs[64'd0]
};

st_toDeCompressType to_decompress_3_i;
assign to_decompress_3_i = '{mode: 2'd2,
  poly: 3'd4,
  src0: mlkem_src_c1_mem,
  src1: 15'd0,
  dest: u_addrs[64'd0]
};

st_toDeCompressType to_decompress_4_i;
assign to_decompress_4_i = '{mode: 2'd1,
  poly: 3'd1,
  src0: mlkem_src_c2_mem,
  src1: 15'd0,
  dest: v_addr
};

st_NttType to_ntt_4_i;
assign to_ntt_4_i = '{mode: Ntt,
  operand1: u_addrs[mlkem_decap_ntt_idx],
  operand2: 15'd0,
  destination: up_addrs[mlkem_decap_ntt_idx],
  masking_en: 0,
  shuffle_en: 1
};

st_NttType to_ntt_5_i;
assign to_ntt_5_i = '{mode: Pwm,
  operand1: s_addrs[64'd0],
  operand2: up_addrs[64'd0],
  destination: su_masked_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_6_i;
assign to_ntt_6_i = '{mode: PwmAccum,
  operand1: s_addrs[2'((mlkem_decap_pwma_idx + 64'd1))],
  operand2: up_addrs[2'((mlkem_decap_pwma_idx + 64'd1))],
  destination: su_masked_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_7_i;
assign to_ntt_7_i = '{mode: Intt,
  operand1: su_masked_addr,
  operand2: 15'd0,
  destination: su_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_8_i;
assign to_ntt_8_i = '{mode: Pws,
  operand1: su_addr,
  operand2: v_addr,
  destination: v_addr,
  masking_en: 0,
  shuffle_en: 1
};

st_toCompressType to_compress_2_i;
assign to_compress_2_i = '{mode: 2'd0,
  poly: 3'd1,
  compare_mode_o: 0,
  src0: v_addr,
  src1: 15'd0,
  dest: mlkem_msg_mem_addr
};

st_toCompressType to_compress_3_i;
assign to_compress_3_i = '{mode: 2'd3,
  poly: 3'd4,
  compare_mode_o: !mlkem_decaps_end_process,
  src0: t_addrs[64'd0],
  src1: 15'd0,
  dest: mlkem_ek_addr
};

st_to_keccakType to_keccak_9_i;
assign to_keccak_9_i = '{data: sk_ram_data,
  strobe: (($past(sipo_chunk_idx) == 16'd4) ? 'h0 : 'hFF)
};

st_to_keccakType to_keccak_10_i;
assign to_keccak_10_i = '{data: getChunk(({ 20480'd0, tr_reg} ), ({ 14'd0, sipo_chunk_idx[1:0]} )),
  strobe: 8'hFF
};

st_to_keccakType to_keccak_11_i;
assign to_keccak_11_i = '{data: getChunk(({ 20480'd0, tr_reg} ), ({ 14'd0, sipo_chunk_idx[1:0]} )),
  strobe: ((sipo_chunk_idx == 16'd4) ? 'h0 : 'hFF)
};

st_ToSamplerType to_sampler_4_i;
assign to_sampler_4_i = '{mode: Sha512,
  destination: mlkem_k_r_reg_id
};

st_to_keccakType to_keccak_12_i;
assign to_keccak_12_i = '{data: ({ 60'd0, cbd_idx} ),
  strobe: 8'h1
};

st_ToSamplerType to_sampler_5_i;
assign to_sampler_5_i = '{mode: Cbd,
  destination: ((({ 60'd0, cbd_idx} ) < 64'd4) ? y_addrs[cbd_idx] : ((cbd_idx == 4'd8) ? e2_addr : e_addrs[{ (({ 60'd0, cbd_idx} ) - 64'd4) }[1:0]]))
};

st_NttType to_ntt_9_i;
assign to_ntt_9_i = '{mode: Ntt,
  operand1: y_addrs[mlkem_encap_ntt_y_idx],
  operand2: 15'd0,
  destination: y_addrs[mlkem_encap_ntt_y_idx],
  masking_en: 0,
  shuffle_en: 1
};

st_to_keccakType to_keccak_13_i;
assign to_keccak_13_i = '{data: ({ 61'd0, mlkem_encap_pw_idx} ),
  strobe: 8'h3
};

st_ToSamplerType to_sampler_6_i;
assign to_sampler_6_i = '{mode: RejSampler,
  destination: ay_addr
};

st_NttType to_ntt_10_i;
assign to_ntt_10_i = '{mode: PwmSampler,
  operand1: mlkem_rho_id,
  operand2: y_addrs[64'd0],
  destination: ay_addr,
  masking_en: 1,
  shuffle_en: 0
};

st_to_keccakType to_keccak_14_i;
assign to_keccak_14_i = '{data: ({ ({ 56'((56'd1 + ({ 53'd0, mlkem_encap_pwa_idx} ))), 5'd0} ), mlkem_encap_pw_idx} ),
  strobe: 8'h3
};

st_NttType to_ntt_11_i;
assign to_ntt_11_i = '{mode: PwmAccuSampler,
  operand1: mlkem_rho_id,
  operand2: y_addrs[(mlkem_encap_pwa_idx + 64'd1)],
  destination: ay_addr,
  masking_en: 1,
  shuffle_en: 0
};

st_NttType to_ntt_12_i;
assign to_ntt_12_i = '{mode: Intt,
  operand1: ay_addr,
  operand2: 15'd0,
  destination: ay_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_13_i;
assign to_ntt_13_i = '{mode: Pwa,
  operand1: ay_addr,
  operand2: e_addrs[mlkem_encap_pw_idx],
  destination: u_addrs[mlkem_encap_pw_idx],
  masking_en: 0,
  shuffle_en: 1
};

st_NttType to_ntt_14_i;
assign to_ntt_14_i = '{mode: Pwm,
  operand1: t_addrs[64'd0],
  operand2: y_addrs[64'd0],
  destination: ty_masked_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_15_i;
assign to_ntt_15_i = '{mode: PwmAccum,
  operand1: t_addrs[2'((mlkem_encap_pwma_ty_idx + 64'd1))],
  operand2: y_addrs[2'((mlkem_encap_pwma_ty_idx + 64'd1))],
  destination: ty_masked_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_NttType to_ntt_16_i;
assign to_ntt_16_i = '{mode: Intt,
  operand1: ty_masked_addr,
  operand2: 15'd0,
  destination: v_addr,
  masking_en: 1,
  shuffle_en: 1
};

st_toDeCompressType to_decompress_5_i;
assign to_decompress_5_i = '{mode: 2'd0,
  poly: 3'd1,
  src0: mlkem_src_msg_mem,
  src1: 15'd0,
  dest: mu_addr
};

st_NttType to_ntt_17_i;
assign to_ntt_17_i = '{mode: Pwa,
  operand1: mu_addr,
  operand2: e2_addr,
  destination: e2_addr,
  masking_en: 0,
  shuffle_en: 1
};

st_NttType to_ntt_18_i;
assign to_ntt_18_i = '{mode: Pwa,
  operand1: v_addr,
  operand2: e2_addr,
  destination: v_addr,
  masking_en: 0,
  shuffle_en: 1
};

st_toCompressType to_compress_4_i;
assign to_compress_4_i = '{mode: 2'd2,
  poly: 3'd4,
  compare_mode_o: ((from_api.instr == MlkemkeygenDecap) || (from_api.instr == MlkemDecap)),
  src0: u_addrs[64'd0],
  src1: 15'd0,
  dest: mlkem_c1_addr
};

st_toCompressType to_compress_5_i;
assign to_compress_5_i = '{mode: 2'd1,
  poly: 3'd1,
  compare_mode_o: ((from_api.instr == MlkemkeygenDecap) || (from_api.instr == MlkemDecap)),
  src0: v_addr,
  src1: 15'd0,
  dest: mlkem_c2_addr
};

st_to_keccakType to_keccak_15_i;
assign to_keccak_15_i = '{data: func_concat_seed(from_api.seed_z, ({ 1'd0, sipo_chunk_idx[1:0]} )),
  strobe: 8'hFF
};

st_to_keccakType to_keccak_16_i;
assign to_keccak_16_i = '{data: func_concat_seed(from_api.seed_z, ({ 1'd0, sipo_chunk_idx[1:0]} )),
  strobe: ((sipo_chunk_idx == 16'd4) ? 'h0 : 'hFF)
};

st_to_keccakType to_keccak_17_i;
assign to_keccak_17_i = '{data: sk_ram_data,
  strobe: (($past(sipo_chunk_idx) == 16'd196) ? 'h0 : 'hFF)
};

st_ToSamplerType to_sampler_7_i;
assign to_sampler_7_i = '{mode: Shake256,
  destination: mlkem_k_reg_id
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property ctrl_reset_p;
  $past(!rst_n) |->
  `ifdef NO_ABSTRACTION
  idle && // Since In IVA mode, post reset counter could start from any state not necessarily abr_prog_cntr at reset
  N == 4'd0 &&
  cbd_idx == 4'd0 &&
  mlkem_decap_ntt_idx == 3'd0 &&
  mlkem_decap_pwma_idx == 2'd0 &&
  mlkem_encap_ntt_y_idx == 3'd0 &&
  mlkem_encap_pw_idx == 3'd0 &&
  mlkem_encap_pwa_idx == 3'd0 &&
  mlkem_encap_pwma_ty_idx == 3'd0 &&
  mlkem_keygen_ntt_idx == 4'd0 &&
  mlkem_keygen_pw_idx == 3'd0 &&
  mlkem_keygen_pwa_idx == 3'd0 &&
  `endif
  msg_start_o == 0 &&
  sha3_start_o == 0 &&
  to_compress_vld == 0 &&
  to_decompress_vld == 0 &&
  to_keccak_vld == 0 &&
  to_ntt_vld == 0 &&
  to_sampler_vld == 0;
endproperty
ctrl_reset_a: assert property (ctrl_reset_p);


property ctrl_idle_to_idle_p;
  idle &&
  (api_in.instr == NoOp)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_idle_to_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_idle_to_idle_p);


property ctrl_idle_to_mlkem_decap_SHA256_START_p;
  idle &&
  (api_in.instr == MlkemDecap)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_decap_SHA256_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_idle_to_mlkem_decap_SHA256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_idle_to_mlkem_decap_SHA256_START_p);


property ctrl_idle_to_mlkem_encap_decompress_t0_start_p;
  idle &&
  (api_in.instr != NoOp) &&
  (api_in.instr != MlkemKeygen) &&
  (api_in.instr != MlkemkeygenDecap) &&
  (api_in.instr != MlkemDecap)
|->
  ##1 ((to_decompress_vld == 0)) and
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_decompress_t0_start &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  to_decompress == $past(to_decompress_0_i, 2) &&
  to_decompress_vld == 1;
endproperty
ctrl_idle_to_mlkem_encap_decompress_t0_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_idle_to_mlkem_encap_decompress_t0_start_p);


property ctrl_idle_to_mlkem_keygen_rnd_seed_SHA3_START_p;
  idle &&
  ((api_in.instr == MlkemKeygen) || (api_in.instr == MlkemkeygenDecap))
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_rnd_seed_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_idle_to_mlkem_keygen_rnd_seed_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_idle_to_mlkem_keygen_rnd_seed_SHA3_START_p);


property ctrl_mlkem_Keygen_pwa_idle_to_mlkem_Keygen_pwa_start_p;
  mlkem_Keygen_pwa_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_Keygen_pwa_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_3_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_Keygen_pwa_idle_to_mlkem_Keygen_pwa_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_idle_to_mlkem_Keygen_pwa_start_p);


property ctrl_mlkem_Keygen_pwa_start_to_mlkem_Keygen_pwa_p;
  mlkem_Keygen_pwa_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_Keygen_pwa &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_Keygen_pwa_start_to_mlkem_Keygen_pwa_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_start_to_mlkem_Keygen_pwa_p);


property ctrl_mlkem_Keygen_pwa_to_mlkem_Keygen_pwa_p;
  mlkem_Keygen_pwa &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_Keygen_pwa &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_Keygen_pwa_to_mlkem_Keygen_pwa_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_to_mlkem_Keygen_pwa_p);


property ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_compress_ek_idle_p;
  mlkem_Keygen_pwa &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_keygen_pw_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_ek_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  mlkem_keygen_pw_idx == 3'd0 &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_compress_ek_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_compress_ek_idle_p);


property ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_pwm_write_rho_SHA3_START_p;
  mlkem_Keygen_pwa &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_keygen_pw_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_pwm_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == (3'd1 + $past(mlkem_keygen_pw_idx, 2)) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_pwm_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_to_mlkem_keygen_pwm_write_rho_SHA3_START_p);


property ctrl_mlkem_decap_SHA256_START_to_mlkem_decap_write_ek_START_p;
  mlkem_decap_SHA256_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek_START &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_decap_SHA256_START_to_mlkem_decap_write_ek_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_SHA256_START_to_mlkem_decap_write_ek_START_p);


property ctrl_mlkem_decap_compress_msg_idle_to_mlkem_decap_compress_msg_start_p;
  mlkem_decap_compress_msg_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_compress_msg_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_compress == $past(to_compress_2_i, 1) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_decap_compress_msg_idle_to_mlkem_decap_compress_msg_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_idle_to_mlkem_decap_compress_msg_start_p);


property ctrl_mlkem_decap_compress_msg_start_to_mlkem_decap_compress_msg_p;
  mlkem_decap_compress_msg_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_compress_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_compress_msg_start_to_mlkem_decap_compress_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_start_to_mlkem_decap_compress_msg_p);


property ctrl_mlkem_decap_compress_msg_to_mlkem_decap_compress_msg_p;
  mlkem_decap_compress_msg &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_compress_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_compress_msg_to_mlkem_decap_compress_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_to_mlkem_decap_compress_msg_p);


property ctrl_mlkem_decap_compress_msg_to_mlkem_encap_decompress_t0_start_p;
  mlkem_decap_compress_msg &&
  compress_done_in
|->
  ##1 ((to_decompress_vld == 0)) and
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_decompress_t0_start &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  to_decompress == $past(to_decompress_1_i, 2) &&
  to_decompress_vld == 1;
endproperty
ctrl_mlkem_decap_compress_msg_to_mlkem_encap_decompress_t0_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_to_mlkem_encap_decompress_t0_start_p);


property ctrl_mlkem_decap_decompress_s0_idle_to_mlkem_decap_decompress_s0_start_p;
  mlkem_decap_decompress_s0_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_s0_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_decompress == $past(to_decompress_2_i, 1) &&
  to_decompress_vld == 1;
endproperty
ctrl_mlkem_decap_decompress_s0_idle_to_mlkem_decap_decompress_s0_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_idle_to_mlkem_decap_decompress_s0_start_p);


property ctrl_mlkem_decap_decompress_s0_start_to_mlkem_decap_decompress_s0_p;
  mlkem_decap_decompress_s0_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_s0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_s0_start_to_mlkem_decap_decompress_s0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_start_to_mlkem_decap_decompress_s0_p);


property ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_s0_p;
  mlkem_decap_decompress_s0 &&
  !decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_s0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_s0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_s0_p);


property ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_u0_idle_p;
  mlkem_decap_decompress_s0 &&
  decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_u0_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_u0_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_to_mlkem_decap_decompress_u0_idle_p);


property ctrl_mlkem_decap_decompress_u0_idle_to_mlkem_decap_decompress_u0_start_p;
  mlkem_decap_decompress_u0_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_u0_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_decompress == $past(to_decompress_3_i, 1) &&
  to_decompress_vld == 1;
endproperty
ctrl_mlkem_decap_decompress_u0_idle_to_mlkem_decap_decompress_u0_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_idle_to_mlkem_decap_decompress_u0_start_p);


property ctrl_mlkem_decap_decompress_u0_start_to_mlkem_decap_decompress_u0_p;
  mlkem_decap_decompress_u0_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_u0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_u0_start_to_mlkem_decap_decompress_u0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_start_to_mlkem_decap_decompress_u0_p);


property ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_u0_p;
  mlkem_decap_decompress_u0 &&
  !decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_u0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_u0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_u0_p);


property ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_v_idle_p;
  mlkem_decap_decompress_u0 &&
  decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_v_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_v_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_to_mlkem_decap_decompress_v_idle_p);


property ctrl_mlkem_decap_decompress_v_idle_to_mlkem_decap_decompress_v_start_p;
  mlkem_decap_decompress_v_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_v_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_decompress == $past(to_decompress_4_i, 1) &&
  to_decompress_vld == 1;
endproperty
ctrl_mlkem_decap_decompress_v_idle_to_mlkem_decap_decompress_v_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_idle_to_mlkem_decap_decompress_v_start_p);


property ctrl_mlkem_decap_decompress_v_start_to_mlkem_decap_decompress_v_p;
  mlkem_decap_decompress_v_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_v_start_to_mlkem_decap_decompress_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_start_to_mlkem_decap_decompress_v_p);


property ctrl_mlkem_decap_decompress_v_to_mlkem_decap_decompress_v_p;
  mlkem_decap_decompress_v &&
  !decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_v_to_mlkem_decap_decompress_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_to_mlkem_decap_decompress_v_p);


property ctrl_mlkem_decap_decompress_v_to_mlkem_decap_ntt_idle_p;
  mlkem_decap_decompress_v &&
  decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ntt_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  mlkem_decap_ntt_idx == 3'd0 &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_decompress_v_to_mlkem_decap_ntt_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_to_mlkem_decap_ntt_idle_p);


property ctrl_mlkem_decap_ek_sampling_start_to_mlkem_decap_ek_sampling_p;
  mlkem_decap_ek_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ek_sampling_start_to_mlkem_decap_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ek_sampling_start_to_mlkem_decap_ek_sampling_p);


property ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_decompress_s0_idle_p;
  mlkem_decap_ek_sampling &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_decompress_s0_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_decompress_s0_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_decompress_s0_idle_p);


property ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_ek_sampling_p;
  mlkem_decap_ek_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ek_sampling_to_mlkem_decap_ek_sampling_p);


property ctrl_mlkem_decap_intt_su_idle_to_mlkem_decap_intt_su_start_p;
  mlkem_decap_intt_su_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_intt_su_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_7_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_decap_intt_su_idle_to_mlkem_decap_intt_su_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_idle_to_mlkem_decap_intt_su_start_p);


property ctrl_mlkem_decap_intt_su_start_to_mlkem_decap_intt_su_p;
  mlkem_decap_intt_su_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_intt_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_intt_su_start_to_mlkem_decap_intt_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_start_to_mlkem_decap_intt_su_p);


property ctrl_mlkem_decap_intt_su_to_mlkem_decap_intt_su_p;
  mlkem_decap_intt_su &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_intt_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_intt_su_to_mlkem_decap_intt_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_to_mlkem_decap_intt_su_p);


property ctrl_mlkem_decap_intt_su_to_mlkem_decap_pws_su_idle_p;
  mlkem_decap_intt_su &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pws_su_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_intt_su_to_mlkem_decap_pws_su_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_to_mlkem_decap_pws_su_idle_p);


property ctrl_mlkem_decap_ntt_idle_to_mlkem_decap_ntt_start_p;
  mlkem_decap_ntt_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ntt_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_4_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_decap_ntt_idle_to_mlkem_decap_ntt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_idle_to_mlkem_decap_ntt_start_p);


property ctrl_mlkem_decap_ntt_start_to_mlkem_decap_ntt_p;
  mlkem_decap_ntt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ntt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ntt_start_to_mlkem_decap_ntt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_start_to_mlkem_decap_ntt_p);


property ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_p;
  mlkem_decap_ntt &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ntt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_p);


property ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_idle_p;
  mlkem_decap_ntt &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_decap_ntt_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_ntt_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  mlkem_decap_ntt_idx == (3'd1 + $past(mlkem_decap_ntt_idx, 1)) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_to_mlkem_decap_ntt_idle_p);


property ctrl_mlkem_decap_ntt_to_mlkem_decap_pwm_su_idle_p;
  mlkem_decap_ntt &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_decap_ntt_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwm_su_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  mlkem_decap_ntt_idx == 3'd0 &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_ntt_to_mlkem_decap_pwm_su_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_to_mlkem_decap_pwm_su_idle_p);


property ctrl_mlkem_decap_pwm_su_idle_to_mlkem_decap_pwm_su_start_p;
  mlkem_decap_pwm_su_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwm_su_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_5_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_decap_pwm_su_idle_to_mlkem_decap_pwm_su_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_idle_to_mlkem_decap_pwm_su_start_p);


property ctrl_mlkem_decap_pwm_su_start_to_mlkem_decap_pwm_su_p;
  mlkem_decap_pwm_su_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwm_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwm_su_start_to_mlkem_decap_pwm_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_start_to_mlkem_decap_pwm_su_p);


property ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwm_su_p;
  mlkem_decap_pwm_su &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwm_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwm_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwm_su_p);


property ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwma_su_idle_p;
  mlkem_decap_pwm_su &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwma_su_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  mlkem_decap_pwma_idx == 2'd0 &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwma_su_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_to_mlkem_decap_pwma_su_idle_p);


property ctrl_mlkem_decap_pwma_su_idle_to_mlkem_decap_pwma_su_start_p;
  mlkem_decap_pwma_su_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwma_su_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_6_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_decap_pwma_su_idle_to_mlkem_decap_pwma_su_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_idle_to_mlkem_decap_pwma_su_start_p);


property ctrl_mlkem_decap_pwma_su_start_to_mlkem_decap_pwma_su_p;
  mlkem_decap_pwma_su_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwma_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwma_su_start_to_mlkem_decap_pwma_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_start_to_mlkem_decap_pwma_su_p);


property ctrl_mlkem_decap_pwma_su_to_mlkem_decap_intt_su_idle_p;
  mlkem_decap_pwma_su &&
  ntt_done_in &&
  (({ 62'd0, 2'((2'd1 + mlkem_decap_pwma_idx))} ) >= 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_intt_su_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  mlkem_decap_pwma_idx == 2'd0 &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwma_su_to_mlkem_decap_intt_su_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_to_mlkem_decap_intt_su_idle_p);


property ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_p;
  mlkem_decap_pwma_su &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwma_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_p);


property ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_idle_p;
  mlkem_decap_pwma_su &&
  ntt_done_in &&
  (({ 62'd0, 2'((2'd1 + mlkem_decap_pwma_idx))} ) < 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pwma_su_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  mlkem_decap_pwma_idx == (2'd1 + $past(mlkem_decap_pwma_idx, 1)) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_to_mlkem_decap_pwma_su_idle_p);


property ctrl_mlkem_decap_pws_su_idle_to_mlkem_decap_pws_su_start_p;
  mlkem_decap_pws_su_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pws_su_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_8_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_decap_pws_su_idle_to_mlkem_decap_pws_su_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_idle_to_mlkem_decap_pws_su_start_p);


property ctrl_mlkem_decap_pws_su_start_to_mlkem_decap_pws_su_p;
  mlkem_decap_pws_su_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pws_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pws_su_start_to_mlkem_decap_pws_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_start_to_mlkem_decap_pws_su_p);


property ctrl_mlkem_decap_pws_su_to_mlkem_decap_compress_msg_idle_p;
  mlkem_decap_pws_su &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_compress_msg_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pws_su_to_mlkem_decap_compress_msg_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_to_mlkem_decap_compress_msg_idle_p);


property ctrl_mlkem_decap_pws_su_to_mlkem_decap_pws_su_p;
  mlkem_decap_pws_su &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_pws_su &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_pws_su_to_mlkem_decap_pws_su_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_to_mlkem_decap_pws_su_p);


property ctrl_mlkem_decap_write_ek_START_to_mlkem_decap_write_ek_init_p;
  mlkem_decap_write_ek_START
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_decap_write_ek_START_to_mlkem_decap_write_ek_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_START_to_mlkem_decap_write_ek_init_p);


property ctrl_mlkem_decap_write_ek_init_to_mlkem_decap_write_ek_p;
  mlkem_decap_write_ek_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_decap_write_ek_init_to_mlkem_decap_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_init_to_mlkem_decap_write_ek_p);


property ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_ek_sampling_start_p;
  mlkem_decap_write_ek_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_decap_ek_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_3_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_ek_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_ek_sampling_start_p);


property ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_write_ek_msg_done_p;
  mlkem_decap_write_ek_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_msg_done_to_mlkem_decap_write_ek_msg_done_p);


property ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_p;
  mlkem_decap_write_ek &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_p);


property ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_1_p;
  mlkem_decap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_1_p);


property ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_2_p;
  mlkem_decap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_2_p);


property ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_msg_done_p;
  mlkem_decap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_decap_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_to_mlkem_decap_write_ek_msg_done_p);


property ctrl_mlkem_encap_SHA256_START_to_mlkem_encap_write_ek_START_p;
  mlkem_encap_SHA256_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek_START &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_SHA256_START_to_mlkem_encap_write_ek_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_SHA256_START_to_mlkem_encap_write_ek_START_p);


property ctrl_mlkem_encap_compress_c1_idle_to_mlkem_encap_compress_c1_start_p;
  mlkem_encap_compress_c1_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c1_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_compress == $past(to_compress_4_i, 1) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_encap_compress_c1_idle_to_mlkem_encap_compress_c1_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_idle_to_mlkem_encap_compress_c1_start_p);


property ctrl_mlkem_encap_compress_c1_start_to_mlkem_encap_compress_c1_p;
  mlkem_encap_compress_c1_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c1 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_c1_start_to_mlkem_encap_compress_c1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_start_to_mlkem_encap_compress_c1_p);


property ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c1_p;
  mlkem_encap_compress_c1 &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c1 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c1_p);


property ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c2_idle_p;
  mlkem_encap_compress_c1 &&
  compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c2_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c2_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_to_mlkem_encap_compress_c2_idle_p);


property ctrl_mlkem_encap_compress_c2_idle_to_mlkem_encap_compress_c2_start_p;
  mlkem_encap_compress_c2_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c2_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_compress == $past(to_compress_5_i, 1) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_encap_compress_c2_idle_to_mlkem_encap_compress_c2_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_idle_to_mlkem_encap_compress_c2_start_p);


property ctrl_mlkem_encap_compress_c2_start_to_mlkem_encap_compress_c2_p;
  mlkem_encap_compress_c2_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c2 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_c2_start_to_mlkem_encap_compress_c2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_start_to_mlkem_encap_compress_c2_p);


property ctrl_mlkem_encap_compress_c2_to_mlkem_encap_compress_c2_p;
  mlkem_encap_compress_c2 &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c2 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_c2_to_mlkem_encap_compress_c2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_to_mlkem_encap_compress_c2_p);


property ctrl_mlkem_encap_compress_c2_to_mlkem_encap_end_p;
  mlkem_encap_compress_c2 &&
  compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_end &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2);
endproperty
ctrl_mlkem_encap_compress_c2_to_mlkem_encap_end_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_to_mlkem_encap_end_p);


property ctrl_mlkem_encap_compress_first_start_to_mlkem_encap_compress_first_p;
  mlkem_encap_compress_first_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_first &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_first_start_to_mlkem_encap_compress_first_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_first_start_to_mlkem_encap_compress_first_p);


property ctrl_mlkem_encap_compress_first_to_mlkem_encap_SHA256_START_p;
  mlkem_encap_compress_first &&
  compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_SHA256_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_compress_first_to_mlkem_encap_SHA256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_first_to_mlkem_encap_SHA256_START_p);


property ctrl_mlkem_encap_compress_first_to_mlkem_encap_compress_first_p;
  mlkem_encap_compress_first &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_first &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_compress_first_to_mlkem_encap_compress_first_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_first_to_mlkem_encap_compress_first_p);


property ctrl_mlkem_encap_ct_shake256_done_to_idle_p;
  mlkem_encap_ct_shake256_done &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  idle &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2);
endproperty
ctrl_mlkem_encap_ct_shake256_done_to_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ct_shake256_done_to_idle_p);


property ctrl_mlkem_encap_ct_shake256_done_to_mlkem_encap_ct_shake256_done_p;
  mlkem_encap_ct_shake256_done &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ct_shake256_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ct_shake256_done_to_mlkem_encap_ct_shake256_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ct_shake256_done_to_mlkem_encap_ct_shake256_done_p);


property ctrl_mlkem_encap_ct_shake256_to_mlkem_encap_ct_shake256_done_p;
  mlkem_encap_ct_shake256
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ct_shake256_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ct_shake256_to_mlkem_encap_ct_shake256_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ct_shake256_to_mlkem_encap_ct_shake256_done_p);


property ctrl_mlkem_encap_decompress_mu_idle_to_mlkem_encap_decompress_mu_start_p;
  mlkem_encap_decompress_mu_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_mu_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_decompress == $past(to_decompress_5_i, 1) &&
  to_decompress_vld == 1;
endproperty
ctrl_mlkem_encap_decompress_mu_idle_to_mlkem_encap_decompress_mu_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_idle_to_mlkem_encap_decompress_mu_start_p);


property ctrl_mlkem_encap_decompress_mu_start_to_mlkem_encap_decompress_mu_p;
  mlkem_encap_decompress_mu_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_mu &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_decompress_mu_start_to_mlkem_encap_decompress_mu_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_start_to_mlkem_encap_decompress_mu_p);


property ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_decompress_mu_p;
  mlkem_encap_decompress_mu &&
  !decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_mu &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_decompress_mu_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_decompress_mu_p);


property ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_pwa_e2_idle_p;
  mlkem_encap_decompress_mu &&
  decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_e2_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_pwa_e2_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_to_mlkem_encap_pwa_e2_idle_p);


property ctrl_mlkem_encap_decompress_t0_start_to_mlkem_encap_decompress_t0_p;
  mlkem_encap_decompress_t0_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_t0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_decompress_t0_start_to_mlkem_encap_decompress_t0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_t0_start_to_mlkem_encap_decompress_t0_p);


property ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_compress_first_start_p;
  mlkem_encap_decompress_t0 &&
  decompress_done_in
|->
  ##1 ((to_compress_vld == 0)) and
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_compress_first_start &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  to_compress == $past(to_compress_3_i, 2) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_compress_first_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_compress_first_start_p);


property ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_decompress_t0_p;
  mlkem_encap_decompress_t0 &&
  !decompress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_t0 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_decompress_t0_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_t0_to_mlkem_encap_decompress_t0_p);


property ctrl_mlkem_encap_ek_sampling_start_to_mlkem_encap_ek_sampling_p;
  mlkem_encap_ek_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ek_sampling_start_to_mlkem_encap_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_start_to_mlkem_encap_ek_sampling_p);


property ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_p;
  mlkem_encap_ek_sampling &&
  from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_p);


property ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_1_p;
  mlkem_encap_ek_sampling &&
  !from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ek_sampling_1_p);

//Note: This assertion is disabled since a sampler_done i.e the sampler_busy deassertion cannot happen 
// at the same time as the keccak sending in a valid i.e from_keccak_piso_vld_in being high.
// This is because valids from the keccak core to sampler top is received only during sampler_busy high period.
// Hence the first property below is disabled. The second property covers the case when from_keccak_piso_vld_in is low
// when sampler_done_in goes high.
property ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_p;
  mlkem_encap_ek_sampling &&
  from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_ld_SHA512_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
//ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_p);


property ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_1_p;
  mlkem_encap_ek_sampling &&
  !from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_ld_SHA512_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_to_mlkem_encap_ld_SHA512_START_1_p);


property ctrl_mlkem_encap_end_to_idle_p;
  mlkem_encap_end &&
  !mlkem_decaps_end_process
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_end_to_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_end_to_idle_p);


property ctrl_mlkem_encap_end_to_mlkem_encap_ld_SHAKE256_START_p;
  mlkem_encap_end &&
  mlkem_decaps_end_process
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_ld_SHAKE256_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_end_to_mlkem_encap_ld_SHAKE256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_end_to_mlkem_encap_ld_SHAKE256_START_p);


property ctrl_mlkem_encap_intt_idle_to_mlkem_encap_intt_start_p;
  mlkem_encap_intt_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_12_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_intt_idle_to_mlkem_encap_intt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_idle_to_mlkem_encap_intt_start_p);


property ctrl_mlkem_encap_intt_start_to_mlkem_encap_intt_p;
  mlkem_encap_intt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_start_to_mlkem_encap_intt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_start_to_mlkem_encap_intt_p);


property ctrl_mlkem_encap_intt_to_mlkem_encap_intt_p;
  mlkem_encap_intt &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_to_mlkem_encap_intt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_to_mlkem_encap_intt_p);


property ctrl_mlkem_encap_intt_to_mlkem_encap_pwa_idle_p;
  mlkem_encap_intt &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_to_mlkem_encap_pwa_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_to_mlkem_encap_pwa_idle_p);


property ctrl_mlkem_encap_intt_v_idle_to_mlkem_encap_intt_v_start_p;
  mlkem_encap_intt_v_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_v_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_16_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_intt_v_idle_to_mlkem_encap_intt_v_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_idle_to_mlkem_encap_intt_v_start_p);


property ctrl_mlkem_encap_intt_v_start_to_mlkem_encap_intt_v_p;
  mlkem_encap_intt_v_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_v_start_to_mlkem_encap_intt_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_start_to_mlkem_encap_intt_v_p);


property ctrl_mlkem_encap_intt_v_to_mlkem_encap_decompress_mu_idle_p;
  mlkem_encap_intt_v &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_mu_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_v_to_mlkem_encap_decompress_mu_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_to_mlkem_encap_decompress_mu_idle_p);


property ctrl_mlkem_encap_intt_v_to_mlkem_encap_intt_v_p;
  mlkem_encap_intt_v &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_intt_v_to_mlkem_encap_intt_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_to_mlkem_encap_intt_v_p);


property ctrl_mlkem_encap_ld_SHA512_START_to_mlkem_encap_write_msg_START_p;
  mlkem_encap_ld_SHA512_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_START &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_ld_SHA512_START_to_mlkem_encap_write_msg_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ld_SHA512_START_to_mlkem_encap_write_msg_START_p);


property ctrl_mlkem_encap_ld_SHAKE256_START_to_mlkem_encap_write_msg_256_START_p;
  mlkem_encap_ld_SHAKE256_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256_START &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_ld_SHAKE256_START_to_mlkem_encap_write_msg_256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ld_SHAKE256_START_to_mlkem_encap_write_msg_256_START_p);


property ctrl_mlkem_encap_ntt_y_idle_to_mlkem_encap_ntt_y_start_p;
  mlkem_encap_ntt_y_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ntt_y_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_9_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_ntt_y_idle_to_mlkem_encap_ntt_y_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_idle_to_mlkem_encap_ntt_y_start_p);


property ctrl_mlkem_encap_ntt_y_start_to_mlkem_encap_ntt_y_p;
  mlkem_encap_ntt_y_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ntt_y &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ntt_y_start_to_mlkem_encap_ntt_y_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_start_to_mlkem_encap_ntt_y_p);


property ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_p;
  mlkem_encap_ntt_y &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ntt_y &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_p);


property ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_idle_p;
  mlkem_encap_ntt_y &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_ntt_y_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ntt_y_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  mlkem_encap_ntt_y_idx == (3'd1 + $past(mlkem_encap_ntt_y_idx, 1)) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_to_mlkem_encap_ntt_y_idle_p);


property ctrl_mlkem_encap_ntt_y_to_mlkem_encap_pwm_write_rho_SHA3_START_p;
  mlkem_encap_ntt_y &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_ntt_y_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_pwm_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == 3'd0 &&
  mlkem_encap_pw_idx == 3'd0 &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_ntt_y_to_mlkem_encap_pwm_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_to_mlkem_encap_pwm_write_rho_SHA3_START_p);


property ctrl_mlkem_encap_pwa_e2_idle_to_mlkem_encap_pwa_e2_start_p;
  mlkem_encap_pwa_e2_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_e2_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_17_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwa_e2_idle_to_mlkem_encap_pwa_e2_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_idle_to_mlkem_encap_pwa_e2_start_p);


property ctrl_mlkem_encap_pwa_e2_start_to_mlkem_encap_pwa_e2_p;
  mlkem_encap_pwa_e2_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_e2 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_e2_start_to_mlkem_encap_pwa_e2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_start_to_mlkem_encap_pwa_e2_p);


property ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_e2_p;
  mlkem_encap_pwa_e2 &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_e2 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_e2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_e2_p);


property ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_v_idle_p;
  mlkem_encap_pwa_e2 &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_v_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_v_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_to_mlkem_encap_pwa_v_idle_p);


property ctrl_mlkem_encap_pwa_idle_to_mlkem_encap_pwa_start_p;
  mlkem_encap_pwa_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_13_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwa_idle_to_mlkem_encap_pwa_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_idle_to_mlkem_encap_pwa_start_p);


property ctrl_mlkem_encap_pwa_start_to_mlkem_encap_pwa_p;
  mlkem_encap_pwa_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_start_to_mlkem_encap_pwa_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_start_to_mlkem_encap_pwa_p);


property ctrl_mlkem_encap_pwa_to_mlkem_encap_pwa_p;
  mlkem_encap_pwa &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_to_mlkem_encap_pwa_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_to_mlkem_encap_pwa_p);


property ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_ty_idle_p;
  mlkem_encap_pwa &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pw_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_ty_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  mlkem_encap_pw_idx == 3'd0 &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_ty_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_ty_idle_p);


property ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_write_rho_SHA3_START_p;
  mlkem_encap_pwa &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pw_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_pwm_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == (3'd1 + $past(mlkem_encap_pw_idx, 2)) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_to_mlkem_encap_pwm_write_rho_SHA3_START_p);


property ctrl_mlkem_encap_pwa_v_idle_to_mlkem_encap_pwa_v_start_p;
  mlkem_encap_pwa_v_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_v_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_18_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwa_v_idle_to_mlkem_encap_pwa_v_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_idle_to_mlkem_encap_pwa_v_start_p);


property ctrl_mlkem_encap_pwa_v_start_to_mlkem_encap_pwa_v_p;
  mlkem_encap_pwa_v_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_v_start_to_mlkem_encap_pwa_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_start_to_mlkem_encap_pwa_v_p);


property ctrl_mlkem_encap_pwa_v_to_mlkem_encap_compress_c1_idle_p;
  mlkem_encap_pwa_v &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_compress_c1_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_v_to_mlkem_encap_compress_c1_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_to_mlkem_encap_compress_c1_idle_p);


property ctrl_mlkem_encap_pwa_v_to_mlkem_encap_pwa_v_p;
  mlkem_encap_pwa_v &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwa_v &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwa_v_to_mlkem_encap_pwa_v_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_to_mlkem_encap_pwa_v_p);


property ctrl_mlkem_encap_pwm_a_ntt_start_to_mlkem_encap_pwm_a_p;
  mlkem_encap_pwm_a_ntt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_ntt_start_to_mlkem_encap_pwm_a_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_ntt_start_to_mlkem_encap_pwm_a_p);


property ctrl_mlkem_encap_pwm_a_rejection_sampling_start_to_mlkem_encap_pwm_a_ntt_start_p;
  mlkem_encap_pwm_a_rejection_sampling_start
|->
  mlkem_encap_pwm_a_ntt_start &&
  N == N &&
  cbd_idx == cbd_idx &&
  mlkem_decap_ntt_idx == mlkem_decap_ntt_idx &&
  mlkem_decap_pwma_idx == mlkem_decap_pwma_idx &&
  mlkem_encap_ntt_y_idx == mlkem_encap_ntt_y_idx &&
  mlkem_encap_pw_idx == mlkem_encap_pw_idx &&
  mlkem_encap_pwa_idx == mlkem_encap_pwa_idx &&
  mlkem_encap_pwma_ty_idx == mlkem_encap_pwma_ty_idx &&
  mlkem_keygen_ntt_idx == mlkem_keygen_ntt_idx &&
  mlkem_keygen_pw_idx == mlkem_keygen_pw_idx &&
  mlkem_keygen_pwa_idx == mlkem_keygen_pwa_idx &&
  to_ntt == to_ntt_11_i &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_rejection_sampling_start_to_mlkem_encap_pwm_a_ntt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_rejection_sampling_start_to_mlkem_encap_pwm_a_ntt_start_p);


property ctrl_mlkem_encap_pwm_a_to_mlkem_encap_intt_idle_p;
  mlkem_encap_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pwa_idx))} ) >= 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  mlkem_encap_pwa_idx == 3'd0 &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_to_mlkem_encap_intt_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_to_mlkem_encap_intt_idle_p);


property ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_p;
  mlkem_encap_pwm_a &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_p);


property ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_write_rho_SHA3_START_p;
  mlkem_encap_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pwa_idx))} ) < 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_pwm_a_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == (3'd1 + $past(mlkem_encap_pwa_idx, 2)) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_to_mlkem_encap_pwm_a_write_rho_SHA3_START_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_rejection_sampling_start_p;
  mlkem_encap_pwm_a_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld)) and
  ##1
  mlkem_encap_pwm_a_rejection_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_6_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_rejection_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_rejection_sampling_start_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_write_immediate_msg_done_p;
  mlkem_encap_pwm_a_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_to_mlkem_encap_pwm_a_write_immediate_msg_done_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_p;
  mlkem_encap_pwm_a_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_msg_done_p;
  mlkem_encap_pwm_a_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_14_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_to_mlkem_encap_pwm_a_write_immediate_msg_done_p);


property ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_to_mlkem_encap_pwm_a_write_rho_start_p;
  mlkem_encap_pwm_a_write_rho_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_rho_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_to_mlkem_encap_pwm_a_write_rho_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_to_mlkem_encap_pwm_a_write_rho_start_p);


property ctrl_mlkem_encap_pwm_a_write_rho_init_to_mlkem_encap_pwm_a_write_rho_p;
  mlkem_encap_pwm_a_write_rho_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_init_to_mlkem_encap_pwm_a_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_init_to_mlkem_encap_pwm_a_write_rho_p);


property ctrl_mlkem_encap_pwm_a_write_rho_start_to_mlkem_encap_pwm_a_write_rho_init_p;
  mlkem_encap_pwm_a_write_rho_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_rho_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_start_to_mlkem_encap_pwm_a_write_rho_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_start_to_mlkem_encap_pwm_a_write_rho_init_p);


property ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_immediate_p;
  mlkem_encap_pwm_a_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_immediate_p);


property ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_p;
  mlkem_encap_pwm_a_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_p);


property ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_1_p;
  mlkem_encap_pwm_a_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_to_mlkem_encap_pwm_a_write_rho_1_p);


property ctrl_mlkem_encap_pwm_ntt_start_to_mlkem_encap_pwm_p;
  mlkem_encap_pwm_ntt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_ntt_start_to_mlkem_encap_pwm_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ntt_start_to_mlkem_encap_pwm_p);


property ctrl_mlkem_encap_pwm_rejection_sampling_start_to_mlkem_encap_pwm_ntt_start_p;
  mlkem_encap_pwm_rejection_sampling_start
|->
  mlkem_encap_pwm_ntt_start &&
  N == N &&
  cbd_idx == cbd_idx &&
  mlkem_decap_ntt_idx == mlkem_decap_ntt_idx &&
  mlkem_decap_pwma_idx == mlkem_decap_pwma_idx &&
  mlkem_encap_ntt_y_idx == mlkem_encap_ntt_y_idx &&
  mlkem_encap_pw_idx == mlkem_encap_pw_idx &&
  mlkem_encap_pwa_idx == mlkem_encap_pwa_idx &&
  mlkem_encap_pwma_ty_idx == mlkem_encap_pwma_ty_idx &&
  mlkem_keygen_ntt_idx == mlkem_keygen_ntt_idx &&
  mlkem_keygen_pw_idx == mlkem_keygen_pw_idx &&
  mlkem_keygen_pwa_idx == mlkem_keygen_pwa_idx &&
  to_ntt == to_ntt_10_i &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_rejection_sampling_start_to_mlkem_encap_pwm_ntt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_rejection_sampling_start_to_mlkem_encap_pwm_ntt_start_p);


property ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_p;
  mlkem_encap_pwm &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_p);


property ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_a_write_rho_SHA3_START_p;
  mlkem_encap_pwm &&
  ntt_done_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_pwm_a_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == 3'd0 &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_to_mlkem_encap_pwm_a_write_rho_SHA3_START_p);


property ctrl_mlkem_encap_pwm_ty_idle_to_mlkem_encap_pwm_ty_start_p;
  mlkem_encap_pwm_ty_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_ty_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_14_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_ty_idle_to_mlkem_encap_pwm_ty_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_idle_to_mlkem_encap_pwm_ty_start_p);


property ctrl_mlkem_encap_pwm_ty_start_to_mlkem_encap_pwm_ty_p;
  mlkem_encap_pwm_ty_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_ty &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_ty_start_to_mlkem_encap_pwm_ty_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_start_to_mlkem_encap_pwm_ty_p);


property ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwm_ty_p;
  mlkem_encap_pwm_ty &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_ty &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwm_ty_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwm_ty_p);


property ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwma_ty_idle_p;
  mlkem_encap_pwm_ty &&
  ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwma_ty_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  mlkem_encap_pwma_ty_idx == 3'd0 &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwma_ty_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_to_mlkem_encap_pwma_ty_idle_p);


property ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_rejection_sampling_start_p;
  mlkem_encap_pwm_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld)) and
  ##1
  mlkem_encap_pwm_rejection_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_6_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_rejection_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_rejection_sampling_start_p);


property ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_write_immediate_msg_done_p;
  mlkem_encap_pwm_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_msg_done_to_mlkem_encap_pwm_write_immediate_msg_done_p);


property ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_p;
  mlkem_encap_pwm_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_p);


property ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_msg_done_p;
  mlkem_encap_pwm_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_13_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_to_mlkem_encap_pwm_write_immediate_msg_done_p);


property ctrl_mlkem_encap_pwm_write_rho_SHA3_START_to_mlkem_encap_pwm_write_rho_start_p;
  mlkem_encap_pwm_write_rho_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_rho_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_pwm_write_rho_SHA3_START_to_mlkem_encap_pwm_write_rho_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_SHA3_START_to_mlkem_encap_pwm_write_rho_start_p);


property ctrl_mlkem_encap_pwm_write_rho_init_to_mlkem_encap_pwm_write_rho_p;
  mlkem_encap_pwm_write_rho_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_write_rho_init_to_mlkem_encap_pwm_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_init_to_mlkem_encap_pwm_write_rho_p);


property ctrl_mlkem_encap_pwm_write_rho_start_to_mlkem_encap_pwm_write_rho_init_p;
  mlkem_encap_pwm_write_rho_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_rho_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_pwm_write_rho_start_to_mlkem_encap_pwm_write_rho_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_start_to_mlkem_encap_pwm_write_rho_init_p);


property ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_immediate_p;
  mlkem_encap_pwm_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_immediate_p);


property ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_p;
  mlkem_encap_pwm_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_p);


property ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_1_p;
  mlkem_encap_pwm_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_to_mlkem_encap_pwm_write_rho_1_p);


property ctrl_mlkem_encap_pwma_ty_idle_to_mlkem_encap_pwma_ty_start_p;
  mlkem_encap_pwma_ty_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwma_ty_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_15_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_encap_pwma_ty_idle_to_mlkem_encap_pwma_ty_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_idle_to_mlkem_encap_pwma_ty_start_p);


property ctrl_mlkem_encap_pwma_ty_start_to_mlkem_encap_pwma_ty_p;
  mlkem_encap_pwma_ty_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwma_ty &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwma_ty_start_to_mlkem_encap_pwma_ty_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_start_to_mlkem_encap_pwma_ty_p);


property ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_intt_v_idle_p;
  mlkem_encap_pwma_ty &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pwma_ty_idx))} ) >= 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_intt_v_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  mlkem_encap_pwma_ty_idx == 3'd0 &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_intt_v_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_intt_v_idle_p);


property ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_p;
  mlkem_encap_pwma_ty &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwma_ty &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_p);


property ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_idle_p;
  mlkem_encap_pwma_ty &&
  ntt_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_encap_pwma_ty_idx))} ) < 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_pwma_ty_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  mlkem_encap_pwma_ty_idx == (3'd1 + $past(mlkem_encap_pwma_ty_idx, 1)) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_to_mlkem_encap_pwma_ty_idle_p);


property ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_p;
  mlkem_encap_sha512_done &&
  from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_sha512_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_p);


property ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_1_p;
  mlkem_encap_sha512_done &&
  !from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_sha512_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_done_to_mlkem_encap_sha512_done_1_p);

//Note: This assertion is disabled since a sampler_done i.e the sampler_busy deassertion cannot happen 
// at the same time as the keccak sending in a valid i.e from_keccak_piso_vld_in being high.
// This is because valids from the keccak core to sampler top is received only during sampler_busy high period.
// Hence the first property below is disabled. The second property covers the case when from_keccak_piso_vld_in is low
// when sampler_done_in goes high.
property ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_p;
  mlkem_encap_sha512_done &&
  from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_y_e1_e2_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == 4'd0 &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
//ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_p);


property ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_1_p;
  mlkem_encap_sha512_done &&
  !from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_y_e1_e2_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == 4'd0 &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_done_to_mlkem_encap_y_e1_e2_SHA3_START_1_p);


property ctrl_mlkem_encap_sha512_to_mlkem_encap_sha512_done_p;
  mlkem_encap_sha512
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_sha512_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_sha512_to_mlkem_encap_sha512_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_to_mlkem_encap_sha512_done_p);


property ctrl_mlkem_encap_write_ct_msg_256_init_to_mlkem_encap_write_ct_msg_256_p;
  mlkem_encap_write_ct_msg_256_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ct_msg_256_init_to_mlkem_encap_write_ct_msg_256_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_init_to_mlkem_encap_write_ct_msg_256_p);


property ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_p;
  mlkem_encap_write_ct_msg_256 &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_p);


property ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_1_p;
  mlkem_encap_write_ct_msg_256 &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_17_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_256_1_p);


property ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_done_p;
  mlkem_encap_write_ct_msg_256 &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak.strobe == to_keccak_17_i.strobe && //here strobe is zero so need to check the data
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_to_mlkem_encap_write_ct_msg_done_p);


property ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_ct_shake256_p;
  mlkem_encap_write_ct_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_encap_ct_shake256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_7_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_ct_shake256_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_ct_shake256_p);


property ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_write_ct_msg_done_p;
  mlkem_encap_write_ct_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_write_ct_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_done_to_mlkem_encap_write_ct_msg_done_p);


property ctrl_mlkem_encap_write_ek_START_to_mlkem_encap_write_ek_init_p;
  mlkem_encap_write_ek_START
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_write_ek_START_to_mlkem_encap_write_ek_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_START_to_mlkem_encap_write_ek_init_p);


property ctrl_mlkem_encap_write_ek_init_to_mlkem_encap_write_ek_p;
  mlkem_encap_write_ek_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ek_init_to_mlkem_encap_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_init_to_mlkem_encap_write_ek_p);


property ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_ek_sampling_start_p;
  mlkem_encap_write_ek_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_encap_ek_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_3_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_ek_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_ek_sampling_start_p);


property ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_write_ek_msg_done_p;
  mlkem_encap_write_ek_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_msg_done_to_mlkem_encap_write_ek_msg_done_p);


property ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_p;
  mlkem_encap_write_ek &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_p);


property ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_1_p;
  mlkem_encap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_1_p);


property ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_2_p;
  mlkem_encap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_2_p);


property ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_msg_done_p;
  mlkem_encap_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_to_mlkem_encap_write_ek_msg_done_p);


property ctrl_mlkem_encap_write_msg_256_START_to_mlkem_encap_write_msg_256_init_p;
  mlkem_encap_write_msg_256_START
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_write_msg_256_START_to_mlkem_encap_write_msg_256_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_START_to_mlkem_encap_write_msg_256_init_p);


property ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_done_p;
  mlkem_encap_write_msg_256_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_done_p);


property ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_wait_p;
  mlkem_encap_write_msg_256_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256_wait &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_wait_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_done_to_mlkem_encap_write_msg_256_wait_p);


property ctrl_mlkem_encap_write_msg_256_init_to_mlkem_encap_write_msg_256_p;
  mlkem_encap_write_msg_256_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_15_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_256_init_to_mlkem_encap_write_msg_256_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_init_to_mlkem_encap_write_msg_256_p);


property ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_p;
  mlkem_encap_write_msg_256 &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_p);


property ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_1_p;
  mlkem_encap_write_msg_256 &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_16_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_1_p);


property ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_done_p;
  mlkem_encap_write_msg_256 &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_256_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_16_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_to_mlkem_encap_write_msg_256_done_p);


property ctrl_mlkem_encap_write_msg_256_wait_to_mlkem_encap_write_ct_msg_256_init_p;
  mlkem_encap_write_msg_256_wait
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_ct_msg_256_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_256_wait_to_mlkem_encap_write_ct_msg_256_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_wait_to_mlkem_encap_write_ct_msg_256_init_p);


property ctrl_mlkem_encap_write_msg_START_to_mlkem_encap_write_msg_init_p;
  mlkem_encap_write_msg_START
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_write_msg_START_to_mlkem_encap_write_msg_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_START_to_mlkem_encap_write_msg_init_p);


property ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_done_p;
  mlkem_encap_write_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_done_p);


property ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_wait_p;
  mlkem_encap_write_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_wait &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_wait_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_done_to_mlkem_encap_write_msg_wait_p);


property ctrl_mlkem_encap_write_msg_init_to_mlkem_encap_write_msg_p;
  mlkem_encap_write_msg_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_init_to_mlkem_encap_write_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_init_to_mlkem_encap_write_msg_p);


property ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_p;
  mlkem_encap_write_msg &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_p);


property ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_1_p;
  mlkem_encap_write_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_9_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_1_p);


property ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_done_p;
  mlkem_encap_write_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_9_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_to_mlkem_encap_write_msg_done_p);


property ctrl_mlkem_encap_write_msg_wait_to_mlkem_encap_write_tr_msg_init_p;
  mlkem_encap_write_msg_wait
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_msg_wait_to_mlkem_encap_write_tr_msg_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_wait_to_mlkem_encap_write_tr_msg_init_p);


property ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_sha512_p;
  mlkem_encap_write_tr_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_encap_sha512 &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_4_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_sha512_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_sha512_p);


property ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_write_tr_msg_done_p;
  mlkem_encap_write_tr_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_write_tr_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_done_to_mlkem_encap_write_tr_msg_done_p);


property ctrl_mlkem_encap_write_tr_msg_init_to_mlkem_encap_write_tr_msg_p;
  mlkem_encap_write_tr_msg_init
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_10_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_tr_msg_init_to_mlkem_encap_write_tr_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_init_to_mlkem_encap_write_tr_msg_p);


property ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_p;
  mlkem_encap_write_tr_msg &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_p);


property ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_1_p;
  mlkem_encap_write_tr_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_11_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_1_p);


property ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_done_p;
  mlkem_encap_write_tr_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd5)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_write_tr_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_11_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_to_mlkem_encap_write_tr_msg_done_p);


property ctrl_mlkem_encap_y_e1_e2_SHA3_START_to_mlkem_encap_y_e1_e2_msg_start_p;
  mlkem_encap_y_e1_e2_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_msg_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_encap_y_e1_e2_SHA3_START_to_mlkem_encap_y_e1_e2_msg_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_SHA3_START_to_mlkem_encap_y_e1_e2_msg_start_p);


property ctrl_mlkem_encap_y_e1_e2_msg_start_to_mlkem_encap_y_e1_e2_write_msg_init_p;
  mlkem_encap_y_e1_e2_msg_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write_msg_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_encap_y_e1_e2_msg_start_to_mlkem_encap_y_e1_e2_write_msg_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_msg_start_to_mlkem_encap_y_e1_e2_write_msg_init_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_to_mlkem_encap_y_e1_e2_sha_sampling_p;
  mlkem_encap_y_e1_e2_sha_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_sha_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_to_mlkem_encap_y_e1_e2_sha_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_to_mlkem_encap_y_e1_e2_sha_sampling_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_ntt_y_idle_p;
  mlkem_encap_y_e1_e2_sha_sampling &&
  sampler_done_in &&
  (({ 60'd0, 4'((4'd1 + cbd_idx))} ) >= 64'd9)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_ntt_y_idle &&
  $stable(N) &&
  cbd_idx == 4'd0 &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  mlkem_encap_ntt_y_idx == 3'd0 &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_ntt_y_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_ntt_y_idle_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_SHA3_START_p;
  mlkem_encap_y_e1_e2_sha_sampling &&
  sampler_done_in &&
  (({ 60'd0, 4'((4'd1 + cbd_idx))} ) < 64'd9)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_encap_y_e1_e2_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == (4'd1 + $past(cbd_idx, 2)) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_SHA3_START_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_sha_sampling_p;
  mlkem_encap_y_e1_e2_sha_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_sha_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_sha_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_to_mlkem_encap_y_e1_e2_sha_sampling_p);


property ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_immediate_p;
  mlkem_encap_y_e1_e2_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_immediate_p);


property ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_msg_done_p;
  mlkem_encap_y_e1_e2_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_12_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_immediate_to_mlkem_encap_y_e1_e2_write_msg_done_p);


property ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_sha_sampling_start_p;
  mlkem_encap_y_e1_e2_write_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_sha_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_5_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_sha_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_sha_sampling_start_p);


property ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_write_msg_done_p;
  mlkem_encap_y_e1_e2_write_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_msg_done_to_mlkem_encap_y_e1_e2_write_msg_done_p);


property ctrl_mlkem_encap_y_e1_e2_write_msg_init_to_mlkem_encap_y_e1_e2_write_p;
  mlkem_encap_y_e1_e2_write_msg_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_write_msg_init_to_mlkem_encap_y_e1_e2_write_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_msg_init_to_mlkem_encap_y_e1_e2_write_p);


property ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_p;
  mlkem_encap_y_e1_e2_write &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_p);


property ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_1_p;
  mlkem_encap_y_e1_e2_write &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_1_p);


property ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_immediate_p;
  mlkem_encap_y_e1_e2_write &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_y_e1_e2_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_to_mlkem_encap_y_e1_e2_write_immediate_p);


property ctrl_mlkem_keygen_SHA256_START_to_mlkem_keygen_write_ek_START_p;
  mlkem_keygen_SHA256_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek_START &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_keygen_SHA256_START_to_mlkem_keygen_write_ek_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_SHA256_START_to_mlkem_keygen_write_ek_START_p);


property ctrl_mlkem_keygen_cbd_SHA3_START_to_mlkem_keygen_cbd_msg_start_p;
  mlkem_keygen_cbd_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_msg_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_keygen_cbd_SHA3_START_to_mlkem_keygen_cbd_msg_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_SHA3_START_to_mlkem_keygen_cbd_msg_start_p);


property ctrl_mlkem_keygen_cbd_msg_start_to_mlkem_keygen_cbd_write_msg_init_p;
  mlkem_keygen_cbd_msg_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_keygen_cbd_msg_start_to_mlkem_keygen_cbd_write_msg_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_msg_start_to_mlkem_keygen_cbd_write_msg_init_p);


property ctrl_mlkem_keygen_cbd_sampling_start_to_mlkem_keygen_cbd_sampling_p;
  mlkem_keygen_cbd_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_sampling_start_to_mlkem_keygen_cbd_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_start_to_mlkem_keygen_cbd_sampling_p);


property ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_SHA3_START_p;
  mlkem_keygen_cbd_sampling &&
  sampler_done_in &&
  (({ 60'd0, 4'((4'd1 + N))} ) < 64'd8)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_cbd_SHA3_START &&
  N == (4'd1 + $past(N, 2)) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_SHA3_START_p);


property ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_sampling_p;
  mlkem_keygen_cbd_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_cbd_sampling_p);


property ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_ntt_idle_p;
  mlkem_keygen_cbd_sampling &&
  sampler_done_in &&
  (({ 60'd0, 4'((4'd1 + N))} ) >= 64'd8)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ntt_idle &&
  N == 4'd0 &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  mlkem_keygen_ntt_idx == 4'd0 &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_ntt_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_to_mlkem_keygen_ntt_idle_p);


property ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_immediate_p;
  mlkem_keygen_cbd_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_immediate_p);


property ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_msg_done_p;
  mlkem_keygen_cbd_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_3_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_immediate_to_mlkem_keygen_cbd_write_msg_done_p);


property ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_sampling_start_p;
  mlkem_keygen_cbd_write_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_keygen_cbd_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_1_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_sampling_start_p);


property ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_write_msg_done_p;
  mlkem_keygen_cbd_write_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_write_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_done_to_mlkem_keygen_cbd_write_msg_done_p);


property ctrl_mlkem_keygen_cbd_write_msg_init_to_mlkem_keygen_cbd_write_msg_p;
  mlkem_keygen_cbd_write_msg_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_cbd_write_msg_init_to_mlkem_keygen_cbd_write_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_init_to_mlkem_keygen_cbd_write_msg_p);


property ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_immediate_p;
  mlkem_keygen_cbd_write_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_immediate_p);


property ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_p;
  mlkem_keygen_cbd_write_msg &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_p);


property ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_1_p;
  mlkem_keygen_cbd_write_msg &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_cbd_write_msg &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_2_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_to_mlkem_keygen_cbd_write_msg_1_p);


property ctrl_mlkem_keygen_compress_dk_idle_to_mlkem_keygen_compress_dk_start_p;
  mlkem_keygen_compress_dk_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_dk_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_compress == $past(to_compress_1_i, 1) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_keygen_compress_dk_idle_to_mlkem_keygen_compress_dk_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_idle_to_mlkem_keygen_compress_dk_start_p);


property ctrl_mlkem_keygen_compress_dk_start_to_mlkem_keygen_compress_dk_p;
  mlkem_keygen_compress_dk_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_dk &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_compress_dk_start_to_mlkem_keygen_compress_dk_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_start_to_mlkem_keygen_compress_dk_p);


property ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_SHA256_START_p;
  mlkem_keygen_compress_dk &&
  compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_SHA256_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_SHA256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_SHA256_START_p);


property ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_compress_dk_p;
  mlkem_keygen_compress_dk &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_dk &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_compress_dk_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_to_mlkem_keygen_compress_dk_p);


property ctrl_mlkem_keygen_compress_ek_idle_to_mlkem_keygen_compress_ek_start_p;
  mlkem_keygen_compress_ek_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_ek_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_compress == $past(to_compress_0_i, 1) &&
  to_compress_vld == 1;
endproperty
ctrl_mlkem_keygen_compress_ek_idle_to_mlkem_keygen_compress_ek_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_idle_to_mlkem_keygen_compress_ek_start_p);


property ctrl_mlkem_keygen_compress_ek_start_to_mlkem_keygen_compress_ek_p;
  mlkem_keygen_compress_ek_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_compress_ek_start_to_mlkem_keygen_compress_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_start_to_mlkem_keygen_compress_ek_p);


property ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_dk_idle_p;
  mlkem_keygen_compress_ek &&
  compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_dk_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_dk_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_dk_idle_p);


property ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_ek_p;
  mlkem_keygen_compress_ek &&
  !compress_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_compress_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_to_mlkem_keygen_compress_ek_p);


property ctrl_mlkem_keygen_ek_sampling_start_to_mlkem_keygen_ek_sampling_p;
  mlkem_keygen_ek_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_ek_sampling_start_to_mlkem_keygen_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_start_to_mlkem_keygen_ek_sampling_p);


property ctrl_mlkem_keygen_ek_sampling_to_idle_p;
  mlkem_keygen_ek_sampling &&
  sampler_done_in &&
  (from_api.instr != MlkemkeygenDecap)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  idle &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2);
endproperty
ctrl_mlkem_keygen_ek_sampling_to_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_to_idle_p);


property ctrl_mlkem_keygen_ek_sampling_to_mlkem_decap_SHA256_START_p;
  mlkem_keygen_ek_sampling &&
  sampler_done_in &&
  ((from_api.instr == MlkemkeygenDecap))
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o))[*2] and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*3] and
  ##3
  mlkem_decap_SHA256_START &&
  N == $past(N, 3) &&
  cbd_idx == $past(cbd_idx, 3) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 3) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 3) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 3) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 3) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 3) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 3) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 3) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 3) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 3) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_ek_sampling_to_mlkem_decap_SHA256_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_to_mlkem_decap_SHA256_START_p);

// Note: This is not a possible transition in the current design,
// but included for completeness if the design changes in the future.
property ctrl_mlkem_keygen_ek_sampling_to_mlkem_encap_decompress_t0_start_p;
  mlkem_keygen_ek_sampling &&
  sampler_done_in &&
  (from_api.instr != MlkemDecap) &&
  (from_api.instr != MlkemkeygenDecap) &&
  ((from_api.instr == MlkemEncap) || mlkem_decaps_end_process)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_encap_decompress_t0_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_decompress == $past(to_decompress_1_i, 1) &&
  to_decompress_vld == 1;
endproperty
//ctrl_mlkem_keygen_ek_sampling_to_mlkem_encap_decompress_t0_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_to_mlkem_encap_decompress_t0_start_p);


property ctrl_mlkem_keygen_ek_sampling_to_mlkem_keygen_ek_sampling_p;
  mlkem_keygen_ek_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ek_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_ek_sampling_to_mlkem_keygen_ek_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_to_mlkem_keygen_ek_sampling_p);


property ctrl_mlkem_keygen_ntt_idle_to_mlkem_keygen_ntt_start_p;
  mlkem_keygen_ntt_idle
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ntt_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_ntt == $past(to_ntt_0_i, 1) &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_keygen_ntt_idle_to_mlkem_keygen_ntt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_idle_to_mlkem_keygen_ntt_start_p);


property ctrl_mlkem_keygen_ntt_start_to_mlkem_keygen_ntt_p;
  mlkem_keygen_ntt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ntt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_ntt_start_to_mlkem_keygen_ntt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_start_to_mlkem_keygen_ntt_p);


property ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_p;
  mlkem_keygen_ntt &&
  !ntt_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ntt &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_p);


property ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_idle_p;
  mlkem_keygen_ntt &&
  ntt_done_in &&
  (({ 60'd0, 4'((4'd1 + mlkem_keygen_ntt_idx))} ) < 64'd8)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_ntt_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  mlkem_keygen_ntt_idx == (4'd1 + $past(mlkem_keygen_ntt_idx, 1)) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_to_mlkem_keygen_ntt_idle_p);


property ctrl_mlkem_keygen_ntt_to_mlkem_keygen_pwm_write_rho_SHA3_START_p;
  mlkem_keygen_ntt &&
  ntt_done_in &&
  (({ 60'd0, 4'((4'd1 + mlkem_keygen_ntt_idx))} ) >= 64'd8)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_pwm_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == 4'd0 &&
  mlkem_keygen_pw_idx == 3'd0 &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_ntt_to_mlkem_keygen_pwm_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_to_mlkem_keygen_pwm_write_rho_SHA3_START_p);


property ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_to_mlkem_keygen_pwm_a_start_p;
  mlkem_keygen_pwm_a_rejection_sampling_start
|->
  mlkem_keygen_pwm_a_start &&
  N == N &&
  cbd_idx == cbd_idx &&
  mlkem_decap_ntt_idx == mlkem_decap_ntt_idx &&
  mlkem_decap_pwma_idx == mlkem_decap_pwma_idx &&
  mlkem_encap_ntt_y_idx == mlkem_encap_ntt_y_idx &&
  mlkem_encap_pw_idx == mlkem_encap_pw_idx &&
  mlkem_encap_pwa_idx == mlkem_encap_pwa_idx &&
  mlkem_encap_pwma_ty_idx == mlkem_encap_pwma_ty_idx &&
  mlkem_keygen_ntt_idx == mlkem_keygen_ntt_idx &&
  mlkem_keygen_pw_idx == mlkem_keygen_pw_idx &&
  mlkem_keygen_pwa_idx == mlkem_keygen_pwa_idx &&
  to_ntt == to_ntt_2_i &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_to_mlkem_keygen_pwm_a_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_to_mlkem_keygen_pwm_a_start_p);


property ctrl_mlkem_keygen_pwm_a_start_to_mlkem_keygen_pwm_a_p;
  mlkem_keygen_pwm_a_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_a_start_to_mlkem_keygen_pwm_a_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_start_to_mlkem_keygen_pwm_a_p);


property ctrl_mlkem_keygen_pwm_a_to_mlkem_Keygen_pwa_idle_p;
  mlkem_keygen_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_keygen_pwa_idx))} ) >= 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_Keygen_pwa_idle &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  mlkem_keygen_pwa_idx == 3'd0;
endproperty
ctrl_mlkem_keygen_pwm_a_to_mlkem_Keygen_pwa_idle_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_to_mlkem_Keygen_pwa_idle_p);


property ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_p;
  mlkem_keygen_pwm_a &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_p);


property ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_p;
  mlkem_keygen_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  (({ 61'd0, 3'((3'd1 + mlkem_keygen_pwa_idx))} ) < 64'd3)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_pwm_a_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == (3'd1 + $past(mlkem_keygen_pwa_idx, 2)) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_rejection_sampling_start_p;
  mlkem_keygen_pwm_a_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld)) and
  ##1
  mlkem_keygen_pwm_a_rejection_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_2_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_rejection_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_rejection_sampling_start_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_write_immediate_msg_done_p;
  mlkem_keygen_pwm_a_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_to_mlkem_keygen_pwm_a_write_immediate_msg_done_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_p;
  mlkem_keygen_pwm_a_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_msg_done_p;
  mlkem_keygen_pwm_a_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_6_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_to_mlkem_keygen_pwm_a_write_immediate_msg_done_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_to_mlkem_keygen_pwm_a_write_rho_start_p;
  mlkem_keygen_pwm_a_write_rho_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_rho_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_to_mlkem_keygen_pwm_a_write_rho_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_to_mlkem_keygen_pwm_a_write_rho_start_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_init_to_mlkem_keygen_pwm_a_write_rho_p;
  mlkem_keygen_pwm_a_write_rho_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_init_to_mlkem_keygen_pwm_a_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_init_to_mlkem_keygen_pwm_a_write_rho_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_start_to_mlkem_keygen_pwm_a_write_rho_init_p;
  mlkem_keygen_pwm_a_write_rho_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_rho_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_start_to_mlkem_keygen_pwm_a_write_rho_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_start_to_mlkem_keygen_pwm_a_write_rho_init_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_immediate_p;
  mlkem_keygen_pwm_a_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_immediate_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_p;
  mlkem_keygen_pwm_a_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_1_p;
  mlkem_keygen_pwm_a_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_a_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_to_mlkem_keygen_pwm_a_write_rho_1_p);


property ctrl_mlkem_keygen_pwm_ntt_start_to_mlkem_keygen_pwm_p;
  mlkem_keygen_pwm_ntt_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_ntt_start_to_mlkem_keygen_pwm_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_ntt_start_to_mlkem_keygen_pwm_p);


property ctrl_mlkem_keygen_pwm_rejection_sampling_start_to_mlkem_keygen_pwm_ntt_start_p;
  mlkem_keygen_pwm_rejection_sampling_start
|->
  mlkem_keygen_pwm_ntt_start &&
  N == N &&
  cbd_idx == cbd_idx &&
  mlkem_decap_ntt_idx == mlkem_decap_ntt_idx &&
  mlkem_decap_pwma_idx == mlkem_decap_pwma_idx &&
  mlkem_encap_ntt_y_idx == mlkem_encap_ntt_y_idx &&
  mlkem_encap_pw_idx == mlkem_encap_pw_idx &&
  mlkem_encap_pwa_idx == mlkem_encap_pwa_idx &&
  mlkem_encap_pwma_ty_idx == mlkem_encap_pwma_ty_idx &&
  mlkem_keygen_ntt_idx == mlkem_keygen_ntt_idx &&
  mlkem_keygen_pw_idx == mlkem_keygen_pw_idx &&
  mlkem_keygen_pwa_idx == mlkem_keygen_pwa_idx &&
  to_ntt == to_ntt_1_i &&
  to_ntt_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_rejection_sampling_start_to_mlkem_keygen_pwm_ntt_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_rejection_sampling_start_to_mlkem_keygen_pwm_ntt_start_p);


property ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_p;
  mlkem_keygen_pwm &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_p);


property ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_p;
  mlkem_keygen_pwm &&
  ntt_done_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_pwm_a_write_rho_SHA3_START &&
  N == $past(N, 2) &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == 3'd0 &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_to_mlkem_keygen_pwm_a_write_rho_SHA3_START_p);


property ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_rejection_sampling_start_p;
  mlkem_keygen_pwm_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld)) and
  ##1
  mlkem_keygen_pwm_rejection_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_2_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_rejection_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_rejection_sampling_start_p);


property ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_write_immediate_msg_done_p;
  mlkem_keygen_pwm_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_msg_done_to_mlkem_keygen_pwm_write_immediate_msg_done_p);


property ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_p;
  mlkem_keygen_pwm_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_p);


property ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_msg_done_p;
  mlkem_keygen_pwm_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_immediate_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_5_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_to_mlkem_keygen_pwm_write_immediate_msg_done_p);


property ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_to_mlkem_keygen_pwm_write_rho_start_p;
  mlkem_keygen_pwm_write_rho_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_rho_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_to_mlkem_keygen_pwm_write_rho_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_to_mlkem_keygen_pwm_write_rho_start_p);


property ctrl_mlkem_keygen_pwm_write_rho_init_to_mlkem_keygen_pwm_write_rho_p;
  mlkem_keygen_pwm_write_rho_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_write_rho_init_to_mlkem_keygen_pwm_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_init_to_mlkem_keygen_pwm_write_rho_p);


property ctrl_mlkem_keygen_pwm_write_rho_start_to_mlkem_keygen_pwm_write_rho_init_p;
  mlkem_keygen_pwm_write_rho_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_rho_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_keygen_pwm_write_rho_start_to_mlkem_keygen_pwm_write_rho_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_start_to_mlkem_keygen_pwm_write_rho_init_p);


property ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_immediate_p;
  mlkem_keygen_pwm_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_immediate_p);


property ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_p;
  mlkem_keygen_pwm_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_p);


property ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_1_p;
  mlkem_keygen_pwm_write_rho &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_pwm_write_rho &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_4_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_to_mlkem_keygen_pwm_write_rho_1_p);


property ctrl_mlkem_keygen_rnd_seed_SHA3_START_to_mlkem_keygen_rnd_seed_start_p;
  mlkem_keygen_rnd_seed_SHA3_START
|->
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_rnd_seed_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 1 &&
  sha3_start_o == 0;
endproperty
ctrl_mlkem_keygen_rnd_seed_SHA3_START_to_mlkem_keygen_rnd_seed_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_rnd_seed_SHA3_START_to_mlkem_keygen_rnd_seed_start_p);


property ctrl_mlkem_keygen_rnd_seed_start_to_mlkem_keygen_write_seed_init_p;
  mlkem_keygen_rnd_seed_start
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_keygen_rnd_seed_start_to_mlkem_keygen_write_seed_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_rnd_seed_start_to_mlkem_keygen_write_seed_init_p);


property ctrl_mlkem_keygen_seed_sha_sampling_start_to_mlkem_keygen_seed_sha_sampling_p;
  mlkem_keygen_seed_sha_sampling_start
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_seed_sha_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_start_to_mlkem_keygen_seed_sha_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_start_to_mlkem_keygen_seed_sha_sampling_p);

//Note: This assertion is disabled since a sampler_done i.e the sampler_busy deassertion cannot happen 
// at the same time as the keccak sending in a valid i.e from_keccak_piso_vld_in being high.
// This is because valids from the keccak core to sampler top is received only during sampler_busy high period.
// Hence the first property below is disabled. The second property covers the case when from_keccak_piso_vld_in is low
// when sampler_done_in goes high.
property ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_p;
  mlkem_keygen_seed_sha_sampling &&
  from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_cbd_SHA3_START &&
  N == 4'd0 &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
//ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_p);


property ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_1_p;
  mlkem_keygen_seed_sha_sampling &&
  !from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o)) and
  ##1 ((to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0))[*2] and
  ##2
  mlkem_keygen_cbd_SHA3_START &&
  N == 4'd0 &&
  cbd_idx == $past(cbd_idx, 2) &&
  mlkem_decap_ntt_idx == $past(mlkem_decap_ntt_idx, 2) &&
  mlkem_decap_pwma_idx == $past(mlkem_decap_pwma_idx, 2) &&
  mlkem_encap_ntt_y_idx == $past(mlkem_encap_ntt_y_idx, 2) &&
  mlkem_encap_pw_idx == $past(mlkem_encap_pw_idx, 2) &&
  mlkem_encap_pwa_idx == $past(mlkem_encap_pwa_idx, 2) &&
  mlkem_encap_pwma_ty_idx == $past(mlkem_encap_pwma_ty_idx, 2) &&
  mlkem_keygen_ntt_idx == $past(mlkem_keygen_ntt_idx, 2) &&
  mlkem_keygen_pw_idx == $past(mlkem_keygen_pw_idx, 2) &&
  mlkem_keygen_pwa_idx == $past(mlkem_keygen_pwa_idx, 2) &&
  msg_start_o == 0 &&
  sha3_start_o == 1;
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_cbd_SHA3_START_1_p);


property ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_p;
  mlkem_keygen_seed_sha_sampling &&
  from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_seed_sha_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_p);


property ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_1_p;
  mlkem_keygen_seed_sha_sampling &&
  !from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_seed_sha_sampling &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_to_mlkem_keygen_seed_sha_sampling_1_p);


property ctrl_mlkem_keygen_write_ek_START_to_mlkem_keygen_write_ek_init_p;
  mlkem_keygen_write_ek_START
|->
  ##1 ($stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek_init &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  msg_start_o == 0;
endproperty
ctrl_mlkem_keygen_write_ek_START_to_mlkem_keygen_write_ek_init_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_START_to_mlkem_keygen_write_ek_init_p);


property ctrl_mlkem_keygen_write_ek_init_to_mlkem_keygen_write_ek_p;
  mlkem_keygen_write_ek_init &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_ek_init_to_mlkem_keygen_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_init_to_mlkem_keygen_write_ek_p);


property ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_ek_sampling_start_p;
  mlkem_keygen_write_ek_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_keygen_ek_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_3_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_ek_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_ek_sampling_start_p);


property ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_write_ek_msg_done_p;
  mlkem_keygen_write_ek_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_msg_done_to_mlkem_keygen_write_ek_msg_done_p);


property ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_p;
  mlkem_keygen_write_ek &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_p);


property ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_1_p;
  mlkem_keygen_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) < 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_7_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_1_p);


property ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_2_p;
  mlkem_keygen_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_2_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_2_p);


property ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_msg_done_p;
  mlkem_keygen_write_ek &&
  to_keccak_rdy &&
  (({ 48'd0, sipo_chunk_idx} ) >= 64'd192) &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd197)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_ek_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_8_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_to_mlkem_keygen_write_ek_msg_done_p);


property ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_immediate_p;
  mlkem_keygen_write_seed_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_immediate_p);


property ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_msg_done_p;
  mlkem_keygen_write_seed_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == to_keccak_1_i &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_immediate_to_mlkem_keygen_write_seed_msg_done_p);


property ctrl_mlkem_keygen_write_seed_init_to_mlkem_keygen_write_seed_p;
  mlkem_keygen_write_seed_init
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_0_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_seed_init_to_mlkem_keygen_write_seed_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_init_to_mlkem_keygen_write_seed_p);


property ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_seed_sha_sampling_start_p;
  mlkem_keygen_write_seed_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_keccak_vld == 0) &&
    (to_ntt_vld == 0)) and
  ##1
  mlkem_keygen_seed_sha_sampling_start &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_sampler == $past(to_sampler_0_i, 1) &&
  to_sampler_vld == 1;
endproperty
ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_seed_sha_sampling_start_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_seed_sha_sampling_start_p);


property ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_write_seed_msg_done_p;
  mlkem_keygen_write_seed_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed_msg_done &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_write_seed_msg_done_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_msg_done_to_mlkem_keygen_write_seed_msg_done_p);


property ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_p;
  mlkem_keygen_write_seed &&
  !to_keccak_rdy
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    ($stable(to_keccak_vld)&&$stable(to_keccak)) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx);
endproperty
ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_p);


property ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_1_p;
  mlkem_keygen_write_seed &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) < 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_0_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_1_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_1_p);


property ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_immediate_p;
  mlkem_keygen_write_seed &&
  to_keccak_rdy &&
  (({ 48'd0, 16'((16'd1 + sipo_chunk_idx))} ) >= 64'd4)
|->
  ##1 ($stable(msg_start_o) &&
    $stable(sha3_start_o) &&
    (to_compress_vld == 0) &&
    (to_decompress_vld == 0) &&
    (to_ntt_vld == 0) &&
    (to_sampler_vld == 0)) and
  ##1
  mlkem_keygen_write_seed_immediate &&
  $stable(N) &&
  $stable(cbd_idx) &&
  $stable(mlkem_decap_ntt_idx) &&
  $stable(mlkem_decap_pwma_idx) &&
  $stable(mlkem_encap_ntt_y_idx) &&
  $stable(mlkem_encap_pw_idx) &&
  $stable(mlkem_encap_pwa_idx) &&
  $stable(mlkem_encap_pwma_ty_idx) &&
  $stable(mlkem_keygen_ntt_idx) &&
  $stable(mlkem_keygen_pw_idx) &&
  $stable(mlkem_keygen_pwa_idx) &&
  to_keccak == $past(to_keccak_0_i, 1) &&
  to_keccak_vld == 1;
endproperty
ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_immediate_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_to_mlkem_keygen_write_seed_immediate_p);


property ctrl_idle_eventually_left_p;
  idle &&
  (api_in.instr != NoOp)
|->
  s_eventually(!idle);
endproperty
ctrl_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_idle_eventually_left_p);


property ctrl_mlkem_keygen_rnd_seed_SHA3_START_eventually_left_p;
  mlkem_keygen_rnd_seed_SHA3_START
|->
  s_eventually(!mlkem_keygen_rnd_seed_SHA3_START);
endproperty
ctrl_mlkem_keygen_rnd_seed_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_rnd_seed_SHA3_START_eventually_left_p);


property ctrl_mlkem_keygen_rnd_seed_start_eventually_left_p;
  mlkem_keygen_rnd_seed_start
|->
  s_eventually(!mlkem_keygen_rnd_seed_start);
endproperty
ctrl_mlkem_keygen_rnd_seed_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_rnd_seed_start_eventually_left_p);


property ctrl_mlkem_keygen_write_seed_init_eventually_left_p;
  mlkem_keygen_write_seed_init
|->
  s_eventually(!mlkem_keygen_write_seed_init);
endproperty
ctrl_mlkem_keygen_write_seed_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_init_eventually_left_p);


property ctrl_mlkem_keygen_write_seed_eventually_left_p;
  mlkem_keygen_write_seed
|->
  s_eventually(!mlkem_keygen_write_seed);
endproperty
ctrl_mlkem_keygen_write_seed_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_eventually_left_p);


property ctrl_mlkem_keygen_write_seed_immediate_eventually_left_p;
  mlkem_keygen_write_seed_immediate
|->
  s_eventually(!mlkem_keygen_write_seed_immediate);
endproperty
ctrl_mlkem_keygen_write_seed_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_immediate_eventually_left_p);


property ctrl_mlkem_keygen_write_seed_msg_done_eventually_left_p;
  mlkem_keygen_write_seed_msg_done
|->
  s_eventually(!mlkem_keygen_write_seed_msg_done);
endproperty
ctrl_mlkem_keygen_write_seed_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_seed_msg_done_eventually_left_p);


property ctrl_mlkem_keygen_seed_sha_sampling_start_eventually_left_p;
  mlkem_keygen_seed_sha_sampling_start
|->
  s_eventually(!mlkem_keygen_seed_sha_sampling_start);
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_start_eventually_left_p);


property ctrl_mlkem_keygen_seed_sha_sampling_eventually_left_p;
  mlkem_keygen_seed_sha_sampling
|->
  s_eventually(!mlkem_keygen_seed_sha_sampling);
endproperty
ctrl_mlkem_keygen_seed_sha_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_seed_sha_sampling_eventually_left_p);


property ctrl_mlkem_keygen_cbd_SHA3_START_eventually_left_p;
  mlkem_keygen_cbd_SHA3_START
|->
  s_eventually(!mlkem_keygen_cbd_SHA3_START);
endproperty
ctrl_mlkem_keygen_cbd_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_SHA3_START_eventually_left_p);


property ctrl_mlkem_keygen_cbd_msg_start_eventually_left_p;
  mlkem_keygen_cbd_msg_start
|->
  s_eventually(!mlkem_keygen_cbd_msg_start);
endproperty
ctrl_mlkem_keygen_cbd_msg_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_msg_start_eventually_left_p);


property ctrl_mlkem_keygen_cbd_write_msg_init_eventually_left_p;
  mlkem_keygen_cbd_write_msg_init
|->
  s_eventually(!mlkem_keygen_cbd_write_msg_init);
endproperty
ctrl_mlkem_keygen_cbd_write_msg_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_init_eventually_left_p);


property ctrl_mlkem_keygen_cbd_write_msg_eventually_left_p;
  mlkem_keygen_cbd_write_msg
|->
  s_eventually(!mlkem_keygen_cbd_write_msg);
endproperty
ctrl_mlkem_keygen_cbd_write_msg_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_eventually_left_p);


property ctrl_mlkem_keygen_cbd_write_immediate_eventually_left_p;
  mlkem_keygen_cbd_write_immediate
|->
  s_eventually(!mlkem_keygen_cbd_write_immediate);
endproperty
ctrl_mlkem_keygen_cbd_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_immediate_eventually_left_p);


property ctrl_mlkem_keygen_cbd_write_msg_done_eventually_left_p;
  mlkem_keygen_cbd_write_msg_done
|->
  s_eventually(!mlkem_keygen_cbd_write_msg_done);
endproperty
ctrl_mlkem_keygen_cbd_write_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_write_msg_done_eventually_left_p);


property ctrl_mlkem_keygen_cbd_sampling_start_eventually_left_p;
  mlkem_keygen_cbd_sampling_start
|->
  s_eventually(!mlkem_keygen_cbd_sampling_start);
endproperty
ctrl_mlkem_keygen_cbd_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_start_eventually_left_p);


property ctrl_mlkem_keygen_cbd_sampling_eventually_left_p;
  mlkem_keygen_cbd_sampling
|->
  s_eventually(!mlkem_keygen_cbd_sampling);
endproperty
ctrl_mlkem_keygen_cbd_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_cbd_sampling_eventually_left_p);


property ctrl_mlkem_keygen_ntt_idle_eventually_left_p;
  mlkem_keygen_ntt_idle
|->
  s_eventually(!mlkem_keygen_ntt_idle);
endproperty
ctrl_mlkem_keygen_ntt_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_idle_eventually_left_p);


property ctrl_mlkem_keygen_ntt_start_eventually_left_p;
  mlkem_keygen_ntt_start
|->
  s_eventually(!mlkem_keygen_ntt_start);
endproperty
ctrl_mlkem_keygen_ntt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_start_eventually_left_p);


property ctrl_mlkem_keygen_ntt_eventually_left_p;
  mlkem_keygen_ntt
|->
  s_eventually(!mlkem_keygen_ntt);
endproperty
ctrl_mlkem_keygen_ntt_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ntt_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_eventually_left_p;
  mlkem_keygen_pwm_write_rho_SHA3_START
|->
  s_eventually(!mlkem_keygen_pwm_write_rho_SHA3_START);
endproperty
ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_SHA3_START_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_rho_start_eventually_left_p;
  mlkem_keygen_pwm_write_rho_start
|->
  s_eventually(!mlkem_keygen_pwm_write_rho_start);
endproperty
ctrl_mlkem_keygen_pwm_write_rho_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_rho_init_eventually_left_p;
  mlkem_keygen_pwm_write_rho_init
|->
  s_eventually(!mlkem_keygen_pwm_write_rho_init);
endproperty
ctrl_mlkem_keygen_pwm_write_rho_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_init_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_rho_eventually_left_p;
  mlkem_keygen_pwm_write_rho
|->
  s_eventually(!mlkem_keygen_pwm_write_rho);
endproperty
ctrl_mlkem_keygen_pwm_write_rho_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_rho_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_immediate_eventually_left_p;
  mlkem_keygen_pwm_write_immediate
|->
  s_eventually(!mlkem_keygen_pwm_write_immediate);
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_eventually_left_p);


property ctrl_mlkem_keygen_pwm_write_immediate_msg_done_eventually_left_p;
  mlkem_keygen_pwm_write_immediate_msg_done
|->
  s_eventually(!mlkem_keygen_pwm_write_immediate_msg_done);
endproperty
ctrl_mlkem_keygen_pwm_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_write_immediate_msg_done_eventually_left_p);


property ctrl_mlkem_keygen_pwm_rejection_sampling_start_eventually_left_p;
  mlkem_keygen_pwm_rejection_sampling_start
|->
  s_eventually(!mlkem_keygen_pwm_rejection_sampling_start);
endproperty
ctrl_mlkem_keygen_pwm_rejection_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_rejection_sampling_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_ntt_start_eventually_left_p;
  mlkem_keygen_pwm_ntt_start
|->
  s_eventually(!mlkem_keygen_pwm_ntt_start);
endproperty
ctrl_mlkem_keygen_pwm_ntt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_ntt_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_eventually_left_p;
  mlkem_keygen_pwm
|->
  s_eventually(!mlkem_keygen_pwm);
endproperty
ctrl_mlkem_keygen_pwm_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_eventually_left_p;
  mlkem_keygen_pwm_a_write_rho_SHA3_START
|->
  s_eventually(!mlkem_keygen_pwm_a_write_rho_SHA3_START);
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_SHA3_START_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_start_eventually_left_p;
  mlkem_keygen_pwm_a_write_rho_start
|->
  s_eventually(!mlkem_keygen_pwm_a_write_rho_start);
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_init_eventually_left_p;
  mlkem_keygen_pwm_a_write_rho_init
|->
  s_eventually(!mlkem_keygen_pwm_a_write_rho_init);
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_init_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_rho_eventually_left_p;
  mlkem_keygen_pwm_a_write_rho
|->
  s_eventually(!mlkem_keygen_pwm_a_write_rho);
endproperty
ctrl_mlkem_keygen_pwm_a_write_rho_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_rho_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_eventually_left_p;
  mlkem_keygen_pwm_a_write_immediate
|->
  s_eventually(!mlkem_keygen_pwm_a_write_immediate);
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_eventually_left_p;
  mlkem_keygen_pwm_a_write_immediate_msg_done
|->
  s_eventually(!mlkem_keygen_pwm_a_write_immediate_msg_done);
endproperty
ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_write_immediate_msg_done_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_eventually_left_p;
  mlkem_keygen_pwm_a_rejection_sampling_start
|->
  s_eventually(!mlkem_keygen_pwm_a_rejection_sampling_start);
endproperty
ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_rejection_sampling_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_start_eventually_left_p;
  mlkem_keygen_pwm_a_start
|->
  s_eventually(!mlkem_keygen_pwm_a_start);
endproperty
ctrl_mlkem_keygen_pwm_a_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_start_eventually_left_p);


property ctrl_mlkem_keygen_pwm_a_eventually_left_p;
  mlkem_keygen_pwm_a
|->
  s_eventually(!mlkem_keygen_pwm_a);
endproperty
ctrl_mlkem_keygen_pwm_a_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_pwm_a_eventually_left_p);


property ctrl_mlkem_Keygen_pwa_idle_eventually_left_p;
  mlkem_Keygen_pwa_idle
|->
  s_eventually(!mlkem_Keygen_pwa_idle);
endproperty
ctrl_mlkem_Keygen_pwa_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_idle_eventually_left_p);


property ctrl_mlkem_Keygen_pwa_start_eventually_left_p;
  mlkem_Keygen_pwa_start
|->
  s_eventually(!mlkem_Keygen_pwa_start);
endproperty
ctrl_mlkem_Keygen_pwa_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_start_eventually_left_p);


property ctrl_mlkem_Keygen_pwa_eventually_left_p;
  mlkem_Keygen_pwa
|->
  s_eventually(!mlkem_Keygen_pwa);
endproperty
ctrl_mlkem_Keygen_pwa_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_Keygen_pwa_eventually_left_p);


property ctrl_mlkem_keygen_compress_ek_idle_eventually_left_p;
  mlkem_keygen_compress_ek_idle
|->
  s_eventually(!mlkem_keygen_compress_ek_idle);
endproperty
ctrl_mlkem_keygen_compress_ek_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_idle_eventually_left_p);


property ctrl_mlkem_keygen_compress_ek_start_eventually_left_p;
  mlkem_keygen_compress_ek_start
|->
  s_eventually(!mlkem_keygen_compress_ek_start);
endproperty
ctrl_mlkem_keygen_compress_ek_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_start_eventually_left_p);


property ctrl_mlkem_keygen_compress_ek_eventually_left_p;
  mlkem_keygen_compress_ek
|->
  s_eventually(!mlkem_keygen_compress_ek);
endproperty
ctrl_mlkem_keygen_compress_ek_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_ek_eventually_left_p);


property ctrl_mlkem_keygen_compress_dk_idle_eventually_left_p;
  mlkem_keygen_compress_dk_idle
|->
  s_eventually(!mlkem_keygen_compress_dk_idle);
endproperty
ctrl_mlkem_keygen_compress_dk_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_idle_eventually_left_p);


property ctrl_mlkem_keygen_compress_dk_start_eventually_left_p;
  mlkem_keygen_compress_dk_start
|->
  s_eventually(!mlkem_keygen_compress_dk_start);
endproperty
ctrl_mlkem_keygen_compress_dk_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_start_eventually_left_p);


property ctrl_mlkem_keygen_compress_dk_eventually_left_p;
  mlkem_keygen_compress_dk
|->
  s_eventually(!mlkem_keygen_compress_dk);
endproperty
ctrl_mlkem_keygen_compress_dk_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_compress_dk_eventually_left_p);


property ctrl_mlkem_keygen_SHA256_START_eventually_left_p;
  mlkem_keygen_SHA256_START
|->
  s_eventually(!mlkem_keygen_SHA256_START);
endproperty
ctrl_mlkem_keygen_SHA256_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_SHA256_START_eventually_left_p);


property ctrl_mlkem_keygen_write_ek_START_eventually_left_p;
  mlkem_keygen_write_ek_START
|->
  s_eventually(!mlkem_keygen_write_ek_START);
endproperty
ctrl_mlkem_keygen_write_ek_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_START_eventually_left_p);


property ctrl_mlkem_keygen_write_ek_init_eventually_left_p;
  mlkem_keygen_write_ek_init
|->
  s_eventually(!mlkem_keygen_write_ek_init);
endproperty
ctrl_mlkem_keygen_write_ek_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_init_eventually_left_p);


property ctrl_mlkem_keygen_write_ek_eventually_left_p;
  mlkem_keygen_write_ek
|->
  s_eventually(!mlkem_keygen_write_ek);
endproperty
ctrl_mlkem_keygen_write_ek_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_eventually_left_p);


property ctrl_mlkem_keygen_write_ek_msg_done_eventually_left_p;
  mlkem_keygen_write_ek_msg_done
|->
  s_eventually(!mlkem_keygen_write_ek_msg_done);
endproperty
ctrl_mlkem_keygen_write_ek_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_write_ek_msg_done_eventually_left_p);


property ctrl_mlkem_keygen_ek_sampling_start_eventually_left_p;
  mlkem_keygen_ek_sampling_start
|->
  s_eventually(!mlkem_keygen_ek_sampling_start);
endproperty
ctrl_mlkem_keygen_ek_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_start_eventually_left_p);


property ctrl_mlkem_keygen_ek_sampling_eventually_left_p;
  mlkem_keygen_ek_sampling
|->
  s_eventually(!mlkem_keygen_ek_sampling);
endproperty
ctrl_mlkem_keygen_ek_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_keygen_ek_sampling_eventually_left_p);


property ctrl_mlkem_decap_SHA256_START_eventually_left_p;
  mlkem_decap_SHA256_START
|->
  s_eventually(!mlkem_decap_SHA256_START);
endproperty
ctrl_mlkem_decap_SHA256_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_SHA256_START_eventually_left_p);


property ctrl_mlkem_decap_write_ek_START_eventually_left_p;
  mlkem_decap_write_ek_START
|->
  s_eventually(!mlkem_decap_write_ek_START);
endproperty
ctrl_mlkem_decap_write_ek_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_START_eventually_left_p);


property ctrl_mlkem_decap_write_ek_init_eventually_left_p;
  mlkem_decap_write_ek_init
|->
  s_eventually(!mlkem_decap_write_ek_init);
endproperty
ctrl_mlkem_decap_write_ek_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_init_eventually_left_p);


property ctrl_mlkem_decap_write_ek_eventually_left_p;
  mlkem_decap_write_ek
|->
  s_eventually(!mlkem_decap_write_ek);
endproperty
ctrl_mlkem_decap_write_ek_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_eventually_left_p);


property ctrl_mlkem_decap_write_ek_msg_done_eventually_left_p;
  mlkem_decap_write_ek_msg_done
|->
  s_eventually(!mlkem_decap_write_ek_msg_done);
endproperty
ctrl_mlkem_decap_write_ek_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_write_ek_msg_done_eventually_left_p);


property ctrl_mlkem_decap_ek_sampling_start_eventually_left_p;
  mlkem_decap_ek_sampling_start
|->
  s_eventually(!mlkem_decap_ek_sampling_start);
endproperty
ctrl_mlkem_decap_ek_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ek_sampling_start_eventually_left_p);


property ctrl_mlkem_decap_ek_sampling_eventually_left_p;
  mlkem_decap_ek_sampling
|->
  s_eventually(!mlkem_decap_ek_sampling);
endproperty
ctrl_mlkem_decap_ek_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ek_sampling_eventually_left_p);


property ctrl_mlkem_decap_decompress_s0_idle_eventually_left_p;
  mlkem_decap_decompress_s0_idle
|->
  s_eventually(!mlkem_decap_decompress_s0_idle);
endproperty
ctrl_mlkem_decap_decompress_s0_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_idle_eventually_left_p);


property ctrl_mlkem_decap_decompress_s0_start_eventually_left_p;
  mlkem_decap_decompress_s0_start
|->
  s_eventually(!mlkem_decap_decompress_s0_start);
endproperty
ctrl_mlkem_decap_decompress_s0_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_start_eventually_left_p);


property ctrl_mlkem_decap_decompress_s0_eventually_left_p;
  mlkem_decap_decompress_s0
|->
  s_eventually(!mlkem_decap_decompress_s0);
endproperty
ctrl_mlkem_decap_decompress_s0_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_s0_eventually_left_p);


property ctrl_mlkem_decap_decompress_u0_idle_eventually_left_p;
  mlkem_decap_decompress_u0_idle
|->
  s_eventually(!mlkem_decap_decompress_u0_idle);
endproperty
ctrl_mlkem_decap_decompress_u0_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_idle_eventually_left_p);


property ctrl_mlkem_decap_decompress_u0_start_eventually_left_p;
  mlkem_decap_decompress_u0_start
|->
  s_eventually(!mlkem_decap_decompress_u0_start);
endproperty
ctrl_mlkem_decap_decompress_u0_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_start_eventually_left_p);


property ctrl_mlkem_decap_decompress_u0_eventually_left_p;
  mlkem_decap_decompress_u0
|->
  s_eventually(!mlkem_decap_decompress_u0);
endproperty
ctrl_mlkem_decap_decompress_u0_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_u0_eventually_left_p);


property ctrl_mlkem_decap_decompress_v_idle_eventually_left_p;
  mlkem_decap_decompress_v_idle
|->
  s_eventually(!mlkem_decap_decompress_v_idle);
endproperty
ctrl_mlkem_decap_decompress_v_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_idle_eventually_left_p);


property ctrl_mlkem_decap_decompress_v_start_eventually_left_p;
  mlkem_decap_decompress_v_start
|->
  s_eventually(!mlkem_decap_decompress_v_start);
endproperty
ctrl_mlkem_decap_decompress_v_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_start_eventually_left_p);


property ctrl_mlkem_decap_decompress_v_eventually_left_p;
  mlkem_decap_decompress_v
|->
  s_eventually(!mlkem_decap_decompress_v);
endproperty
ctrl_mlkem_decap_decompress_v_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_decompress_v_eventually_left_p);


property ctrl_mlkem_decap_ntt_idle_eventually_left_p;
  mlkem_decap_ntt_idle
|->
  s_eventually(!mlkem_decap_ntt_idle);
endproperty
ctrl_mlkem_decap_ntt_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_idle_eventually_left_p);


property ctrl_mlkem_decap_ntt_start_eventually_left_p;
  mlkem_decap_ntt_start
|->
  s_eventually(!mlkem_decap_ntt_start);
endproperty
ctrl_mlkem_decap_ntt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_start_eventually_left_p);


property ctrl_mlkem_decap_ntt_eventually_left_p;
  mlkem_decap_ntt
|->
  s_eventually(!mlkem_decap_ntt);
endproperty
ctrl_mlkem_decap_ntt_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_ntt_eventually_left_p);


property ctrl_mlkem_decap_pwm_su_idle_eventually_left_p;
  mlkem_decap_pwm_su_idle
|->
  s_eventually(!mlkem_decap_pwm_su_idle);
endproperty
ctrl_mlkem_decap_pwm_su_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_idle_eventually_left_p);


property ctrl_mlkem_decap_pwm_su_start_eventually_left_p;
  mlkem_decap_pwm_su_start
|->
  s_eventually(!mlkem_decap_pwm_su_start);
endproperty
ctrl_mlkem_decap_pwm_su_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_start_eventually_left_p);


property ctrl_mlkem_decap_pwm_su_eventually_left_p;
  mlkem_decap_pwm_su
|->
  s_eventually(!mlkem_decap_pwm_su);
endproperty
ctrl_mlkem_decap_pwm_su_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwm_su_eventually_left_p);


property ctrl_mlkem_decap_pwma_su_idle_eventually_left_p;
  mlkem_decap_pwma_su_idle
|->
  s_eventually(!mlkem_decap_pwma_su_idle);
endproperty
ctrl_mlkem_decap_pwma_su_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_idle_eventually_left_p);


property ctrl_mlkem_decap_pwma_su_start_eventually_left_p;
  mlkem_decap_pwma_su_start
|->
  s_eventually(!mlkem_decap_pwma_su_start);
endproperty
ctrl_mlkem_decap_pwma_su_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_start_eventually_left_p);


property ctrl_mlkem_decap_pwma_su_eventually_left_p;
  mlkem_decap_pwma_su
|->
  s_eventually(!mlkem_decap_pwma_su);
endproperty
ctrl_mlkem_decap_pwma_su_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pwma_su_eventually_left_p);


property ctrl_mlkem_decap_intt_su_idle_eventually_left_p;
  mlkem_decap_intt_su_idle
|->
  s_eventually(!mlkem_decap_intt_su_idle);
endproperty
ctrl_mlkem_decap_intt_su_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_idle_eventually_left_p);


property ctrl_mlkem_decap_intt_su_start_eventually_left_p;
  mlkem_decap_intt_su_start
|->
  s_eventually(!mlkem_decap_intt_su_start);
endproperty
ctrl_mlkem_decap_intt_su_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_start_eventually_left_p);


property ctrl_mlkem_decap_intt_su_eventually_left_p;
  mlkem_decap_intt_su
|->
  s_eventually(!mlkem_decap_intt_su);
endproperty
ctrl_mlkem_decap_intt_su_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_intt_su_eventually_left_p);


property ctrl_mlkem_decap_pws_su_idle_eventually_left_p;
  mlkem_decap_pws_su_idle
|->
  s_eventually(!mlkem_decap_pws_su_idle);
endproperty
ctrl_mlkem_decap_pws_su_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_idle_eventually_left_p);


property ctrl_mlkem_decap_pws_su_start_eventually_left_p;
  mlkem_decap_pws_su_start
|->
  s_eventually(!mlkem_decap_pws_su_start);
endproperty
ctrl_mlkem_decap_pws_su_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_start_eventually_left_p);


property ctrl_mlkem_decap_pws_su_eventually_left_p;
  mlkem_decap_pws_su
|->
  s_eventually(!mlkem_decap_pws_su);
endproperty
ctrl_mlkem_decap_pws_su_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_pws_su_eventually_left_p);


property ctrl_mlkem_decap_compress_msg_idle_eventually_left_p;
  mlkem_decap_compress_msg_idle
|->
  s_eventually(!mlkem_decap_compress_msg_idle);
endproperty
ctrl_mlkem_decap_compress_msg_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_idle_eventually_left_p);


property ctrl_mlkem_decap_compress_msg_start_eventually_left_p;
  mlkem_decap_compress_msg_start
|->
  s_eventually(!mlkem_decap_compress_msg_start);
endproperty
ctrl_mlkem_decap_compress_msg_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_start_eventually_left_p);


property ctrl_mlkem_decap_compress_msg_eventually_left_p;
  mlkem_decap_compress_msg
|->
  s_eventually(!mlkem_decap_compress_msg);
endproperty
ctrl_mlkem_decap_compress_msg_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_decap_compress_msg_eventually_left_p);


property ctrl_mlkem_encap_decompress_t0_start_eventually_left_p;
  mlkem_encap_decompress_t0_start
|->
  s_eventually(!mlkem_encap_decompress_t0_start);
endproperty
ctrl_mlkem_encap_decompress_t0_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_t0_start_eventually_left_p);


property ctrl_mlkem_encap_decompress_t0_eventually_left_p;
  mlkem_encap_decompress_t0
|->
  s_eventually(!mlkem_encap_decompress_t0);
endproperty
ctrl_mlkem_encap_decompress_t0_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_t0_eventually_left_p);


property ctrl_mlkem_encap_compress_first_start_eventually_left_p;
  mlkem_encap_compress_first_start
|->
  s_eventually(!mlkem_encap_compress_first_start);
endproperty
ctrl_mlkem_encap_compress_first_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_first_start_eventually_left_p);


property ctrl_mlkem_encap_compress_first_eventually_left_p;
  mlkem_encap_compress_first
|->
  s_eventually(!mlkem_encap_compress_first);
endproperty
ctrl_mlkem_encap_compress_first_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_first_eventually_left_p);


property ctrl_mlkem_encap_SHA256_START_eventually_left_p;
  mlkem_encap_SHA256_START
|->
  s_eventually(!mlkem_encap_SHA256_START);
endproperty
ctrl_mlkem_encap_SHA256_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_SHA256_START_eventually_left_p);


property ctrl_mlkem_encap_write_ek_START_eventually_left_p;
  mlkem_encap_write_ek_START
|->
  s_eventually(!mlkem_encap_write_ek_START);
endproperty
ctrl_mlkem_encap_write_ek_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_START_eventually_left_p);


property ctrl_mlkem_encap_write_ek_init_eventually_left_p;
  mlkem_encap_write_ek_init
|->
  s_eventually(!mlkem_encap_write_ek_init);
endproperty
ctrl_mlkem_encap_write_ek_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_init_eventually_left_p);


property ctrl_mlkem_encap_write_ek_eventually_left_p;
  mlkem_encap_write_ek
|->
  s_eventually(!mlkem_encap_write_ek);
endproperty
ctrl_mlkem_encap_write_ek_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_eventually_left_p);


property ctrl_mlkem_encap_write_ek_msg_done_eventually_left_p;
  mlkem_encap_write_ek_msg_done
|->
  s_eventually(!mlkem_encap_write_ek_msg_done);
endproperty
ctrl_mlkem_encap_write_ek_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ek_msg_done_eventually_left_p);


property ctrl_mlkem_encap_ek_sampling_start_eventually_left_p;
  mlkem_encap_ek_sampling_start
|->
  s_eventually(!mlkem_encap_ek_sampling_start);
endproperty
ctrl_mlkem_encap_ek_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_start_eventually_left_p);


property ctrl_mlkem_encap_ek_sampling_eventually_left_p;
  mlkem_encap_ek_sampling
|->
  s_eventually(!mlkem_encap_ek_sampling);
endproperty
ctrl_mlkem_encap_ek_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ek_sampling_eventually_left_p);


property ctrl_mlkem_encap_ld_SHA512_START_eventually_left_p;
  mlkem_encap_ld_SHA512_START
|->
  s_eventually(!mlkem_encap_ld_SHA512_START);
endproperty
ctrl_mlkem_encap_ld_SHA512_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ld_SHA512_START_eventually_left_p);


property ctrl_mlkem_encap_write_msg_START_eventually_left_p;
  mlkem_encap_write_msg_START
|->
  s_eventually(!mlkem_encap_write_msg_START);
endproperty
ctrl_mlkem_encap_write_msg_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_START_eventually_left_p);


property ctrl_mlkem_encap_write_msg_init_eventually_left_p;
  mlkem_encap_write_msg_init
|->
  s_eventually(!mlkem_encap_write_msg_init);
endproperty
ctrl_mlkem_encap_write_msg_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_init_eventually_left_p);


property ctrl_mlkem_encap_write_msg_eventually_left_p;
  mlkem_encap_write_msg
|->
  s_eventually(!mlkem_encap_write_msg);
endproperty
ctrl_mlkem_encap_write_msg_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_eventually_left_p);


property ctrl_mlkem_encap_write_msg_done_eventually_left_p;
  mlkem_encap_write_msg_done
|->
  s_eventually(!mlkem_encap_write_msg_done);
endproperty
ctrl_mlkem_encap_write_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_done_eventually_left_p);


property ctrl_mlkem_encap_write_msg_wait_eventually_left_p;
  mlkem_encap_write_msg_wait
|->
  s_eventually(!mlkem_encap_write_msg_wait);
endproperty
ctrl_mlkem_encap_write_msg_wait_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_wait_eventually_left_p);


property ctrl_mlkem_encap_write_tr_msg_init_eventually_left_p;
  mlkem_encap_write_tr_msg_init
|->
  s_eventually(!mlkem_encap_write_tr_msg_init);
endproperty
ctrl_mlkem_encap_write_tr_msg_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_init_eventually_left_p);


property ctrl_mlkem_encap_write_tr_msg_eventually_left_p;
  mlkem_encap_write_tr_msg
|->
  s_eventually(!mlkem_encap_write_tr_msg);
endproperty
ctrl_mlkem_encap_write_tr_msg_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_eventually_left_p);


property ctrl_mlkem_encap_write_tr_msg_done_eventually_left_p;
  mlkem_encap_write_tr_msg_done
|->
  s_eventually(!mlkem_encap_write_tr_msg_done);
endproperty
ctrl_mlkem_encap_write_tr_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_tr_msg_done_eventually_left_p);


property ctrl_mlkem_encap_sha512_eventually_left_p;
  mlkem_encap_sha512
|->
  s_eventually(!mlkem_encap_sha512);
endproperty
ctrl_mlkem_encap_sha512_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_eventually_left_p);


property ctrl_mlkem_encap_sha512_done_eventually_left_p;
  mlkem_encap_sha512_done
|->
  s_eventually(!mlkem_encap_sha512_done);
endproperty
ctrl_mlkem_encap_sha512_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_sha512_done_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_SHA3_START_eventually_left_p;
  mlkem_encap_y_e1_e2_SHA3_START
|->
  s_eventually(!mlkem_encap_y_e1_e2_SHA3_START);
endproperty
ctrl_mlkem_encap_y_e1_e2_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_SHA3_START_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_msg_start_eventually_left_p;
  mlkem_encap_y_e1_e2_msg_start
|->
  s_eventually(!mlkem_encap_y_e1_e2_msg_start);
endproperty
ctrl_mlkem_encap_y_e1_e2_msg_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_msg_start_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_write_msg_init_eventually_left_p;
  mlkem_encap_y_e1_e2_write_msg_init
|->
  s_eventually(!mlkem_encap_y_e1_e2_write_msg_init);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_msg_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_msg_init_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_write_eventually_left_p;
  mlkem_encap_y_e1_e2_write
|->
  s_eventually(!mlkem_encap_y_e1_e2_write);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_write_immediate_eventually_left_p;
  mlkem_encap_y_e1_e2_write_immediate
|->
  s_eventually(!mlkem_encap_y_e1_e2_write_immediate);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_immediate_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_write_msg_done_eventually_left_p;
  mlkem_encap_y_e1_e2_write_msg_done
|->
  s_eventually(!mlkem_encap_y_e1_e2_write_msg_done);
endproperty
ctrl_mlkem_encap_y_e1_e2_write_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_write_msg_done_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_eventually_left_p;
  mlkem_encap_y_e1_e2_sha_sampling_start
|->
  s_eventually(!mlkem_encap_y_e1_e2_sha_sampling_start);
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_start_eventually_left_p);


property ctrl_mlkem_encap_y_e1_e2_sha_sampling_eventually_left_p;
  mlkem_encap_y_e1_e2_sha_sampling
|->
  s_eventually(!mlkem_encap_y_e1_e2_sha_sampling);
endproperty
ctrl_mlkem_encap_y_e1_e2_sha_sampling_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_y_e1_e2_sha_sampling_eventually_left_p);


property ctrl_mlkem_encap_ntt_y_idle_eventually_left_p;
  mlkem_encap_ntt_y_idle
|->
  s_eventually(!mlkem_encap_ntt_y_idle);
endproperty
ctrl_mlkem_encap_ntt_y_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_idle_eventually_left_p);


property ctrl_mlkem_encap_ntt_y_start_eventually_left_p;
  mlkem_encap_ntt_y_start
|->
  s_eventually(!mlkem_encap_ntt_y_start);
endproperty
ctrl_mlkem_encap_ntt_y_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_start_eventually_left_p);


property ctrl_mlkem_encap_ntt_y_eventually_left_p;
  mlkem_encap_ntt_y
|->
  s_eventually(!mlkem_encap_ntt_y);
endproperty
ctrl_mlkem_encap_ntt_y_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ntt_y_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_rho_SHA3_START_eventually_left_p;
  mlkem_encap_pwm_write_rho_SHA3_START
|->
  s_eventually(!mlkem_encap_pwm_write_rho_SHA3_START);
endproperty
ctrl_mlkem_encap_pwm_write_rho_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_SHA3_START_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_rho_start_eventually_left_p;
  mlkem_encap_pwm_write_rho_start
|->
  s_eventually(!mlkem_encap_pwm_write_rho_start);
endproperty
ctrl_mlkem_encap_pwm_write_rho_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_rho_init_eventually_left_p;
  mlkem_encap_pwm_write_rho_init
|->
  s_eventually(!mlkem_encap_pwm_write_rho_init);
endproperty
ctrl_mlkem_encap_pwm_write_rho_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_init_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_rho_eventually_left_p;
  mlkem_encap_pwm_write_rho
|->
  s_eventually(!mlkem_encap_pwm_write_rho);
endproperty
ctrl_mlkem_encap_pwm_write_rho_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_rho_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_immediate_eventually_left_p;
  mlkem_encap_pwm_write_immediate
|->
  s_eventually(!mlkem_encap_pwm_write_immediate);
endproperty
ctrl_mlkem_encap_pwm_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_eventually_left_p);


property ctrl_mlkem_encap_pwm_write_immediate_msg_done_eventually_left_p;
  mlkem_encap_pwm_write_immediate_msg_done
|->
  s_eventually(!mlkem_encap_pwm_write_immediate_msg_done);
endproperty
ctrl_mlkem_encap_pwm_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_write_immediate_msg_done_eventually_left_p);


property ctrl_mlkem_encap_pwm_rejection_sampling_start_eventually_left_p;
  mlkem_encap_pwm_rejection_sampling_start
|->
  s_eventually(!mlkem_encap_pwm_rejection_sampling_start);
endproperty
ctrl_mlkem_encap_pwm_rejection_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_rejection_sampling_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_ntt_start_eventually_left_p;
  mlkem_encap_pwm_ntt_start
|->
  s_eventually(!mlkem_encap_pwm_ntt_start);
endproperty
ctrl_mlkem_encap_pwm_ntt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ntt_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_eventually_left_p;
  mlkem_encap_pwm
|->
  s_eventually(!mlkem_encap_pwm);
endproperty
ctrl_mlkem_encap_pwm_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_eventually_left_p;
  mlkem_encap_pwm_a_write_rho_SHA3_START
|->
  s_eventually(!mlkem_encap_pwm_a_write_rho_SHA3_START);
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_SHA3_START_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_rho_start_eventually_left_p;
  mlkem_encap_pwm_a_write_rho_start
|->
  s_eventually(!mlkem_encap_pwm_a_write_rho_start);
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_rho_init_eventually_left_p;
  mlkem_encap_pwm_a_write_rho_init
|->
  s_eventually(!mlkem_encap_pwm_a_write_rho_init);
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_init_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_rho_eventually_left_p;
  mlkem_encap_pwm_a_write_rho
|->
  s_eventually(!mlkem_encap_pwm_a_write_rho);
endproperty
ctrl_mlkem_encap_pwm_a_write_rho_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_rho_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_eventually_left_p;
  mlkem_encap_pwm_a_write_immediate
|->
  s_eventually(!mlkem_encap_pwm_a_write_immediate);
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_eventually_left_p;
  mlkem_encap_pwm_a_write_immediate_msg_done
|->
  s_eventually(!mlkem_encap_pwm_a_write_immediate_msg_done);
endproperty
ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_write_immediate_msg_done_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_rejection_sampling_start_eventually_left_p;
  mlkem_encap_pwm_a_rejection_sampling_start
|->
  s_eventually(!mlkem_encap_pwm_a_rejection_sampling_start);
endproperty
ctrl_mlkem_encap_pwm_a_rejection_sampling_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_rejection_sampling_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_ntt_start_eventually_left_p;
  mlkem_encap_pwm_a_ntt_start
|->
  s_eventually(!mlkem_encap_pwm_a_ntt_start);
endproperty
ctrl_mlkem_encap_pwm_a_ntt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_ntt_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_a_eventually_left_p;
  mlkem_encap_pwm_a
|->
  s_eventually(!mlkem_encap_pwm_a);
endproperty
ctrl_mlkem_encap_pwm_a_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_a_eventually_left_p);


property ctrl_mlkem_encap_intt_idle_eventually_left_p;
  mlkem_encap_intt_idle
|->
  s_eventually(!mlkem_encap_intt_idle);
endproperty
ctrl_mlkem_encap_intt_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_idle_eventually_left_p);


property ctrl_mlkem_encap_intt_start_eventually_left_p;
  mlkem_encap_intt_start
|->
  s_eventually(!mlkem_encap_intt_start);
endproperty
ctrl_mlkem_encap_intt_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_start_eventually_left_p);


property ctrl_mlkem_encap_intt_eventually_left_p;
  mlkem_encap_intt
|->
  s_eventually(!mlkem_encap_intt);
endproperty
ctrl_mlkem_encap_intt_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_eventually_left_p);


property ctrl_mlkem_encap_pwa_idle_eventually_left_p;
  mlkem_encap_pwa_idle
|->
  s_eventually(!mlkem_encap_pwa_idle);
endproperty
ctrl_mlkem_encap_pwa_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_idle_eventually_left_p);


property ctrl_mlkem_encap_pwa_start_eventually_left_p;
  mlkem_encap_pwa_start
|->
  s_eventually(!mlkem_encap_pwa_start);
endproperty
ctrl_mlkem_encap_pwa_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_start_eventually_left_p);


property ctrl_mlkem_encap_pwa_eventually_left_p;
  mlkem_encap_pwa
|->
  s_eventually(!mlkem_encap_pwa);
endproperty
ctrl_mlkem_encap_pwa_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_eventually_left_p);


property ctrl_mlkem_encap_pwm_ty_idle_eventually_left_p;
  mlkem_encap_pwm_ty_idle
|->
  s_eventually(!mlkem_encap_pwm_ty_idle);
endproperty
ctrl_mlkem_encap_pwm_ty_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_idle_eventually_left_p);


property ctrl_mlkem_encap_pwm_ty_start_eventually_left_p;
  mlkem_encap_pwm_ty_start
|->
  s_eventually(!mlkem_encap_pwm_ty_start);
endproperty
ctrl_mlkem_encap_pwm_ty_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_start_eventually_left_p);


property ctrl_mlkem_encap_pwm_ty_eventually_left_p;
  mlkem_encap_pwm_ty
|->
  s_eventually(!mlkem_encap_pwm_ty);
endproperty
ctrl_mlkem_encap_pwm_ty_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwm_ty_eventually_left_p);


property ctrl_mlkem_encap_pwma_ty_idle_eventually_left_p;
  mlkem_encap_pwma_ty_idle
|->
  s_eventually(!mlkem_encap_pwma_ty_idle);
endproperty
ctrl_mlkem_encap_pwma_ty_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_idle_eventually_left_p);


property ctrl_mlkem_encap_pwma_ty_start_eventually_left_p;
  mlkem_encap_pwma_ty_start
|->
  s_eventually(!mlkem_encap_pwma_ty_start);
endproperty
ctrl_mlkem_encap_pwma_ty_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_start_eventually_left_p);


property ctrl_mlkem_encap_pwma_ty_eventually_left_p;
  mlkem_encap_pwma_ty
|->
  s_eventually(!mlkem_encap_pwma_ty);
endproperty
ctrl_mlkem_encap_pwma_ty_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwma_ty_eventually_left_p);


property ctrl_mlkem_encap_intt_v_idle_eventually_left_p;
  mlkem_encap_intt_v_idle
|->
  s_eventually(!mlkem_encap_intt_v_idle);
endproperty
ctrl_mlkem_encap_intt_v_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_idle_eventually_left_p);


property ctrl_mlkem_encap_intt_v_start_eventually_left_p;
  mlkem_encap_intt_v_start
|->
  s_eventually(!mlkem_encap_intt_v_start);
endproperty
ctrl_mlkem_encap_intt_v_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_start_eventually_left_p);


property ctrl_mlkem_encap_intt_v_eventually_left_p;
  mlkem_encap_intt_v
|->
  s_eventually(!mlkem_encap_intt_v);
endproperty
ctrl_mlkem_encap_intt_v_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_intt_v_eventually_left_p);


property ctrl_mlkem_encap_decompress_mu_idle_eventually_left_p;
  mlkem_encap_decompress_mu_idle
|->
  s_eventually(!mlkem_encap_decompress_mu_idle);
endproperty
ctrl_mlkem_encap_decompress_mu_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_idle_eventually_left_p);


property ctrl_mlkem_encap_decompress_mu_start_eventually_left_p;
  mlkem_encap_decompress_mu_start
|->
  s_eventually(!mlkem_encap_decompress_mu_start);
endproperty
ctrl_mlkem_encap_decompress_mu_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_start_eventually_left_p);


property ctrl_mlkem_encap_decompress_mu_eventually_left_p;
  mlkem_encap_decompress_mu
|->
  s_eventually(!mlkem_encap_decompress_mu);
endproperty
ctrl_mlkem_encap_decompress_mu_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_decompress_mu_eventually_left_p);


property ctrl_mlkem_encap_pwa_e2_idle_eventually_left_p;
  mlkem_encap_pwa_e2_idle
|->
  s_eventually(!mlkem_encap_pwa_e2_idle);
endproperty
ctrl_mlkem_encap_pwa_e2_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_idle_eventually_left_p);


property ctrl_mlkem_encap_pwa_e2_start_eventually_left_p;
  mlkem_encap_pwa_e2_start
|->
  s_eventually(!mlkem_encap_pwa_e2_start);
endproperty
ctrl_mlkem_encap_pwa_e2_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_start_eventually_left_p);


property ctrl_mlkem_encap_pwa_e2_eventually_left_p;
  mlkem_encap_pwa_e2
|->
  s_eventually(!mlkem_encap_pwa_e2);
endproperty
ctrl_mlkem_encap_pwa_e2_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_e2_eventually_left_p);


property ctrl_mlkem_encap_pwa_v_idle_eventually_left_p;
  mlkem_encap_pwa_v_idle
|->
  s_eventually(!mlkem_encap_pwa_v_idle);
endproperty
ctrl_mlkem_encap_pwa_v_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_idle_eventually_left_p);


property ctrl_mlkem_encap_pwa_v_start_eventually_left_p;
  mlkem_encap_pwa_v_start
|->
  s_eventually(!mlkem_encap_pwa_v_start);
endproperty
ctrl_mlkem_encap_pwa_v_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_start_eventually_left_p);


property ctrl_mlkem_encap_pwa_v_eventually_left_p;
  mlkem_encap_pwa_v
|->
  s_eventually(!mlkem_encap_pwa_v);
endproperty
ctrl_mlkem_encap_pwa_v_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_pwa_v_eventually_left_p);


property ctrl_mlkem_encap_compress_c1_idle_eventually_left_p;
  mlkem_encap_compress_c1_idle
|->
  s_eventually(!mlkem_encap_compress_c1_idle);
endproperty
ctrl_mlkem_encap_compress_c1_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_idle_eventually_left_p);


property ctrl_mlkem_encap_compress_c1_start_eventually_left_p;
  mlkem_encap_compress_c1_start
|->
  s_eventually(!mlkem_encap_compress_c1_start);
endproperty
ctrl_mlkem_encap_compress_c1_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_start_eventually_left_p);


property ctrl_mlkem_encap_compress_c1_eventually_left_p;
  mlkem_encap_compress_c1
|->
  s_eventually(!mlkem_encap_compress_c1);
endproperty
ctrl_mlkem_encap_compress_c1_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c1_eventually_left_p);


property ctrl_mlkem_encap_compress_c2_idle_eventually_left_p;
  mlkem_encap_compress_c2_idle
|->
  s_eventually(!mlkem_encap_compress_c2_idle);
endproperty
ctrl_mlkem_encap_compress_c2_idle_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_idle_eventually_left_p);


property ctrl_mlkem_encap_compress_c2_start_eventually_left_p;
  mlkem_encap_compress_c2_start
|->
  s_eventually(!mlkem_encap_compress_c2_start);
endproperty
ctrl_mlkem_encap_compress_c2_start_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_start_eventually_left_p);


property ctrl_mlkem_encap_compress_c2_eventually_left_p;
  mlkem_encap_compress_c2
|->
  s_eventually(!mlkem_encap_compress_c2);
endproperty
ctrl_mlkem_encap_compress_c2_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_compress_c2_eventually_left_p);


property ctrl_mlkem_encap_end_eventually_left_p;
  mlkem_encap_end
|->
  s_eventually(!mlkem_encap_end);
endproperty
ctrl_mlkem_encap_end_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_end_eventually_left_p);


property ctrl_mlkem_encap_ld_SHAKE256_START_eventually_left_p;
  mlkem_encap_ld_SHAKE256_START
|->
  s_eventually(!mlkem_encap_ld_SHAKE256_START);
endproperty
ctrl_mlkem_encap_ld_SHAKE256_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ld_SHAKE256_START_eventually_left_p);


property ctrl_mlkem_encap_write_msg_256_START_eventually_left_p;
  mlkem_encap_write_msg_256_START
|->
  s_eventually(!mlkem_encap_write_msg_256_START);
endproperty
ctrl_mlkem_encap_write_msg_256_START_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_START_eventually_left_p);


property ctrl_mlkem_encap_write_msg_256_init_eventually_left_p;
  mlkem_encap_write_msg_256_init
|->
  s_eventually(!mlkem_encap_write_msg_256_init);
endproperty
ctrl_mlkem_encap_write_msg_256_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_init_eventually_left_p);


property ctrl_mlkem_encap_write_msg_256_eventually_left_p;
  mlkem_encap_write_msg_256
|->
  s_eventually(!mlkem_encap_write_msg_256);
endproperty
ctrl_mlkem_encap_write_msg_256_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_eventually_left_p);


property ctrl_mlkem_encap_write_msg_256_done_eventually_left_p;
  mlkem_encap_write_msg_256_done
|->
  s_eventually(!mlkem_encap_write_msg_256_done);
endproperty
ctrl_mlkem_encap_write_msg_256_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_done_eventually_left_p);


property ctrl_mlkem_encap_write_msg_256_wait_eventually_left_p;
  mlkem_encap_write_msg_256_wait
|->
  s_eventually(!mlkem_encap_write_msg_256_wait);
endproperty
ctrl_mlkem_encap_write_msg_256_wait_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_msg_256_wait_eventually_left_p);


property ctrl_mlkem_encap_write_ct_msg_256_init_eventually_left_p;
  mlkem_encap_write_ct_msg_256_init
|->
  s_eventually(!mlkem_encap_write_ct_msg_256_init);
endproperty
ctrl_mlkem_encap_write_ct_msg_256_init_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_init_eventually_left_p);


property ctrl_mlkem_encap_write_ct_msg_256_eventually_left_p;
  mlkem_encap_write_ct_msg_256
|->
  s_eventually(!mlkem_encap_write_ct_msg_256);
endproperty
ctrl_mlkem_encap_write_ct_msg_256_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_256_eventually_left_p);


property ctrl_mlkem_encap_write_ct_msg_done_eventually_left_p;
  mlkem_encap_write_ct_msg_done
|->
  s_eventually(!mlkem_encap_write_ct_msg_done);
endproperty
ctrl_mlkem_encap_write_ct_msg_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_write_ct_msg_done_eventually_left_p);


property ctrl_mlkem_encap_ct_shake256_eventually_left_p;
  mlkem_encap_ct_shake256
|->
  s_eventually(!mlkem_encap_ct_shake256);
endproperty
ctrl_mlkem_encap_ct_shake256_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ct_shake256_eventually_left_p);


property ctrl_mlkem_encap_ct_shake256_done_eventually_left_p;
  mlkem_encap_ct_shake256_done
|->
  s_eventually(!mlkem_encap_ct_shake256_done);
endproperty
ctrl_mlkem_encap_ct_shake256_done_eventually_left_a: assert property (disable iff(!abr_ctrl.rst_b || abr_ctrl.zeroize || abr_ctrl.error_flag_reg) ctrl_mlkem_encap_ct_shake256_done_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  ctrl_consistency_onehot0_state: assert property($onehot0({ idle, mlkem_Keygen_pwa, mlkem_Keygen_pwa_idle, mlkem_Keygen_pwa_start, mlkem_decap_SHA256_START, mlkem_decap_compress_msg, mlkem_decap_compress_msg_idle, mlkem_decap_compress_msg_start, mlkem_decap_decompress_s0, mlkem_decap_decompress_s0_idle, mlkem_decap_decompress_s0_start, mlkem_decap_decompress_u0, mlkem_decap_decompress_u0_idle, mlkem_decap_decompress_u0_start, mlkem_decap_decompress_v, mlkem_decap_decompress_v_idle, mlkem_decap_decompress_v_start, mlkem_decap_ek_sampling, mlkem_decap_ek_sampling_start, mlkem_decap_intt_su, mlkem_decap_intt_su_idle, mlkem_decap_intt_su_start, mlkem_decap_ntt, mlkem_decap_ntt_idle, mlkem_decap_ntt_start, mlkem_decap_pwm_su, mlkem_decap_pwm_su_idle, mlkem_decap_pwm_su_start, mlkem_decap_pwma_su, mlkem_decap_pwma_su_idle, mlkem_decap_pwma_su_start, mlkem_decap_pws_su, mlkem_decap_pws_su_idle, mlkem_decap_pws_su_start, mlkem_decap_write_ek, mlkem_decap_write_ek_START, mlkem_decap_write_ek_msg_done, mlkem_encap_SHA256_START, mlkem_encap_compress_c1, mlkem_encap_compress_c1_idle, mlkem_encap_compress_c1_start, mlkem_encap_compress_c2, mlkem_encap_compress_c2_idle, mlkem_encap_compress_c2_start, mlkem_encap_compress_first, mlkem_encap_compress_first_start, mlkem_encap_ct_shake256, mlkem_encap_ct_shake256_done, mlkem_encap_decompress_mu, mlkem_encap_decompress_mu_idle, mlkem_encap_decompress_mu_start, mlkem_encap_decompress_t0, mlkem_encap_decompress_t0_start, mlkem_encap_ek_sampling, mlkem_encap_ek_sampling_start, mlkem_encap_end, mlkem_encap_intt, mlkem_encap_intt_idle, mlkem_encap_intt_start, mlkem_encap_intt_v, mlkem_encap_intt_v_idle, mlkem_encap_intt_v_start, mlkem_encap_ld_SHA512_START, mlkem_encap_ld_SHAKE256_START, mlkem_encap_ntt_y, mlkem_encap_ntt_y_idle, mlkem_encap_ntt_y_start, mlkem_encap_pwa, mlkem_encap_pwa_e2, mlkem_encap_pwa_e2_idle, mlkem_encap_pwa_e2_start, mlkem_encap_pwa_idle, mlkem_encap_pwa_start, mlkem_encap_pwa_v, mlkem_encap_pwa_v_idle, mlkem_encap_pwa_v_start, mlkem_encap_pwm, mlkem_encap_pwm_a, mlkem_encap_pwm_a_rejection_sampling_start, mlkem_encap_pwm_a_write_immediate, mlkem_encap_pwm_a_write_immediate_msg_done, mlkem_encap_pwm_a_write_rho, mlkem_encap_pwm_a_write_rho_SHA3_START, mlkem_encap_pwm_a_write_rho_start, mlkem_encap_pwm_rejection_sampling_start, mlkem_encap_pwm_ty, mlkem_encap_pwm_ty_idle, mlkem_encap_pwm_ty_start, mlkem_encap_pwm_write_immediate, mlkem_encap_pwm_write_immediate_msg_done, mlkem_encap_pwm_write_rho, mlkem_encap_pwm_write_rho_SHA3_START, mlkem_encap_pwm_write_rho_start, mlkem_encap_pwma_ty, mlkem_encap_pwma_ty_idle, mlkem_encap_pwma_ty_start, mlkem_encap_sha512, mlkem_encap_sha512_done, mlkem_encap_write_ct_msg_256, mlkem_encap_write_ct_msg_done, mlkem_encap_write_ek, mlkem_encap_write_ek_START, mlkem_encap_write_ek_msg_done, mlkem_encap_write_msg, mlkem_encap_write_msg_256, mlkem_encap_write_msg_256_START, mlkem_encap_write_msg_256_done, mlkem_encap_write_msg_256_wait, mlkem_encap_write_msg_START, mlkem_encap_write_msg_done, mlkem_encap_write_msg_wait, mlkem_encap_write_tr_msg, mlkem_encap_write_tr_msg_done, mlkem_encap_y_e1_e2_SHA3_START, mlkem_encap_y_e1_e2_msg_start, mlkem_encap_y_e1_e2_sha_sampling, mlkem_encap_y_e1_e2_sha_sampling_start, mlkem_encap_y_e1_e2_write, mlkem_encap_y_e1_e2_write_immediate, mlkem_encap_y_e1_e2_write_msg_done, mlkem_keygen_SHA256_START, mlkem_keygen_cbd_SHA3_START, mlkem_keygen_cbd_msg_start, mlkem_keygen_cbd_sampling, mlkem_keygen_cbd_sampling_start, mlkem_keygen_cbd_write_immediate, mlkem_keygen_cbd_write_msg, mlkem_keygen_cbd_write_msg_done, mlkem_keygen_compress_dk, mlkem_keygen_compress_dk_idle, mlkem_keygen_compress_dk_start, mlkem_keygen_compress_ek, mlkem_keygen_compress_ek_idle, mlkem_keygen_compress_ek_start, mlkem_keygen_ek_sampling, mlkem_keygen_ek_sampling_start, mlkem_keygen_ntt, mlkem_keygen_ntt_idle, mlkem_keygen_ntt_start, mlkem_keygen_pwm, mlkem_keygen_pwm_a, mlkem_keygen_pwm_a_rejection_sampling_start, mlkem_keygen_pwm_a_write_immediate, mlkem_keygen_pwm_a_write_immediate_msg_done, mlkem_keygen_pwm_a_write_rho, mlkem_keygen_pwm_a_write_rho_SHA3_START, mlkem_keygen_pwm_a_write_rho_start, mlkem_keygen_pwm_rejection_sampling_start, mlkem_keygen_pwm_write_immediate, mlkem_keygen_pwm_write_immediate_msg_done, mlkem_keygen_pwm_write_rho, mlkem_keygen_pwm_write_rho_SHA3_START, mlkem_keygen_pwm_write_rho_start, mlkem_keygen_rnd_seed_SHA3_START, mlkem_keygen_rnd_seed_start, mlkem_keygen_seed_sha_sampling, mlkem_keygen_seed_sha_sampling_start, mlkem_keygen_write_ek, mlkem_keygen_write_ek_START, mlkem_keygen_write_ek_msg_done, mlkem_keygen_write_seed, mlkem_keygen_write_seed_immediate, mlkem_keygen_write_seed_msg_done }));
end


endmodule
