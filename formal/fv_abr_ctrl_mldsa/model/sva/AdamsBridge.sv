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
// | Created on 07.03.2025 at 13:41                    |
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


module fv_mldsa_ctrl_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input st_FromApiType api_in,

  input logic api_out_vld,
  input st_ToApiType api_out,

  input logic unsigned [14:0] lfsr_seed_reg_id_in,

  input logic unsigned [14:0] rho_k_reg_id_in,

  input logic unsigned [14:0] tr_reg_id_in,

  input logic unsigned [14:0] mu_reg_id_in,

  input logic unsigned [14:0] rho_prime_reg_id_in,

  input logic unsigned [14:0] sig_c_reg_id_in,

  input logic unsigned [14:0] verify_res_reg_id_in,

  input a_unsigned_15_7 s1_addrs_in,

  input a_unsigned_15_8 s2_addrs_in,

  input logic unsigned [14:0] temp_addr_in,

  input a_unsigned_15_7 s1_ntt_addrs_in,

  input logic unsigned [14:0] as_addr_in,

  input logic unsigned [14:0] rho_id_in,

  input logic unsigned [14:0] as_intt_addr_in,

  input a_unsigned_15_8 t_addrs_in,

  input a_unsigned_15_7 y_addrs_in,

  input a_unsigned_15_7 y_ntt_addrs_in,

  input logic unsigned [14:0] ay0_addr_in,

  input a_unsigned_15_8 w0_addrs_in,

  input a_unsigned_15_7 z_addrs_in,

  input logic unsigned [14:0] c_addr_in,

  input logic unsigned [14:0] c_ntt_addr_in,

  input a_unsigned_15_7 z_ntt_addrs_in,

  input logic unsigned [14:0] az_addr_in,

  input logic unsigned [14:0] ct_addr_in,

  input logic unsigned [14:0] hint_r_addr_in,

  input logic y_valid_in,

  input logic set_y_valid_out,

  input logic w0_valid_in,

  input logic set_w0_valid_out,

  input logic c_valid_in,

  input logic set_c_valid_out,

  input logic unsigned [511:0] entropy_in,

  input logic unsigned [63:0] counter_in,

  input a_unsigned_32_17 msg_prime_in,

  input logic to_keccak_vld,
  input logic unsigned [63:0] to_keccak,

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

  input logic to_power_2_round_vld,
  input logic to_power_2_round_rdy,
  input st_Power2RoundType to_power_2_round,

  input logic power_2_round_done_in,

  input logic to_sk_encode_vld,
  input logic to_sk_encode_rdy,
  input st_SkEncodeType to_sk_encode,

  input logic sk_encode_done_in,

  input logic to_decompose_vld,
  input logic to_decompose_rdy,
  input st_DecomposeType to_decompose,

  input logic decompose_done_in,

  input logic to_pk_decode_vld,
  input logic to_pk_decode_rdy,
  input st_PkDecodeType to_pk_decode,

  input logic pk_decode_done_in,

  input logic to_sig_decode_z_vld,
  input logic to_sig_decode_z_rdy,
  input st_SigDecodeType to_sig_decode_z,

  input logic sig_decode_z_done_in,

  input logic to_norm_check_vld,
  input logic to_norm_check_rdy,
  input st_NormCheckType to_norm_check,

  input logic norm_check_done_in,

  input logic to_sig_decode_h_vld,
  input logic to_sig_decode_h_rdy,
  input st_SigDecodeType to_sig_decode_h,

  input logic sig_decode_h_done_in,

  input logic to_use_hint_vld,
  input logic to_use_hint_rdy,
  input st_UseHintType to_use_hint,

  input logic use_hint_done_in,

  input logic from_ext_mu_mode_in,

  input logic from_keygen_jump_in,

  input logic enable_lfsr,

  input logic sig_vld_chk_done_in,

  input logic sha3_start_o,

  input logic msg_start_o,

  input logic unsigned [2:0] sampler_offset_f,

  input a_unsigned_32_10 pk_ram_data,

  input logic unsigned [511:0] from_ext_mu,

  // Registers
  input logic unsigned [14:0] as_addr,
  input logic unsigned [14:0] ay0_addr,
  input logic unsigned [14:0] az_addr,
  input logic unsigned [63:0] counter,
  input logic unsigned [63:0] counter_ForStmt_838_9,
  input logic unsigned [511:0] entropy,
  input logic unsigned [511:0] entropy_ForStmt_828_9,
  input st_FromApiType from_api,
  input logic jump_if_invalid,
  input logic unsigned [2:0] keygen_ntt_s1_idx,
  input logic unsigned [7:0] keygen_pwm_a_idx,
  input logic unsigned [7:0] keygen_t_idx,
  input a_unsigned_32_17 msg_prime,
  input a_unsigned_32_17 msg_prime_ForStmt_1178_9,
  input st_RegsType registers,
  input logic unsigned [15:0] rejbounded_counter,
  input logic unsigned [14:0] rho_id,
  input logic unsigned [14:0] rho_id_ForStmt_1272_11,
  input logic unsigned [14:0] rho_id_ForStmt_920_11,
  input a_unsigned_15_7 s1_ntt_addrs_ForStmt_513_11,
  input logic unsigned [7:0] sign_compute_w0_idx,
  input logic unsigned [7:0] sign_compute_w0_y_idx,
  input logic unsigned [7:0] sign_expand_mask_idx,
  input logic unsigned [7:0] sign_ntt_y_idx,
  input logic unsigned [15:0] sipo_chunk_idx,
  input st_ToApiType to_api,
  input logic unsigned [7:0] verify_compute_az_idx,
  input logic unsigned [7:0] verify_compute_w0_idx,
  input logic unsigned [7:0] verify_norm_check_idx,
  input logic unsigned [7:0] verify_ntt_t_idx,
  input logic unsigned [7:0] verify_ntt_z_idx,
  input logic unsigned [0:0] vld_lcl_w0,
  input a_unsigned_15_7 y_ntt_addrs_ForStmt_920_11,
  input a_unsigned_15_7 z_ntt_addrs_ForStmt_1272_11,

  // States
  input logic idle,
  input logic keygen_rnd_seed_SHA3_START,
  input logic keygen_rnd_seed_start,
  input logic keygen_write_entropy,
  input logic keygen_write_entropy_msg_done,
  input logic keygen_rnd_seed_wait,
  input logic keygen_write_counter,
  input logic keygen_write_counter_msg_done,
  input logic keygen_sample_rnd_seed_start,
  input logic keygen_sample_rnd_seed,
  input logic keygen_rnd_seed_lfsr,
  input logic keygen_rnd_seed_done,
  input logic keygen_expand_seed_SHA3_START,
  input logic keygen_expand_seed_start,
  input logic keygen_write_seed,
  input logic keygen_write_seed_immediate,
  input logic keygen_write_seed_msg_done,
  input logic keygen_expand_seed_sampling_start,
  input logic keygen_expand_seed_sampling,
  input logic keygen_write_rejbounded_input_s1_SHA3_START,
  input logic keygen_write_rejbounded_input_s1_start,
  input logic keygen_write_rejbounded_input_s1,
  input logic keygen_write_rejbounded_immediate_s1,
  input logic keygen_write_rejbounded_immediate_s1_msg_done,
  input logic keygen_rejbounded_s1_start,
  input logic keygen_rejbounded_s1,
  input logic keygen_write_rejbounded_input_s2_SHA3_START,
  input logic keygen_write_rejbounded_input_s2_start,
  input logic keygen_write_rejbounded_input_s2,
  input logic keygen_write_rejbounded_immediate_s2,
  input logic keygen_write_rejbounded_immediate_s2_msg_done,
  input logic keygen_rejbounded_s2_start,
  input logic keygen_rejbounded_s2,
  input logic Keygen_ntt_s1_idle,
  input logic keygen_ntt_s1_start,
  input logic keygen_ntt_s1,
  input logic keygen_pwm_a_write_rho_SHA3_START,
  input logic keygen_pwm_a_write_rho_start,
  input logic keygen_pwm_a_write_rho,
  input logic keygen_pwm_a_write_immediate,
  input logic keygen_pwm_a_write_immediate_msg_done,
  input logic keygen_pwm_a_rejection_sampling_start,
  input logic keygen_pwm_a_start,
  input logic keygen_pwm_a,
  input logic keygen_intt_a_idle,
  input logic keygen_intt_a_start,
  input logic keygen_intt_a,
  input logic keygen_compute_t_start,
  input logic keygen_compute_t,
  input logic keygen_power_2_round_start,
  input logic keygen_power_2_round,
  input logic keygen_compute_tr_write_pk_SHA3_START,
  input logic keygen_compute_tr_write_pk_start,
  input logic keygen_compute_tr_write_pk,
  input logic keygen_compute_tr_write_pk_msg_done,
  input logic keygen_compute_tr_sampling_start,
  input logic keygen_compute_tr_sampling,
  input logic keygen_sk_encode_start,
  input logic keygen_sk_encode,
  input logic keygen_jump_sign,
  input logic keygen_end_state,
  input logic sign_rnd_seed_SHA3_START,
  input logic sign_rnd_seed_start,
  input logic sign_write_entropy,
  input logic sign_write_entropy_msg_done,
  input logic sign_rnd_seed_wait,
  input logic sign_write_counter,
  input logic sign_write_counter_msg_done,
  input logic sign_sample_rnd_seed_start,
  input logic sign_sample_rnd_seed,
  input logic sign_rnd_seed_lfsr,
  input logic sign_compute_mu_idle,
  input logic sign_compute_mu_SHA3_START,
  input logic sign_compute_mu_start,
  input logic sign_compute_mu_write_tr,
  input logic sign_compute_mu_write_tr_msg_done,
  input logic sign_compute_mu_wait,
  input logic sign_compute_mu_write_msg_prime,
  input logic sign_compute_mu_write_msg_prime_msg_done,
  input logic sign_compute_mu_sampling_start,
  input logic sign_compute_mu_sampling,
  input logic sign_compute_rho_prime_SHA3_START,
  input logic sign_compute_rho_prime_start,
  input logic sign_compute_rho_prime_write_K,
  input logic sign_compute_rho_prime_write_K_msg_done,
  input logic sign_compute_rho_prime_wait_0,
  input logic sign_compute_rho_prime_write_sign_rnd,
  input logic sign_compute_rho_prime_write_sign_rnd_msg_done,
  input logic sign_compute_rho_prime_wait_1,
  input logic sign_compute_rho_prime_write_mu,
  input logic sign_compute_rho_prime_write_mu_msg_done,
  input logic sign_compute_rho_prime_sampling_start,
  input logic sign_compute_rho_prime_sampling,
  input logic sign_wait_for_y_and_w0_clear,
  input logic sign_compute_lfsr_seed_SHA3_START,
  input logic sign_compute_lfsr_seed_start,
  input logic sign_compute_lfsr_seed_write_entropy,
  input logic sign_compute_lfsr_seed_write_entropy_msg_done,
  input logic sign_compute_lfsr_seed_wait,
  input logic sign_compute_lfsr_seed_write_counter,
  input logic sign_compute_lfsr_seed_write_counter_msg_done,
  input logic sign_compute_lfsr_seed_sampling_start,
  input logic sign_compute_lfsr_seed_sampling,
  input logic sign_compute_lfsr_seed_lfsr,
  input logic sign_expand_mask_done,
  input logic sign_expand_mask_SHA3_START,
  input logic sign_expand_mask_start,
  input logic sign_expand_mask_write_rho_prime,
  input logic sign_expand_mask_write_kappa_immediate,
  input logic sign_expand_mask_write_kappa_immediate_msg_done,
  input logic sign_expand_mask_sampling_start,
  input logic sign_expand_mask_sampling,
  input logic sign_ntt_y_idle,
  input logic sign_ntt_y_start,
  input logic sign_ntt_y,
  input logic sign_wait_for_w0_clear,
  input logic sign_compute_w0_pwm_SHA3_START,
  input logic sign_compute_w0_pwm_start,
  input logic sign_compute_w0_pwm_write_rho,
  input logic sign_compute_w0_pwm_write_immediate,
  input logic sign_compute_w0_pwm_write_immediate_msg_done,
  input logic sign_compute_w0_pwm_sampling_start,
  input logic sign_compute_w0_pwm_samp_ntt,
  input logic sign_compute_w0_pwm,
  input logic sign_compute_w0_intt_idle,
  input logic sign_compute_w0_intt_start,
  input logic sign_compute_w0_intt,
  input logic sign_set_y_valid,
  input logic sign_load_mu_idle,
  input logic sign_load_mu_SHA3_START,
  input logic sign_load_mu_start,
  input logic sign_load_mu,
  input logic sign_load_mu_msg_done,
  input logic sign_load_mu_wait,
  input logic sign_decompose_w_start,
  input logic sign_decompose_w,
  input logic sign_set_w0_valid,
  input logic sign_wait_for_c_clear,
  input logic sign_compute_c_start,
  input logic sign_compute_c,
  input logic sign_sample_in_ball_SHA3_START,
  input logic sign_sample_in_ball_start,
  input logic sign_sample_in_ball_write_c,
  input logic sign_sample_in_ball_write_c_msg_done,
  input logic sign_sample_in_ball_sampling_start,
  input logic sign_sample_in_ball_sampling,
  input logic sign_set_c_valid,
  input logic sign_end_of_challenge,
  input logic sign_check_mode,
  input logic sign_end_state,
  input logic verify_pk_decode_start,
  input logic verify_pk_decode,
  input logic verify_sig_decode_z_start,
  input logic verify_sig_decode_z,
  input logic verify_norm_check_start,
  input logic verify_norm_check,
  input logic verify_compute_tr_SHA3_START,
  input logic verify_compute_tr_start,
  input logic verify_compute_tr_write_pk,
  input logic verify_compute_tr_write_pk_msg_done,
  input logic verify_compute_tr_sampling_start,
  input logic verify_compute_tr_sampling,
  input logic verify_check_mode,
  input logic verify_compute_mu_SHA3_START,
  input logic verify_compute_mu_start,
  input logic verify_compute_mu_write_tr,
  input logic verify_compute_mu_write_tr_msg_done,
  input logic verify_compute_mu_wait,
  input logic verify_compute_mu_write_msg_prime,
  input logic verify_compute_mu_write_msg_prime_msg_done,
  input logic verify_compute_mu_sampling_start,
  input logic verify_compute_mu_sampling,
  input logic verify_sample_in_ball_SHA3_START,
  input logic verify_sample_in_ball_start,
  input logic verify_sample_in_ball_write_c,
  input logic verify_sample_in_ball_write_c_msg_done,
  input logic verify_sample_in_ball_sampling_start,
  input logic verify_sample_in_ball_sampling,
  input logic verify_ntt_c_start,
  input logic verify_ntt_c,
  input logic verify_ntt_t_start,
  input logic verify_ntt_t,
  input logic verify_ntt_z_start,
  input logic verify_ntt_z,
  input logic verify_compute_az_SHA3_START,
  input logic verify_compute_az_start,
  input logic verify_compute_az_write_rho,
  input logic verify_compute_az_write_immediate,
  input logic verify_compute_az_write_immediate_msg_done,
  input logic verify_compute_az_sampling_start,
  input logic verify_compute_az_pwm_start,
  input logic verify_compute_az_pwm,
  input logic verify_compute_w0_pwm_start,
  input logic verify_compute_w0_pwm,
  input logic verify_compute_w0_pws_start,
  input logic verify_compute_w0_pws,
  input logic verify_compute_w0_intt_idle,
  input logic verify_compute_w0_intt_start,
  input logic verify_compute_w0_intt,
  input logic verify_sig_decode_h_start,
  input logic verify_sig_decode_h,
  input logic verify_load_mu_SHA3_START,
  input logic verify_load_mu_start,
  input logic verify_load_mu,
  input logic verify_load_mu_msg_done,
  input logic verify_load_mu_wait,
  input logic verify_use_hint_start,
  input logic verify_use_hint,
  input logic verify_mu_sampling_start,
  input logic verify_mu_sampling,
  input logic verify_end_state
);


default clocking default_clk @(posedge clk); endclocking


st_FromApiType from_api_0_i;
assign from_api_0_i = '{
  instr: NoOp,
  seed: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0 },
  sign_rnd: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0 },
  tr: 512'd0,
  pk: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 0, 9: 0, 10: 0, 11: 0, 12: 0, 13: 0, 14: 0, 15: 0, 16: 0, 17: 0, 18: 0, 19: 0, 20: 0, 21: 0, 22: 0, 23: 0, 24: 0, 25: 0, 26: 0, 27: 0, 28: 0, 29: 0, 30: 0, 31: 0, 32: 0, 33: 0, 34: 0, 35: 0, 36: 0, 37: 0, 38: 0, 39: 0, 40: 0, 41: 0, 42: 0, 43: 0, 44: 0, 45: 0, 46: 0, 47: 0, 48: 0, 49: 0, 50: 0, 51: 0, 52: 0, 53: 0, 54: 0, 55: 0, 56: 0, 57: 0, 58: 0, 59: 0, 60: 0, 61: 0, 62: 0, 63: 0, 64: 0, 65: 0, 66: 0, 67: 0, 68: 0, 69: 0, 70: 0, 71: 0, 72: 0, 73: 0, 74: 0, 75: 0, 76: 0, 77: 0, 78: 0, 79: 0, 80: 0, 81: 0, 82: 0, 83: 0, 84: 0, 85: 0, 86: 0, 87: 0, 88: 0, 89: 0, 90: 0, 91: 0, 92: 0, 93: 0, 94: 0, 95: 0, 96: 0, 97: 0, 98: 0, 99: 0, 100: 0, 101: 0, 102: 0, 103: 0, 104: 0, 105: 0, 106: 0, 107: 0, 108: 0, 109: 0, 110: 0, 111: 0, 112: 0, 113: 0, 114: 0, 115: 0, 116: 0, 117: 0, 118: 0, 119: 0, 120: 0, 121: 0, 122: 0, 123: 0, 124: 0, 125: 0, 126: 0, 127: 0, 128: 0, 129: 0, 130: 0, 131: 0, 132: 0, 133: 0, 134: 0, 135: 0, 136: 0, 137: 0, 138: 0, 139: 0, 140: 0, 141: 0, 142: 0, 143: 0, 144: 0, 145: 0, 146: 0, 147: 0, 148: 0, 149: 0, 150: 0, 151: 0, 152: 0, 153: 0, 154: 0, 155: 0, 156: 0, 157: 0, 158: 0, 159: 0, 160: 0, 161: 0, 162: 0, 163: 0, 164: 0, 165: 0, 166: 0, 167: 0, 168: 0, 169: 0, 170: 0, 171: 0, 172: 0, 173: 0, 174: 0, 175: 0, 176: 0, 177: 0, 178: 0, 179: 0, 180: 0, 181: 0, 182: 0, 183: 0, 184: 0, 185: 0, 186: 0, 187: 0, 188: 0, 189: 0, 190: 0, 191: 0, 192: 0, 193: 0, 194: 0, 195: 0, 196: 0, 197: 0, 198: 0, 199: 0, 200: 0, 201: 0, 202: 0, 203: 0, 204: 0, 205: 0, 206: 0, 207: 0, 208: 0, 209: 0, 210: 0, 211: 0, 212: 0, 213: 0, 214: 0, 215: 0, 216: 0, 217: 0, 218: 0, 219: 0, 220: 0, 221: 0, 222: 0, 223: 0, 224: 0, 225: 0, 226: 0, 227: 0, 228: 0, 229: 0, 230: 0, 231: 0, 232: 0, 233: 0, 234: 0, 235: 0, 236: 0, 237: 0, 238: 0, 239: 0, 240: 0, 241: 0, 242: 0, 243: 0, 244: 0, 245: 0, 246: 0, 247: 0, 248: 0, 249: 0, 250: 0, 251: 0, 252: 0, 253: 0, 254: 0, 255: 0, 256: 0, 257: 0, 258: 0, 259: 0, 260: 0, 261: 0, 262: 0, 263: 0, 264: 0, 265: 0, 266: 0, 267: 0, 268: 0, 269: 0, 270: 0, 271: 0, 272: 0, 273: 0, 274: 0, 275: 0, 276: 0, 277: 0, 278: 0, 279: 0, 280: 0, 281: 0, 282: 0, 283: 0, 284: 0, 285: 0, 286: 0, 287: 0, 288: 0, 289: 0, 290: 0, 291: 0, 292: 0, 293: 0, 294: 0, 295: 0, 296: 0, 297: 0, 298: 0, 299: 0, 300: 0, 301: 0, 302: 0, 303: 0, 304: 0, 305: 0, 306: 0, 307: 0, 308: 0, 309: 0, 310: 0, 311: 0, 312: 0, 313: 0, 314: 0, 315: 0, 316: 0, 317: 0, 318: 0, 319: 0, 320: 0, 321: 0, 322: 0, 323: 0, 324: 0, 325: 0, 326: 0, 327: 0, 328: 0, 329: 0, 330: 0, 331: 0, 332: 0, 333: 0, 334: 0, 335: 0, 336: 0, 337: 0, 338: 0, 339: 0, 340: 0, 341: 0, 342: 0, 343: 0, 344: 0, 345: 0, 346: 0, 347: 0, 348: 0, 349: 0, 350: 0, 351: 0, 352: 0, 353: 0, 354: 0, 355: 0, 356: 0, 357: 0, 358: 0, 359: 0, 360: 0, 361: 0, 362: 0, 363: 0, 364: 0, 365: 0, 366: 0, 367: 0, 368: 0, 369: 0, 370: 0, 371: 0, 372: 0, 373: 0, 374: 0, 375: 0, 376: 0, 377: 0, 378: 0, 379: 0, 380: 0, 381: 0, 382: 0, 383: 0, 384: 0, 385: 0, 386: 0, 387: 0, 388: 0, 389: 0, 390: 0, 391: 0, 392: 0, 393: 0, 394: 0, 395: 0, 396: 0, 397: 0, 398: 0, 399: 0, 400: 0, 401: 0, 402: 0, 403: 0, 404: 0, 405: 0, 406: 0, 407: 0, 408: 0, 409: 0, 410: 0, 411: 0, 412: 0, 413: 0, 414: 0, 415: 0, 416: 0, 417: 0, 418: 0, 419: 0, 420: 0, 421: 0, 422: 0, 423: 0, 424: 0, 425: 0, 426: 0, 427: 0, 428: 0, 429: 0, 430: 0, 431: 0, 432: 0, 433: 0, 434: 0, 435: 0, 436: 0, 437: 0, 438: 0, 439: 0, 440: 0, 441: 0, 442: 0, 443: 0, 444: 0, 445: 0, 446: 0, 447: 0, 448: 0, 449: 0, 450: 0, 451: 0, 452: 0, 453: 0, 454: 0, 455: 0, 456: 0, 457: 0, 458: 0, 459: 0, 460: 0, 461: 0, 462: 0, 463: 0, 464: 0, 465: 0, 466: 0, 467: 0, 468: 0, 469: 0, 470: 0, 471: 0, 472: 0, 473: 0, 474: 0, 475: 0, 476: 0, 477: 0, 478: 0, 479: 0, 480: 0, 481: 0, 482: 0, 483: 0, 484: 0, 485: 0, 486: 0, 487: 0, 488: 0, 489: 0, 490: 0, 491: 0, 492: 0, 493: 0, 494: 0, 495: 0, 496: 0, 497: 0, 498: 0, 499: 0, 500: 0, 501: 0, 502: 0, 503: 0, 504: 0, 505: 0, 506: 0, 507: 0, 508: 0, 509: 0, 510: 0, 511: 0, 512: 0, 513: 0, 514: 0, 515: 0, 516: 0, 517: 0, 518: 0, 519: 0, 520: 0, 521: 0, 522: 0, 523: 0, 524: 0, 525: 0, 526: 0, 527: 0, 528: 0, 529: 0, 530: 0, 531: 0, 532: 0, 533: 0, 534: 0, 535: 0, 536: 0, 537: 0, 538: 0, 539: 0, 540: 0, 541: 0, 542: 0, 543: 0, 544: 0, 545: 0, 546: 0, 547: 0, 548: 0, 549: 0, 550: 0, 551: 0, 552: 0, 553: 0, 554: 0, 555: 0, 556: 0, 557: 0, 558: 0, 559: 0, 560: 0, 561: 0, 562: 0, 563: 0, 564: 0, 565: 0, 566: 0, 567: 0, 568: 0, 569: 0, 570: 0, 571: 0, 572: 0, 573: 0, 574: 0, 575: 0, 576: 0, 577: 0, 578: 0, 579: 0, 580: 0, 581: 0, 582: 0, 583: 0, 584: 0, 585: 0, 586: 0, 587: 0, 588: 0, 589: 0, 590: 0, 591: 0, 592: 0, 593: 0, 594: 0, 595: 0, 596: 0, 597: 0, 598: 0, 599: 0, 600: 0, 601: 0, 602: 0, 603: 0, 604: 0, 605: 0, 606: 0, 607: 0, 608: 0, 609: 0, 610: 0, 611: 0, 612: 0, 613: 0, 614: 0, 615: 0, 616: 0, 617: 0, 618: 0, 619: 0, 620: 0, 621: 0, 622: 0, 623: 0, 624: 0, 625: 0, 626: 0, 627: 0, 628: 0, 629: 0, 630: 0, 631: 0, 632: 0, 633: 0, 634: 0, 635: 0, 636: 0, 637: 0, 638: 0, 639: 0, 640: 0, 641: 0, 642: 0, 643: 0, 644: 0, 645: 0, 646: 0, 647: 0 },
  sk_in: 39168'd0
};

a_unsigned_32_17 msg_prime_0_i;
assign msg_prime_0_i = '{
  0: 0,
  1: 0,
  2: 0,
  3: 0,
  4: 0,
  5: 0,
  6: 0,
  7: 0,
  8: 0,
  9: 0,
  10: 0,
  11: 0,
  12: 0,
  13: 0,
  14: 0,
  15: 0,
  16: 0
};

st_RegsType registers_0_i;
assign registers_0_i = '{
  rho: 256'd0,
  rho_prime: 512'd0,
  K: 256'd0,
  mu: 512'd0,
  kappa: 16'd0,
  c: '{ 0: 0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0, 7: 0, 8: 0, 9: 0, 10: 0, 11: 0, 12: 0, 13: 0, 14: 0, 15: 0 }
};

a_unsigned_15_7 s1_addrs_0_i;
assign s1_addrs_0_i = '{
  0: 15'd0,
  1: 15'd0,
  2: 15'd0,
  3: 15'd0,
  4: 15'd0,
  5: 15'd0,
  6: 15'd0
};

st_ToApiType to_api_0_i;
assign to_api_0_i = '{
  tr: 512'd0,
  sk_out: 39168'd0
};

st_PkDecodeType to_pk_decode_0_i;
assign to_pk_decode_0_i = '{
  destination: t_addrs_in[64'd0]
};

logic unsigned [63:0] getChunk_0_i;
assign getChunk_0_i = getChunk(20736'(entropy), 16'(sipo_chunk_idx[2:0]));

logic unsigned [63:0] getChunk_1_i;
assign getChunk_1_i = getChunk(20736'(counter), 16'd0);

st_ToSamplerType to_sampler_0_i;
assign to_sampler_0_i = '{
  mode: Shake256,
  destination: lfsr_seed_reg_id_in
};

logic unsigned [63:0] func_concat_seed_0_i;
assign func_concat_seed_0_i = func_concat_seed(from_api.seed, 3'(sipo_chunk_idx[1:0]));

st_ToSamplerType to_sampler_1_i;
assign to_sampler_1_i = '{
  mode: Shake256,
  destination: rho_k_reg_id_in
};
st_ToSamplerType to_sampler_15_i;
assign to_sampler_15_i = '{
  mode: Shake256,
  destination: rho_prime_reg_id_in
};

st_RegsType registers_1_i;
assign registers_1_i = '{
  rho: (from_keccak_piso_vld_in ? from_keccak_piso[255:0] : registers.rho),
  rho_prime: (from_keccak_piso_vld_in ? from_keccak_piso[767:256] : registers.rho_prime),
  K: (from_keccak_piso_vld_in ? from_keccak_piso[1023:768] : registers.K),
  mu: registers.mu,
  kappa: registers.kappa,
  c: registers.c
};

logic unsigned [63:0] getChunk_2_i;
assign getChunk_2_i = getChunk(20736'(registers.rho_prime), 16'(sipo_chunk_idx[2:0]));

st_ToSamplerType to_sampler_2_i;
assign to_sampler_2_i = '{
  mode: RejBounded,
  destination: s1_addrs_in[rejbounded_counter]
};

st_ToSamplerType to_sampler_3_i;
assign to_sampler_3_i = '{
  mode: RejBounded,
  destination: s2_addrs_in[(({ 48'h0, rejbounded_counter} ) - 64'd7)]
};

st_NttType to_ntt_0_i;
assign to_ntt_0_i = '{
  mode: Ntt,
  operand1: s1_addrs_in[keygen_ntt_s1_idx],
  operand2: temp_addr_in,
  destination: s1_ntt_addrs_in[keygen_ntt_s1_idx]
};

logic unsigned [63:0] getChunk_3_i;
assign getChunk_3_i = getChunk(20736'(registers.rho), 16'(sipo_chunk_idx[1:0]));

st_ToSamplerType to_sampler_4_i;
assign to_sampler_4_i = '{
  mode: RejSampler,
  destination: as_addr_in
};

st_NttType to_ntt_1_i;
assign to_ntt_1_i = '{
  mode: ((({ 56'd0, keygen_pwm_a_idx} ) > 64'd0) ? PwmAccuSampler : PwmSampler),
  operand1: rho_id,
  operand2: s1_ntt_addrs_ForStmt_513_11[keygen_pwm_a_idx],
  destination: as_addr
};

st_NttType to_ntt_2_i;
assign to_ntt_2_i = '{
  mode: Intt,
  operand1: as_addr_in,
  operand2: temp_addr_in,
  destination: as_intt_addr_in
};

st_NttType to_ntt_3_i;
assign to_ntt_3_i = '{
  mode: Pwa,
  operand1: as_intt_addr_in,
  operand2: s2_addrs_in[keygen_t_idx],
  destination: t_addrs_in[keygen_t_idx]
};

st_Power2RoundType to_power_2_round_0_i;
assign to_power_2_round_0_i = '{
  t_addr: t_addrs_in[64'd0]
};

logic unsigned [63:0] func_concat_0_i;
assign func_concat_0_i = func_concat(pk_ram_data, sampler_offset_f);

logic unsigned [63:0] func_concat_pk_0_i;
assign func_concat_pk_0_i = func_concat_pk(from_api.pk, 3'(sipo_chunk_idx[1:0]));

st_ToSamplerType to_sampler_5_i;
assign to_sampler_5_i = '{
  mode: Shake256,
  destination: tr_reg_id_in
};

st_ToApiType api_out_0_i;
assign api_out_0_i = '{
  tr: (from_keccak_piso_vld_in ? from_keccak_piso[511:0] : to_api.tr),
  sk_out: to_api.sk_out
};

st_SkEncodeType to_sk_encode_0_i;
assign to_sk_encode_0_i = '{
  coeff_addr: s1_addrs_in[64'd0]
};

logic unsigned [63:0] getChunk_4_i;
assign getChunk_4_i = getChunk(20736'(from_api.tr), 16'(sipo_chunk_idx[2:0]));

logic unsigned [63:0] func_concat_msg_p_0_i;
assign func_concat_msg_p_0_i = func_concat_msg_p(msg_prime, sipo_chunk_idx[3:0]);

st_ToSamplerType to_sampler_6_i;
assign to_sampler_6_i = '{
  mode: Shake256,
  destination: mu_reg_id_in
};

st_RegsType registers_2_i;
assign registers_2_i = '{
  rho: registers.rho,
  rho_prime: registers.rho_prime,
  K: registers.K,
  mu: from_ext_mu,
  kappa: registers.kappa,
  c: registers.c
};

logic unsigned [63:0] getChunk_5_i;
assign getChunk_5_i = getChunk(20736'(registers.K), 16'(sipo_chunk_idx[1:0]));

logic unsigned [63:0] func_concat_seed_1_i;
assign func_concat_seed_1_i = func_concat_seed(from_api.sign_rnd, 3'(sipo_chunk_idx[1:0]));

logic unsigned [63:0] getChunk_6_i;
assign getChunk_6_i = getChunk(20736'(registers.mu), 16'(sipo_chunk_idx[2:0]));

st_RegsType registers_3_i;
assign registers_3_i = '{
  rho: registers.rho,
  rho_prime: (from_keccak_piso_vld_in ? from_keccak_piso[511:0] : registers.rho_prime),
  K: registers.K,
  mu: registers.mu,
  kappa: registers.kappa,
  c: registers.c
};

logic unsigned [63:0] getChunk_7_i;
assign getChunk_7_i = getChunk(20736'(entropy_ForStmt_828_9), 16'(sipo_chunk_idx[2:0]));

logic unsigned [63:0] getChunk_8_i;
assign getChunk_8_i = getChunk(20736'(counter_ForStmt_838_9), 16'd0);

st_ToSamplerType to_sampler_7_i;
assign to_sampler_7_i = '{
  mode: ExpMask,
  destination: y_addrs_in[sign_expand_mask_idx]
};

st_NttType to_ntt_4_i;
assign to_ntt_4_i = '{
  mode: Ntt,
  operand1: y_addrs_in[sign_ntt_y_idx],
  operand2: temp_addr_in,
  destination: y_ntt_addrs_in[sign_ntt_y_idx]
};

st_ToSamplerType to_sampler_8_i;
assign to_sampler_8_i = '{
  mode: RejSampler,
  destination: ay0_addr_in
};

st_NttType to_ntt_5_i;
assign to_ntt_5_i = '{
  mode: ((({ 56'd0, sign_compute_w0_y_idx} ) > 64'd0) ? PwmAccuSampler : PwmSampler),
  operand1: rho_id_ForStmt_920_11,
  operand2: y_ntt_addrs_ForStmt_920_11[sign_compute_w0_y_idx],
  destination: ay0_addr
};

st_NttType to_ntt_6_i;
assign to_ntt_6_i = '{
  mode: Intt,
  operand1: ay0_addr_in,
  operand2: temp_addr_in,
  destination: w0_addrs_in[sign_compute_w0_idx]
};

st_DecomposeType to_decompose_0_i;
assign to_decompose_0_i = '{
  source_addr: w0_addrs_in[64'd0],
  destination: w0_addrs_in[64'd0]
};

st_ToSamplerType to_sampler_9_i;
assign to_sampler_9_i = '{
  mode: Shake256,
  destination: sig_c_reg_id_in
};

st_RegsType registers_4_i;
assign registers_4_i = '{
  rho: registers.rho,
  rho_prime: registers.rho_prime,
  K: registers.K,
  mu: registers.mu,
  kappa: registers.kappa,
  c: '{ 0: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[32:0]) : registers.c[0]), 1: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[64:32]) : registers.c[1]), 2: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[96:64]) : registers.c[2]), 3: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[128:96]) : registers.c[3]), 4: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[160:128]) : registers.c[4]), 5: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[192:160]) : registers.c[5]), 6: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[224:192]) : registers.c[6]), 7: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[256:224]) : registers.c[7]), 8: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[288:256]) : registers.c[8]), 9: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[320:288]) : registers.c[9]), 10: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[352:320]) : registers.c[10]), 11: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[384:352]) : registers.c[11]), 12: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[416:384]) : registers.c[12]), 13: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[448:416]) : registers.c[13]), 14: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[480:448]) : registers.c[14]), 15: (from_keccak_piso_vld_in ? 32'(from_keccak_piso[512:480]) : registers.c[15]) }
};

logic unsigned [63:0] func_concat_sig_c_0_i;
assign func_concat_sig_c_0_i = func_concat_sig_c(registers.c, sipo_chunk_idx[2:0]);

st_ToSamplerType to_sampler_10_i;
assign to_sampler_10_i = '{
  mode: SampleInBall,
  destination: 15'd0
};

st_RegsType registers_5_i;
assign registers_5_i = '{
  rho: registers.rho,
  rho_prime: registers.rho_prime,
  K: registers.K,
  mu: registers.mu,
  kappa: (16'd7 + registers.kappa),
  c: registers.c
};

st_SigDecodeType to_sig_decode_z_0_i;
assign to_sig_decode_z_0_i = '{
  destination: z_addrs_in[64'd0]
};

st_NormCheckType to_norm_check_0_i;
assign to_norm_check_0_i = '{
  immediate: norm_check_z_immediate,
  source_addr: z_addrs_in[8'd0]
};

st_NormCheckType to_norm_check_1_i;
assign to_norm_check_1_i = '{
  immediate: norm_check_z_immediate,
  source_addr: z_addrs_in[(8'd1 + verify_norm_check_idx)]
};

st_ToApiType api_out_1_i;
assign api_out_1_i = '{
  tr: from_keccak_piso[511:0],
  sk_out: to_api.sk_out
};

logic unsigned [63:0] func_concat_msg_p_1_i;
assign func_concat_msg_p_1_i = func_concat_msg_p(msg_prime_ForStmt_1178_9, sipo_chunk_idx[3:0]);

st_NttType to_ntt_7_i;
assign to_ntt_7_i = '{
  mode: Ntt,
  operand1: c_addr_in,
  operand2: temp_addr_in,
  destination: c_ntt_addr_in
};

st_NttType to_ntt_8_i;
assign to_ntt_8_i = '{
  mode: Ntt,
  operand1: t_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: t_addrs_in[8'd0]
};

st_NttType to_ntt_9_i;
assign to_ntt_9_i = '{
  mode: Ntt,
  operand1: t_addrs_in[(8'd1 + verify_ntt_t_idx)],
  operand2: temp_addr_in,
  destination: t_addrs_in[(8'd1 + verify_ntt_t_idx)]
};

st_NttType to_ntt_10_i;
assign to_ntt_10_i = '{
  mode: Ntt,
  operand1: z_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: z_ntt_addrs_in[8'd0]
};

st_NttType to_ntt_11_i;
assign to_ntt_11_i = '{
  mode: Ntt,
  operand1: z_addrs_in[(8'd1 + verify_ntt_z_idx)],
  operand2: temp_addr_in,
  destination: z_ntt_addrs_in[(8'd1 + verify_ntt_z_idx)]
};

st_ToSamplerType to_sampler_11_i;
assign to_sampler_11_i = '{
  mode: RejSampler,
  destination: az_addr_in
};

st_NttType to_ntt_12_i;
assign to_ntt_12_i = '{
  mode: ((({ 56'd0, verify_compute_az_idx} ) > 64'd0) ? PwmAccuSampler : PwmSampler),
  operand1: rho_id_ForStmt_1272_11,
  operand2: z_ntt_addrs_ForStmt_1272_11[verify_compute_az_idx],
  destination: az_addr
};

st_NttType to_ntt_13_i;
assign to_ntt_13_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: t_addrs_in[verify_compute_w0_idx],
  destination: ct_addr_in
};

st_NttType to_ntt_14_i;
assign to_ntt_14_i = '{
  mode: Pws,
  operand1: ct_addr_in,
  operand2: az_addr_in,
  destination: az_addr_in
};

st_NttType to_ntt_15_i;
assign to_ntt_15_i = '{
  mode: Intt,
  operand1: az_addr_in,
  operand2: temp_addr_in,
  destination: w0_addrs_in[verify_compute_w0_idx]
};

st_SigDecodeType to_sig_decode_h_0_i;
assign to_sig_decode_h_0_i = '{
  destination: hint_r_addr_in
};

st_UseHintType to_use_hint_0_i;
assign to_use_hint_0_i = '{
  operand1: w0_addrs_in[64'd0],
  operand2: hint_r_addr_in
};

st_ToSamplerType to_sampler_12_i;
assign to_sampler_12_i = '{
  mode: Shake256,
  destination: verify_res_reg_id_in
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

`ifdef NO_ABSTRACTION
property ctrl_reset_p;
  $past(!rst_n) |->
  idle &&
  sign_compute_w0_idx == 8'd0 &&
  sign_compute_w0_y_idx == 8'd0 &&
  sign_expand_mask_idx == 8'd0 &&
  sign_ntt_y_idx == 8'd0 &&
  verify_compute_az_idx == 8'd0 &&
  verify_compute_w0_idx == 8'd0 &&
  verify_norm_check_idx == 8'd0 &&
  verify_ntt_t_idx == 8'd0 &&
  verify_ntt_z_idx == 8'd0 &&
  enable_lfsr == 0 &&
  keygen_ntt_s1_idx == 3'd0 &&
  keygen_pwm_a_idx == 8'd0 &&
  keygen_t_idx == 8'd0 &&
  msg_start_o == 0 &&
  registers.rho == registers_0_i.rho &&
  registers.rho_prime == registers_0_i.rho_prime &&
  registers.K == registers_0_i.K &&
  registers.kappa == registers_0_i.kappa &&
  registers.c == registers_0_i.c &&
  rejbounded_counter == 16'd0 &&
  set_c_valid_out == 0 &&
  set_w0_valid_out == 0 &&
  set_y_valid_out == 0 &&
  sha3_start_o == 0 &&
  to_decompose_vld == 0 &&
  to_keccak_vld == 0 &&
  to_norm_check_vld == 0 &&
  to_ntt_vld == 0 &&
  to_pk_decode_vld == 0 &&
  to_power_2_round_vld == 0 &&
  to_sampler_vld == 0 &&
  to_sig_decode_h_vld == 0 &&
  to_sig_decode_z_vld == 0 &&
  to_sk_encode_vld == 0 &&
  to_use_hint_vld == 0;
endproperty
ctrl_reset_a: assert property (ctrl_reset_p);
`endif 

property ctrl_Keygen_ntt_s1_idle_to_keygen_ntt_s1_start_p;
  Keygen_ntt_s1_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_ntt_s1_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_ntt == $past(to_ntt_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_ntt_vld == 1;
endproperty
ctrl_Keygen_ntt_s1_idle_to_keygen_ntt_s1_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_Keygen_ntt_s1_idle_to_keygen_ntt_s1_start_p);


property ctrl_idle_to_idle_p;
  idle &&
  (api_in.instr == NoOp)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  //$stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_idle_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_idle_to_idle_p);


property ctrl_idle_to_keygen_rnd_seed_SHA3_START_p;
  idle &&
  ((api_in.instr == Keygen) || (api_in.instr == KeygenSign))
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_rnd_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 1) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_idle_to_keygen_rnd_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_idle_to_keygen_rnd_seed_SHA3_START_p);


property ctrl_idle_to_sign_rnd_seed_SHA3_START_p;
  idle &&
  (api_in.instr == Sign)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_rnd_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 1) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_idle_to_sign_rnd_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_idle_to_sign_rnd_seed_SHA3_START_p);


property ctrl_idle_to_verify_pk_decode_start_p;
  idle &&
  (api_in.instr == Verify)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_pk_decode_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 1) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_pk_decode == $past(to_pk_decode_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_pk_decode_vld == 1;
endproperty
ctrl_idle_to_verify_pk_decode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_idle_to_verify_pk_decode_start_p);


property ctrl_keygen_compute_t_start_to_keygen_compute_t_p;
  keygen_compute_t_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_t &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_t_start_to_keygen_compute_t_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_start_to_keygen_compute_t_p);


property ctrl_keygen_compute_t_to_keygen_compute_t_p;
  keygen_compute_t &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_t &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_t_to_keygen_compute_t_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_to_keygen_compute_t_p);


property ctrl_keygen_compute_t_to_keygen_power_2_round_start_p;
  keygen_compute_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, keygen_t_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_power_2_round_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == 8'd0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_power_2_round == $past(to_power_2_round_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_power_2_round_vld == 1;
endproperty
ctrl_keygen_compute_t_to_keygen_power_2_round_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_to_keygen_power_2_round_start_p);


property ctrl_keygen_compute_t_to_keygen_pwm_a_write_rho_SHA3_START_p;
  keygen_compute_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, keygen_t_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_pwm_a_write_rho_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == 8'd0 &&
  keygen_t_idx == (8'd1 + $past(keygen_t_idx, 2)) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_compute_t_to_keygen_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_to_keygen_pwm_a_write_rho_SHA3_START_p);


property ctrl_keygen_compute_tr_sampling_start_to_keygen_compute_tr_sampling_p;
  keygen_compute_tr_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_sampling_start_to_keygen_compute_tr_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_sampling_start_to_keygen_compute_tr_sampling_p);


property ctrl_keygen_compute_tr_sampling_to_keygen_compute_tr_sampling_p;
  keygen_compute_tr_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_sampling_to_keygen_compute_tr_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_sampling_to_keygen_compute_tr_sampling_p);


property ctrl_keygen_compute_tr_sampling_to_keygen_sk_encode_start_p;
  keygen_compute_tr_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_sk_encode_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_sk_encode == $past(to_sk_encode_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_sk_encode_vld == 1;
endproperty
ctrl_keygen_compute_tr_sampling_to_keygen_sk_encode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_sampling_to_keygen_sk_encode_start_p);


property ctrl_keygen_compute_tr_write_pk_SHA3_START_to_keygen_compute_tr_write_pk_start_p;
  keygen_compute_tr_write_pk_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_write_pk_SHA3_START_to_keygen_compute_tr_write_pk_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_SHA3_START_to_keygen_compute_tr_write_pk_start_p);


property ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_sampling_start_p;
  keygen_compute_tr_write_pk_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_5_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_sampling_start_p);


property ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_write_pk_msg_done_p;
  keygen_compute_tr_write_pk_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_write_pk_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_msg_done_to_keygen_compute_tr_write_pk_msg_done_p);


property ctrl_keygen_compute_tr_write_pk_start_to_keygen_compute_tr_write_pk_p;
  keygen_compute_tr_write_pk_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_write_pk_start_to_keygen_compute_tr_write_pk_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_start_to_keygen_compute_tr_write_pk_p);


property ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_p;
  keygen_compute_tr_write_pk &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_p);


property ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_1_p;
  keygen_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx >= 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == func_concat_0_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_1_p);


property ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_2_p;
  keygen_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx < 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_pk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_2_p);


property ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_msg_done_p;
  keygen_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx >= 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_compute_tr_write_pk_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == func_concat_0_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_to_keygen_compute_tr_write_pk_msg_done_p);


property ctrl_keygen_end_state_to_idle_p;
  keygen_end_state &&
  (api_in.instr != Sign) &&
  (api_in.instr != KeygenSign) &&
  (api_in.instr != Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_end_state_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_end_state_to_idle_p);


property ctrl_keygen_end_state_to_sign_compute_mu_idle_p;
  keygen_end_state &&
  (api_in.instr == KeygenSign)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_keygen_end_state_to_sign_compute_mu_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_end_state_to_sign_compute_mu_idle_p);


property ctrl_keygen_end_state_to_sign_rnd_seed_SHA3_START_p;
  keygen_end_state &&
  (api_in.instr == Sign)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_rnd_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
//ctrl_keygen_end_state_to_sign_rnd_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_end_state_to_sign_rnd_seed_SHA3_START_p);


property ctrl_keygen_end_state_to_verify_pk_decode_start_p;
  keygen_end_state &&
  (api_in.instr == Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_pk_decode == $past(to_pk_decode_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_pk_decode_vld == 1;
endproperty
//ctrl_keygen_end_state_to_verify_pk_decode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_end_state_to_verify_pk_decode_start_p);


property ctrl_keygen_expand_seed_SHA3_START_to_keygen_expand_seed_start_p;
  keygen_expand_seed_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_expand_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_expand_seed_SHA3_START_to_keygen_expand_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_SHA3_START_to_keygen_expand_seed_start_p);


property ctrl_keygen_expand_seed_sampling_start_to_keygen_expand_seed_sampling_p;
  keygen_expand_seed_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_expand_seed_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_expand_seed_sampling_start_to_keygen_expand_seed_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_sampling_start_to_keygen_expand_seed_sampling_p);


property ctrl_keygen_expand_seed_sampling_to_keygen_expand_seed_sampling_p;
  keygen_expand_seed_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_expand_seed_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_1_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_expand_seed_sampling_to_keygen_expand_seed_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_sampling_to_keygen_expand_seed_sampling_p);


property ctrl_keygen_expand_seed_sampling_to_keygen_write_rejbounded_input_s1_SHA3_START_p;
  keygen_expand_seed_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_write_rejbounded_input_s1_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers_1_i, 2) &&
  rejbounded_counter == 16'd0 &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_expand_seed_sampling_to_keygen_write_rejbounded_input_s1_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_sampling_to_keygen_write_rejbounded_input_s1_SHA3_START_p);


property ctrl_keygen_expand_seed_start_to_keygen_write_seed_p;
  keygen_expand_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_expand_seed_start_to_keygen_write_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_start_to_keygen_write_seed_p);


property ctrl_keygen_intt_a_idle_to_keygen_intt_a_start_p;
  keygen_intt_a_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_intt_a_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_ntt == $past(to_ntt_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_ntt_vld == 1;
endproperty
ctrl_keygen_intt_a_idle_to_keygen_intt_a_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_idle_to_keygen_intt_a_start_p);


property ctrl_keygen_intt_a_start_to_keygen_intt_a_p;
  keygen_intt_a_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_intt_a &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_intt_a_start_to_keygen_intt_a_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_start_to_keygen_intt_a_p);


property ctrl_keygen_intt_a_to_keygen_compute_t_start_p;
  keygen_intt_a &&
  ntt_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_compute_t_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_3_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_keygen_intt_a_to_keygen_compute_t_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_to_keygen_compute_t_start_p);


property ctrl_keygen_intt_a_to_keygen_intt_a_p;
  keygen_intt_a &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_intt_a &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_intt_a_to_keygen_intt_a_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_to_keygen_intt_a_p);


property ctrl_keygen_jump_sign_to_idle_p;
  keygen_jump_sign &&
  (from_api.instr != Keygen) &&
  (api_in.instr != Sign) &&
  (api_in.instr != KeygenSign) &&
  (api_in.instr != Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_keygen_jump_sign_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_to_idle_p);


property ctrl_keygen_jump_sign_to_keygen_end_state_p;
  keygen_jump_sign &&
  (from_api.instr == Keygen)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1 
  keygen_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_jump_sign_to_keygen_end_state_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_to_keygen_end_state_p);


property ctrl_keygen_jump_sign_to_sign_check_mode_p;
  keygen_jump_sign &&
  (from_api.instr != Keygen) &&
  (api_in.instr == KeygenSign)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_check_mode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_jump_sign_to_sign_check_mode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_to_sign_check_mode_p);


property ctrl_keygen_jump_sign_to_sign_rnd_seed_SHA3_START_p;
  keygen_jump_sign &&
  (from_api.instr != Keygen) &&
  (api_in.instr == Sign)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_rnd_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
//ctrl_keygen_jump_sign_to_sign_rnd_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_to_sign_rnd_seed_SHA3_START_p);


property ctrl_keygen_jump_sign_to_verify_pk_decode_start_p;
  keygen_jump_sign &&
  (from_api.instr != Keygen) &&
  (api_in.instr == Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_pk_decode == $past(to_pk_decode_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_pk_decode_vld == 1;
endproperty
//ctrl_keygen_jump_sign_to_verify_pk_decode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_to_verify_pk_decode_start_p);


property ctrl_keygen_ntt_s1_start_to_keygen_ntt_s1_p;
  keygen_ntt_s1_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_ntt_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_ntt_s1_start_to_keygen_ntt_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_start_to_keygen_ntt_s1_p);


property ctrl_keygen_ntt_s1_to_Keygen_ntt_s1_idle_p;
  keygen_ntt_s1 &&
  ntt_done_in &&
  ((64'd1 + ({ 61'h0, keygen_ntt_s1_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  Keygen_ntt_s1_idle &&
  keygen_ntt_s1_idx == (3'd1 + $past(keygen_ntt_s1_idx, 1)) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_ntt_s1_to_Keygen_ntt_s1_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_to_Keygen_ntt_s1_idle_p);


property ctrl_keygen_ntt_s1_to_keygen_ntt_s1_p;
  keygen_ntt_s1 &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_ntt_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_ntt_s1_to_keygen_ntt_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_to_keygen_ntt_s1_p);


property ctrl_keygen_ntt_s1_to_keygen_pwm_a_write_rho_SHA3_START_p;
  keygen_ntt_s1 &&
  ntt_done_in &&
  ((64'd1 + ({ 61'h0, keygen_ntt_s1_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_pwm_a_write_rho_SHA3_START &&
  keygen_ntt_s1_idx == 3'd0 &&
  keygen_pwm_a_idx == 8'd0 &&
  keygen_t_idx == 8'd0 &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_ntt_s1_to_keygen_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_to_keygen_pwm_a_write_rho_SHA3_START_p);


property ctrl_keygen_power_2_round_start_to_keygen_power_2_round_p;
  keygen_power_2_round_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_power_2_round &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_power_2_round_start_to_keygen_power_2_round_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_power_2_round_start_to_keygen_power_2_round_p);


property ctrl_keygen_power_2_round_to_keygen_compute_tr_write_pk_SHA3_START_p;
  keygen_power_2_round &&
  power_2_round_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_compute_tr_write_pk_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_power_2_round_to_keygen_compute_tr_write_pk_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_power_2_round_to_keygen_compute_tr_write_pk_SHA3_START_p);


property ctrl_keygen_power_2_round_to_keygen_power_2_round_p;
  keygen_power_2_round &&
  !power_2_round_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_power_2_round &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_power_2_round_to_keygen_power_2_round_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_power_2_round_to_keygen_power_2_round_p);


property ctrl_keygen_pwm_a_rejection_sampling_start_to_keygen_pwm_a_start_p;
  keygen_pwm_a_rejection_sampling_start
|->
  keygen_pwm_a_start &&
  keygen_ntt_s1_idx == keygen_ntt_s1_idx &&
  keygen_pwm_a_idx == keygen_pwm_a_idx &&
  keygen_t_idx == keygen_t_idx &&
  registers == registers &&
  rejbounded_counter == rejbounded_counter &&
  sign_compute_w0_idx == sign_compute_w0_idx &&
  sign_compute_w0_y_idx == sign_compute_w0_y_idx &&
  sign_expand_mask_idx == sign_expand_mask_idx &&
  sign_ntt_y_idx == sign_ntt_y_idx &&
  to_ntt == to_ntt_1_i &&
  verify_compute_az_idx == verify_compute_az_idx &&
  verify_compute_w0_idx == verify_compute_w0_idx &&
  verify_norm_check_idx == verify_norm_check_idx &&
  verify_ntt_t_idx == verify_ntt_t_idx &&
  verify_ntt_z_idx == verify_ntt_z_idx &&
  to_ntt_vld == 1;
endproperty
ctrl_keygen_pwm_a_rejection_sampling_start_to_keygen_pwm_a_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_rejection_sampling_start_to_keygen_pwm_a_start_p);


property ctrl_keygen_pwm_a_start_to_keygen_pwm_a_p;
  keygen_pwm_a_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_start_to_keygen_pwm_a_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_start_to_keygen_pwm_a_p);


property ctrl_keygen_pwm_a_to_keygen_intt_a_idle_p;
  keygen_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, keygen_pwm_a_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_intt_a_idle &&
  $stable(keygen_ntt_s1_idx) &&
  keygen_pwm_a_idx == 8'd0 &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_to_keygen_intt_a_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_to_keygen_intt_a_idle_p);


property ctrl_keygen_pwm_a_to_keygen_pwm_a_p;
  keygen_pwm_a &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_to_keygen_pwm_a_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_to_keygen_pwm_a_p);


property ctrl_keygen_pwm_a_to_keygen_pwm_a_write_rho_SHA3_START_p;
  keygen_pwm_a &&
  ntt_done_in &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, keygen_pwm_a_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_pwm_a_write_rho_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == (8'd1 + $past(keygen_pwm_a_idx, 2)) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_pwm_a_to_keygen_pwm_a_write_rho_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_to_keygen_pwm_a_write_rho_SHA3_START_p);


property ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_rejection_sampling_start_p;
  keygen_pwm_a_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 1) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_rejection_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_rejection_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_rejection_sampling_start_p);


property ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_write_immediate_msg_done_p;
  keygen_pwm_a_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_msg_done_to_keygen_pwm_a_write_immediate_msg_done_p);


property ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_p;
  keygen_pwm_a_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_p);


property ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_msg_done_p;
  keygen_pwm_a_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == ({ { 64'({ $past(keygen_t_idx, 1) }) }[55:0], $past(keygen_pwm_a_idx, 1)} ) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_to_keygen_pwm_a_write_immediate_msg_done_p);


property ctrl_keygen_pwm_a_write_rho_SHA3_START_to_keygen_pwm_a_write_rho_start_p;
  keygen_pwm_a_write_rho_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_rho_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_write_rho_SHA3_START_to_keygen_pwm_a_write_rho_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_SHA3_START_to_keygen_pwm_a_write_rho_start_p);


property ctrl_keygen_pwm_a_write_rho_start_to_keygen_pwm_a_write_rho_p;
  keygen_pwm_a_write_rho_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_write_rho_start_to_keygen_pwm_a_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_start_to_keygen_pwm_a_write_rho_p);


property ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_immediate_p;
  keygen_pwm_a_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_immediate_p);


property ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_p;
  keygen_pwm_a_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_p);


property ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_1_p;
  keygen_pwm_a_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_pwm_a_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_to_keygen_pwm_a_write_rho_1_p);


property ctrl_keygen_rejbounded_s1_start_to_keygen_rejbounded_s1_p;
  keygen_rejbounded_s1_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rejbounded_s1_start_to_keygen_rejbounded_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_start_to_keygen_rejbounded_s1_p);


property ctrl_keygen_rejbounded_s1_to_keygen_rejbounded_s1_p;
  keygen_rejbounded_s1 &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rejbounded_s1_to_keygen_rejbounded_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_to_keygen_rejbounded_s1_p);


property ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s1_SHA3_START_p;
  keygen_rejbounded_s1 &&
  sampler_done_in &&
  ((64'd1 + ({ 48'h0, rejbounded_counter} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_write_rejbounded_input_s1_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == (16'd1 + $past(rejbounded_counter, 2)) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s1_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s1_SHA3_START_p);


property ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s2_SHA3_START_p;
  keygen_rejbounded_s1 &&
  sampler_done_in &&
  ((64'd1 + ({ 48'h0, rejbounded_counter} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_write_rejbounded_input_s2_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == 16'd7 &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s2_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_to_keygen_write_rejbounded_input_s2_SHA3_START_p);


property ctrl_keygen_rejbounded_s2_start_to_keygen_rejbounded_s2_p;
  keygen_rejbounded_s2_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rejbounded_s2_start_to_keygen_rejbounded_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_start_to_keygen_rejbounded_s2_p);


property ctrl_keygen_rejbounded_s2_to_Keygen_ntt_s1_idle_p;
  keygen_rejbounded_s2 &&
  sampler_done_in &&
  ((64'd1 + ({ 48'h0, rejbounded_counter} )) >= 64'd15)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  Keygen_ntt_s1_idle &&
  keygen_ntt_s1_idx == 3'd0 &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  rejbounded_counter == 16'd0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rejbounded_s2_to_Keygen_ntt_s1_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_to_Keygen_ntt_s1_idle_p);


property ctrl_keygen_rejbounded_s2_to_keygen_rejbounded_s2_p;
  keygen_rejbounded_s2 &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rejbounded_s2_to_keygen_rejbounded_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_to_keygen_rejbounded_s2_p);


property ctrl_keygen_rejbounded_s2_to_keygen_write_rejbounded_input_s2_SHA3_START_p;
  keygen_rejbounded_s2 &&
  sampler_done_in &&
  ((64'd1 + ({ 48'h0, rejbounded_counter} )) < 64'd15)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_write_rejbounded_input_s2_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == (16'd1 + $past(rejbounded_counter, 2)) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_rejbounded_s2_to_keygen_write_rejbounded_input_s2_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_to_keygen_write_rejbounded_input_s2_SHA3_START_p);


property ctrl_keygen_rnd_seed_SHA3_START_to_keygen_rnd_seed_start_p;
  keygen_rnd_seed_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rnd_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rnd_seed_SHA3_START_to_keygen_rnd_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_SHA3_START_to_keygen_rnd_seed_start_p);


property ctrl_keygen_rnd_seed_done_to_keygen_expand_seed_SHA3_START_p;
  keygen_rnd_seed_done
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_expand_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_rnd_seed_done_to_keygen_expand_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_done_to_keygen_expand_seed_SHA3_START_p);


property ctrl_keygen_rnd_seed_lfsr_to_keygen_rnd_seed_done_p;
  keygen_rnd_seed_lfsr
|->
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rnd_seed_done &&
  enable_lfsr == 0 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rnd_seed_lfsr_to_keygen_rnd_seed_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_lfsr_to_keygen_rnd_seed_done_p);


property ctrl_keygen_rnd_seed_start_to_keygen_write_entropy_p;
  keygen_rnd_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rnd_seed_start_to_keygen_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_start_to_keygen_write_entropy_p);


property ctrl_keygen_rnd_seed_wait_to_keygen_write_counter_p;
  keygen_rnd_seed_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_rnd_seed_wait_to_keygen_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_wait_to_keygen_write_counter_p);


property ctrl_keygen_sample_rnd_seed_start_to_keygen_sample_rnd_seed_p;
  keygen_sample_rnd_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_sample_rnd_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_sample_rnd_seed_start_to_keygen_sample_rnd_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sample_rnd_seed_start_to_keygen_sample_rnd_seed_p);


property ctrl_keygen_sample_rnd_seed_to_keygen_rnd_seed_lfsr_p;
  keygen_sample_rnd_seed &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  keygen_rnd_seed_lfsr &&
  enable_lfsr == 1 &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_keygen_sample_rnd_seed_to_keygen_rnd_seed_lfsr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sample_rnd_seed_to_keygen_rnd_seed_lfsr_p);


property ctrl_keygen_sample_rnd_seed_to_keygen_sample_rnd_seed_p;
  keygen_sample_rnd_seed &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_sample_rnd_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_sample_rnd_seed_to_keygen_sample_rnd_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sample_rnd_seed_to_keygen_sample_rnd_seed_p);


property ctrl_keygen_sk_encode_start_to_keygen_sk_encode_p;
  keygen_sk_encode_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_sk_encode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_sk_encode_start_to_keygen_sk_encode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sk_encode_start_to_keygen_sk_encode_p);


property ctrl_keygen_sk_encode_to_keygen_jump_sign_p;
  keygen_sk_encode &&
  sk_encode_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_jump_sign &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_sk_encode_to_keygen_jump_sign_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sk_encode_to_keygen_jump_sign_p);


property ctrl_keygen_sk_encode_to_keygen_sk_encode_p;
  keygen_sk_encode &&
  !sk_encode_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_sk_encode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_sk_encode_to_keygen_sk_encode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sk_encode_to_keygen_sk_encode_p);


property ctrl_keygen_write_counter_msg_done_to_keygen_sample_rnd_seed_start_p;
  keygen_write_counter_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_sample_rnd_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_write_counter_msg_done_to_keygen_sample_rnd_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_msg_done_to_keygen_sample_rnd_seed_start_p);


property ctrl_keygen_write_counter_msg_done_to_keygen_write_counter_msg_done_p;
  keygen_write_counter_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_counter_msg_done_to_keygen_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_msg_done_to_keygen_write_counter_msg_done_p);


property ctrl_keygen_write_counter_to_keygen_write_counter_p;
  keygen_write_counter &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_counter_to_keygen_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_to_keygen_write_counter_p);


property ctrl_keygen_write_counter_to_keygen_write_counter_1_p;
  keygen_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_counter_to_keygen_write_counter_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_to_keygen_write_counter_1_p);


property ctrl_keygen_write_counter_to_keygen_write_counter_msg_done_p;
  keygen_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_counter_to_keygen_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_to_keygen_write_counter_msg_done_p);


property ctrl_keygen_write_entropy_msg_done_to_keygen_rnd_seed_wait_p;
  keygen_write_entropy_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rnd_seed_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_entropy_msg_done_to_keygen_rnd_seed_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_msg_done_to_keygen_rnd_seed_wait_p);


property ctrl_keygen_write_entropy_msg_done_to_keygen_write_entropy_msg_done_p;
  keygen_write_entropy_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_entropy_msg_done_to_keygen_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_msg_done_to_keygen_write_entropy_msg_done_p);


property ctrl_keygen_write_entropy_to_keygen_write_entropy_p;
  keygen_write_entropy &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_entropy_to_keygen_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_to_keygen_write_entropy_p);


property ctrl_keygen_write_entropy_to_keygen_write_entropy_1_p;
  keygen_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_entropy_to_keygen_write_entropy_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_to_keygen_write_entropy_1_p);


property ctrl_keygen_write_entropy_to_keygen_write_entropy_msg_done_p;
  keygen_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_entropy_to_keygen_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_to_keygen_write_entropy_msg_done_p);


property ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_rejbounded_s1_start_p;
  keygen_write_rejbounded_immediate_s1_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s1_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_rejbounded_s1_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_rejbounded_s1_start_p);


property ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_write_rejbounded_immediate_s1_msg_done_p;
  keygen_write_rejbounded_immediate_s1_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s1_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_write_rejbounded_immediate_s1_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_msg_done_to_keygen_write_rejbounded_immediate_s1_msg_done_p);


property ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_p;
  keygen_write_rejbounded_immediate_s1 &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_p);


property ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_msg_done_p;
  keygen_write_rejbounded_immediate_s1 &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s1_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == 64'($past(rejbounded_counter, 1)) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_to_keygen_write_rejbounded_immediate_s1_msg_done_p);


property ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_rejbounded_s2_start_p;
  keygen_write_rejbounded_immediate_s2_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_rejbounded_s2_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_rejbounded_s2_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_rejbounded_s2_start_p);


property ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_write_rejbounded_immediate_s2_msg_done_p;
  keygen_write_rejbounded_immediate_s2_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s2_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_write_rejbounded_immediate_s2_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_msg_done_to_keygen_write_rejbounded_immediate_s2_msg_done_p);


property ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_p;
  keygen_write_rejbounded_immediate_s2 &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_p);


property ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_msg_done_p;
  keygen_write_rejbounded_immediate_s2 &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s2_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == 64'($past(rejbounded_counter, 1)) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_to_keygen_write_rejbounded_immediate_s2_msg_done_p);


property ctrl_keygen_write_rejbounded_input_s1_SHA3_START_to_keygen_write_rejbounded_input_s1_start_p;
  keygen_write_rejbounded_input_s1_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s1_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s1_SHA3_START_to_keygen_write_rejbounded_input_s1_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_SHA3_START_to_keygen_write_rejbounded_input_s1_start_p);


property ctrl_keygen_write_rejbounded_input_s1_start_to_keygen_write_rejbounded_input_s1_p;
  keygen_write_rejbounded_input_s1_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s1_start_to_keygen_write_rejbounded_input_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_start_to_keygen_write_rejbounded_input_s1_p);


property ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_immediate_s1_p;
  keygen_write_rejbounded_input_s1 &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_immediate_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_immediate_s1_p);


property ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_p;
  keygen_write_rejbounded_input_s1 &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_p);


property ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_1_p;
  keygen_write_rejbounded_input_s1 &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_to_keygen_write_rejbounded_input_s1_1_p);


property ctrl_keygen_write_rejbounded_input_s2_SHA3_START_to_keygen_write_rejbounded_input_s2_start_p;
  keygen_write_rejbounded_input_s2_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s2_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s2_SHA3_START_to_keygen_write_rejbounded_input_s2_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_SHA3_START_to_keygen_write_rejbounded_input_s2_start_p);


property ctrl_keygen_write_rejbounded_input_s2_start_to_keygen_write_rejbounded_input_s2_p;
  keygen_write_rejbounded_input_s2_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s2_start_to_keygen_write_rejbounded_input_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_start_to_keygen_write_rejbounded_input_s2_p);


property ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_immediate_s2_p;
  keygen_write_rejbounded_input_s2 &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_immediate_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_immediate_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_immediate_s2_p);


property ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_p;
  keygen_write_rejbounded_input_s2 &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_p);


property ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_1_p;
  keygen_write_rejbounded_input_s2 &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_rejbounded_input_s2 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_to_keygen_write_rejbounded_input_s2_1_p);


property ctrl_keygen_write_seed_immediate_to_keygen_write_seed_immediate_p;
  keygen_write_seed_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_seed_immediate_to_keygen_write_seed_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_immediate_to_keygen_write_seed_immediate_p);


property ctrl_keygen_write_seed_immediate_to_keygen_write_seed_msg_done_p;
  keygen_write_seed_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == 64'h708 &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_seed_immediate_to_keygen_write_seed_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_immediate_to_keygen_write_seed_msg_done_p);


property ctrl_keygen_write_seed_msg_done_to_keygen_expand_seed_sampling_start_p;
  keygen_write_seed_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_expand_seed_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_keygen_write_seed_msg_done_to_keygen_expand_seed_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_msg_done_to_keygen_expand_seed_sampling_start_p);


property ctrl_keygen_write_seed_msg_done_to_keygen_write_seed_msg_done_p;
  keygen_write_seed_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_seed_msg_done_to_keygen_write_seed_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_msg_done_to_keygen_write_seed_msg_done_p);


property ctrl_keygen_write_seed_to_keygen_write_seed_p;
  keygen_write_seed &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_keygen_write_seed_to_keygen_write_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_to_keygen_write_seed_p);


property ctrl_keygen_write_seed_to_keygen_write_seed_1_p;
  keygen_write_seed &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_seed_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_seed_to_keygen_write_seed_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_to_keygen_write_seed_1_p);


property ctrl_keygen_write_seed_to_keygen_write_seed_immediate_p;
  keygen_write_seed &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  keygen_write_seed_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_seed_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_keygen_write_seed_to_keygen_write_seed_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_to_keygen_write_seed_immediate_p);


property ctrl_sign_compute_c_start_to_sign_compute_c_p;
  sign_compute_c_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_c_start_to_sign_compute_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_c_start_to_sign_compute_c_p);


property ctrl_sign_compute_c_to_sign_compute_c_p;
  sign_compute_c &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_4_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_c_to_sign_compute_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_c_to_sign_compute_c_p);


property ctrl_sign_compute_c_to_sign_sample_in_ball_SHA3_START_p;
  sign_compute_c &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_sample_in_ball_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers_4_i, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_compute_c_to_sign_sample_in_ball_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_c_to_sign_sample_in_ball_SHA3_START_p);


property ctrl_sign_compute_lfsr_seed_SHA3_START_to_sign_compute_lfsr_seed_start_p;
  sign_compute_lfsr_seed_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_SHA3_START_to_sign_compute_lfsr_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_SHA3_START_to_sign_compute_lfsr_seed_start_p);


property ctrl_sign_compute_lfsr_seed_lfsr_to_sign_expand_mask_done_p;
  sign_compute_lfsr_seed_lfsr
|->
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_done &&
  enable_lfsr == 0 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_lfsr_to_sign_expand_mask_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_lfsr_to_sign_expand_mask_done_p);


property ctrl_sign_compute_lfsr_seed_sampling_start_to_sign_compute_lfsr_seed_sampling_p;
  sign_compute_lfsr_seed_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_sampling_start_to_sign_compute_lfsr_seed_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_sampling_start_to_sign_compute_lfsr_seed_sampling_p);


property ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_lfsr_p;
  sign_compute_lfsr_seed_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_lfsr_seed_lfsr &&
  enable_lfsr == 1 &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_lfsr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_lfsr_p);


property ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_sampling_p;
  sign_compute_lfsr_seed_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_sampling_to_sign_compute_lfsr_seed_sampling_p);


property ctrl_sign_compute_lfsr_seed_start_to_sign_compute_lfsr_seed_write_entropy_p;
  sign_compute_lfsr_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_start_to_sign_compute_lfsr_seed_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_start_to_sign_compute_lfsr_seed_write_entropy_p);


property ctrl_sign_compute_lfsr_seed_wait_to_sign_compute_lfsr_seed_write_counter_p;
  sign_compute_lfsr_seed_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_wait_to_sign_compute_lfsr_seed_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_wait_to_sign_compute_lfsr_seed_write_counter_p);


property ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_sampling_start_p;
  sign_compute_lfsr_seed_write_counter_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_sampling_start_p);


property ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_write_counter_msg_done_p;
  sign_compute_lfsr_seed_write_counter_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_msg_done_to_sign_compute_lfsr_seed_write_counter_msg_done_p);


property ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_p;
  sign_compute_lfsr_seed_write_counter &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_p);


property ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_1_p;
  sign_compute_lfsr_seed_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_8_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_1_p);


property ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_msg_done_p;
  sign_compute_lfsr_seed_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_8_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_to_sign_compute_lfsr_seed_write_counter_msg_done_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_wait_p;
  sign_compute_lfsr_seed_write_entropy_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_wait_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_write_entropy_msg_done_p;
  sign_compute_lfsr_seed_write_entropy_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_to_sign_compute_lfsr_seed_write_entropy_msg_done_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_p;
  sign_compute_lfsr_seed_write_entropy &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_1_p;
  sign_compute_lfsr_seed_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_7_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_1_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_msg_done_p;
  sign_compute_lfsr_seed_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_lfsr_seed_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_7_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_to_sign_compute_lfsr_seed_write_entropy_msg_done_p);


property ctrl_sign_compute_mu_SHA3_START_to_sign_compute_mu_start_p;
  sign_compute_mu_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_SHA3_START_to_sign_compute_mu_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_SHA3_START_to_sign_compute_mu_start_p);


property ctrl_sign_check_mode_to_sign_compute_mu_idle_p;
  sign_check_mode &&
  !from_ext_mu_mode_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_check_mode_to_sign_compute_mu_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_check_mode_to_sign_compute_mu_idle_p);


property ctrl_sign_compute_mu_idle_to_sign_compute_mu_SHA3_START_p;
  sign_compute_mu_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_SHA3_START &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 1 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_idle_to_sign_compute_mu_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_idle_to_sign_compute_mu_SHA3_START_p);


property ctrl_sign_check_mode_to_sign_compute_rho_prime_SHA3_START_p;
  sign_check_mode &&
  from_ext_mu_mode_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_rho_prime_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers_2_i, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_check_mode_to_sign_compute_rho_prime_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_check_mode_to_sign_compute_rho_prime_SHA3_START_p);

property ctrl_sign_compute_mu_sampling_start_to_sign_compute_mu_sampling_p;
  sign_compute_mu_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_sampling_start_to_sign_compute_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_sampling_start_to_sign_compute_mu_sampling_p);


property ctrl_sign_compute_mu_sampling_to_sign_compute_mu_sampling_p;
  sign_compute_mu_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_2_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_sampling_to_sign_compute_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_sampling_to_sign_compute_mu_sampling_p);


property ctrl_sign_compute_mu_sampling_to_sign_compute_rho_prime_SHA3_START_p;
  sign_compute_mu_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_rho_prime_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers_2_i, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_compute_mu_sampling_to_sign_compute_rho_prime_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_sampling_to_sign_compute_rho_prime_SHA3_START_p);


property ctrl_sign_compute_mu_start_to_sign_compute_mu_write_tr_p;
  sign_compute_mu_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_start_to_sign_compute_mu_write_tr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_start_to_sign_compute_mu_write_tr_p);


property ctrl_sign_compute_mu_wait_to_sign_compute_mu_write_msg_prime_p;
  sign_compute_mu_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_wait_to_sign_compute_mu_write_msg_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_wait_to_sign_compute_mu_write_msg_prime_p);


property ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_sampling_start_p;
  sign_compute_mu_write_msg_prime_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_sampling_start_p);


property ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_write_msg_prime_msg_done_p;
  sign_compute_mu_write_msg_prime_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_msg_prime_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_write_msg_prime_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_msg_done_to_sign_compute_mu_write_msg_prime_msg_done_p);


property ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_p;
  sign_compute_mu_write_msg_prime &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_p);


property ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_1_p;
  sign_compute_mu_write_msg_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_msg_p_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_1_p);


property ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_msg_done_p;
  sign_compute_mu_write_msg_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_msg_prime_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_msg_p_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_to_sign_compute_mu_write_msg_prime_msg_done_p);


property ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_wait_p;
  sign_compute_mu_write_tr_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_wait_p);


property ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_write_tr_msg_done_p;
  sign_compute_mu_write_tr_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_tr_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_write_tr_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_msg_done_to_sign_compute_mu_write_tr_msg_done_p);


property ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_p;
  sign_compute_mu_write_tr &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_p);


property ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_1_p;
  sign_compute_mu_write_tr &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_1_p);


property ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_msg_done_p;
  sign_compute_mu_write_tr &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_mu_write_tr_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_to_sign_compute_mu_write_tr_msg_done_p);


property ctrl_sign_compute_rho_prime_SHA3_START_to_sign_compute_rho_prime_start_p;
  sign_compute_rho_prime_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_SHA3_START_to_sign_compute_rho_prime_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_SHA3_START_to_sign_compute_rho_prime_start_p);


property ctrl_sign_compute_rho_prime_sampling_start_to_sign_compute_rho_prime_sampling_p;
  sign_compute_rho_prime_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_sampling_start_to_sign_compute_rho_prime_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_sampling_start_to_sign_compute_rho_prime_sampling_p);


property ctrl_sign_compute_rho_prime_sampling_to_sign_compute_rho_prime_sampling_p;
  sign_compute_rho_prime_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_3_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_sampling_to_sign_compute_rho_prime_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_sampling_to_sign_compute_rho_prime_sampling_p);


property ctrl_sign_compute_rho_prime_sampling_to_sign_wait_for_y_and_w0_clear_p;
  sign_compute_rho_prime_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_y_and_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_3_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_sampling_to_sign_wait_for_y_and_w0_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_sampling_to_sign_wait_for_y_and_w0_clear_p);


property ctrl_sign_compute_rho_prime_start_to_sign_compute_rho_prime_write_K_p;
  sign_compute_rho_prime_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_K &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_start_to_sign_compute_rho_prime_write_K_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_start_to_sign_compute_rho_prime_write_K_p);


property ctrl_sign_compute_rho_prime_wait_0_to_sign_compute_rho_prime_write_sign_rnd_p;
  sign_compute_rho_prime_wait_0
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_sign_rnd &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_wait_0_to_sign_compute_rho_prime_write_sign_rnd_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_wait_0_to_sign_compute_rho_prime_write_sign_rnd_p);


property ctrl_sign_compute_rho_prime_wait_1_to_sign_compute_rho_prime_write_mu_p;
  sign_compute_rho_prime_wait_1
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_wait_1_to_sign_compute_rho_prime_write_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_wait_1_to_sign_compute_rho_prime_write_mu_p);


property ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_wait_0_p;
  sign_compute_rho_prime_write_K_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_wait_0 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_wait_0_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_wait_0_p);


property ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_write_K_msg_done_p;
  sign_compute_rho_prime_write_K_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_K_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_write_K_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_msg_done_to_sign_compute_rho_prime_write_K_msg_done_p);


property ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_p;
  sign_compute_rho_prime_write_K &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_K &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_p);


property ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_1_p;
  sign_compute_rho_prime_write_K &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd5)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_K &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_5_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_1_p);


property ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_msg_done_p;
  sign_compute_rho_prime_write_K &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd5)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_K_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_5_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_to_sign_compute_rho_prime_write_K_msg_done_p);


property ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_sampling_start_p;
  sign_compute_rho_prime_write_mu_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_15_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_sampling_start_p);


property ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_write_mu_msg_done_p;
  sign_compute_rho_prime_write_mu_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_write_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_msg_done_to_sign_compute_rho_prime_write_mu_msg_done_p);


property ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_p;
  sign_compute_rho_prime_write_mu &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_p);


property ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_1_p;
  sign_compute_rho_prime_write_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_1_p);


property ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_msg_done_p;
  sign_compute_rho_prime_write_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_to_sign_compute_rho_prime_write_mu_msg_done_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_wait_1_p;
  sign_compute_rho_prime_write_sign_rnd_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_wait_1 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_wait_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_wait_1_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_write_sign_rnd_msg_done_p;
  sign_compute_rho_prime_write_sign_rnd_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_sign_rnd_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_write_sign_rnd_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_to_sign_compute_rho_prime_write_sign_rnd_msg_done_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_p;
  sign_compute_rho_prime_write_sign_rnd &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_sign_rnd &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_1_p;
  sign_compute_rho_prime_write_sign_rnd &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd5)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_sign_rnd &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_seed_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_1_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_msg_done_p;
  sign_compute_rho_prime_write_sign_rnd &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd5)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_rho_prime_write_sign_rnd_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_seed_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_to_sign_compute_rho_prime_write_sign_rnd_msg_done_p);


property ctrl_sign_compute_w0_intt_idle_to_sign_compute_w0_intt_start_p;
  sign_compute_w0_intt_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_intt_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_ntt == $past(to_ntt_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_ntt_vld == 1;
endproperty
ctrl_sign_compute_w0_intt_idle_to_sign_compute_w0_intt_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_idle_to_sign_compute_w0_intt_start_p);


property ctrl_sign_compute_w0_intt_start_to_sign_compute_w0_intt_p;
  sign_compute_w0_intt_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_intt &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_intt_start_to_sign_compute_w0_intt_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_start_to_sign_compute_w0_intt_p);


property ctrl_sign_compute_w0_intt_to_sign_compute_w0_intt_p;
  sign_compute_w0_intt &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_intt &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_intt_to_sign_compute_w0_intt_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_to_sign_compute_w0_intt_p);


property ctrl_sign_compute_w0_intt_to_sign_compute_w0_pwm_SHA3_START_p;
  sign_compute_w0_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, sign_compute_w0_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_w0_pwm_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == (8'd1 + $past(sign_compute_w0_idx, 2)) &&
  sign_compute_w0_y_idx == 8'd0 &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_compute_w0_intt_to_sign_compute_w0_pwm_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_to_sign_compute_w0_pwm_SHA3_START_p);


property ctrl_sign_compute_w0_intt_to_sign_set_y_valid_p;
  sign_compute_w0_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, sign_compute_w0_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_set_y_valid &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_y_valid_out == 1 &&
  sign_compute_w0_idx == 8'd0 &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_intt_to_sign_set_y_valid_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_to_sign_set_y_valid_p);


property ctrl_sign_compute_w0_pwm_SHA3_START_to_sign_compute_w0_pwm_start_p;
  sign_compute_w0_pwm_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_SHA3_START_to_sign_compute_w0_pwm_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_SHA3_START_to_sign_compute_w0_pwm_start_p);


property ctrl_sign_compute_w0_pwm_samp_ntt_to_sign_compute_w0_pwm_p;
  sign_compute_w0_pwm_samp_ntt
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_samp_ntt_to_sign_compute_w0_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_samp_ntt_to_sign_compute_w0_pwm_p);


property ctrl_sign_compute_w0_pwm_sampling_start_to_sign_compute_w0_pwm_samp_ntt_p;
  sign_compute_w0_pwm_sampling_start
|->
  sign_compute_w0_pwm_samp_ntt &&
  keygen_ntt_s1_idx == keygen_ntt_s1_idx &&
  keygen_pwm_a_idx == keygen_pwm_a_idx &&
  keygen_t_idx == keygen_t_idx &&
  registers == registers &&
  rejbounded_counter == rejbounded_counter &&
  sign_compute_w0_idx == sign_compute_w0_idx &&
  sign_compute_w0_y_idx == sign_compute_w0_y_idx &&
  sign_expand_mask_idx == sign_expand_mask_idx &&
  sign_ntt_y_idx == sign_ntt_y_idx &&
  to_ntt == to_ntt_5_i &&
  verify_compute_az_idx == verify_compute_az_idx &&
  verify_compute_w0_idx == verify_compute_w0_idx &&
  verify_norm_check_idx == verify_norm_check_idx &&
  verify_ntt_t_idx == verify_ntt_t_idx &&
  verify_ntt_z_idx == verify_ntt_z_idx &&
  to_ntt_vld == 1;
endproperty
ctrl_sign_compute_w0_pwm_sampling_start_to_sign_compute_w0_pwm_samp_ntt_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_sampling_start_to_sign_compute_w0_pwm_samp_ntt_p);


property ctrl_sign_compute_w0_pwm_start_to_sign_compute_w0_pwm_write_rho_p;
  sign_compute_w0_pwm_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_start_to_sign_compute_w0_pwm_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_start_to_sign_compute_w0_pwm_write_rho_p);


property ctrl_sign_compute_w0_pwm_to_sign_compute_w0_intt_idle_p;
  sign_compute_w0_pwm &&
  ntt_done_in &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, sign_compute_w0_y_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_intt_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  sign_compute_w0_y_idx == 8'd0 &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_to_sign_compute_w0_intt_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_to_sign_compute_w0_intt_idle_p);


property ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_p;
  sign_compute_w0_pwm &&
  !(ntt_done_in && sampler_done_in)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_p);


property ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_SHA3_START_p;
  sign_compute_w0_pwm &&
  ntt_done_in &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, sign_compute_w0_y_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_w0_pwm_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == (8'd1 + $past(sign_compute_w0_y_idx, 2)) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_to_sign_compute_w0_pwm_SHA3_START_p);


property ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_sampling_start_p;
  sign_compute_w0_pwm_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 1) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_8_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_sampling_start_p);


property ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_write_immediate_msg_done_p;
  sign_compute_w0_pwm_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_msg_done_to_sign_compute_w0_pwm_write_immediate_msg_done_p);


property ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_p;
  sign_compute_w0_pwm_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_p);


property ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_msg_done_p;
  sign_compute_w0_pwm_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == (({ { 64'({ $past(sign_compute_w0_idx, 1) }) }[55:0], 8'h0} ) | 64'($past(sign_compute_w0_y_idx, 1))) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_to_sign_compute_w0_pwm_write_immediate_msg_done_p);


property ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_immediate_p;
  sign_compute_w0_pwm_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_immediate_p);


property ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_p;
  sign_compute_w0_pwm_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_p);


property ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_1_p;
  sign_compute_w0_pwm_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_compute_w0_pwm_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_rho_to_sign_compute_w0_pwm_write_rho_1_p);


property ctrl_sign_decompose_w_start_to_sign_decompose_w_p;
  sign_decompose_w_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_decompose_w &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_decompose_w_start_to_sign_decompose_w_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_decompose_w_start_to_sign_decompose_w_p);


property ctrl_sign_decompose_w_to_sign_decompose_w_p;
  sign_decompose_w &&
  !decompose_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_decompose_w &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_decompose_w_to_sign_decompose_w_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_decompose_w_to_sign_decompose_w_p);


property ctrl_sign_decompose_w_to_sign_set_w0_valid_p;
  sign_decompose_w &&
  decompose_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_set_w0_valid &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_w0_valid_out == 1 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_decompose_w_to_sign_set_w0_valid_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_decompose_w_to_sign_set_w0_valid_p);


property ctrl_sign_end_of_challenge_to_sign_end_state_p;
  sign_end_of_challenge &&
  !sig_vld_chk_done_in &&
  (vld_lcl_w0 == 1'd1)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_5_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_sign_end_of_challenge_to_sign_end_state_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_of_challenge_to_sign_end_state_p);


property ctrl_sign_end_of_challenge_to_sign_end_state_1_p;
  sign_end_of_challenge &&
  sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_end_of_challenge_to_sign_end_state_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_of_challenge_to_sign_end_state_1_p);


property ctrl_sign_end_of_challenge_to_sign_wait_for_y_and_w0_clear_p;
  sign_end_of_challenge &&
  !sig_vld_chk_done_in &&
  (vld_lcl_w0 != 1'd1)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_y_and_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_5_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_end_of_challenge_to_sign_wait_for_y_and_w0_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_of_challenge_to_sign_wait_for_y_and_w0_clear_p);


property ctrl_sign_end_state_to_idle_p;
  sign_end_state &&
  (api_in.instr != Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_end_state_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_state_to_idle_p);


property ctrl_sign_end_state_to_verify_pk_decode_start_p;
  sign_end_state &&
  (api_in.instr == Verify)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_pk_decode == $past(to_pk_decode_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_pk_decode_vld == 1;
endproperty
//ctrl_sign_end_state_to_verify_pk_decode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_state_to_verify_pk_decode_start_p);


property ctrl_sign_expand_mask_SHA3_START_to_sign_expand_mask_start_p;
  sign_expand_mask_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_SHA3_START_to_sign_expand_mask_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_SHA3_START_to_sign_expand_mask_start_p);


property ctrl_sign_expand_mask_done_to_sign_expand_mask_SHA3_START_p;
  sign_expand_mask_done
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_expand_mask_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == 8'd0 &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_expand_mask_done_to_sign_expand_mask_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_done_to_sign_expand_mask_SHA3_START_p);


property ctrl_sign_expand_mask_sampling_start_to_sign_expand_mask_sampling_p;
  sign_expand_mask_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_sampling_start_to_sign_expand_mask_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_start_to_sign_expand_mask_sampling_p);


property ctrl_sign_expand_mask_sampling_to_sign_expand_mask_SHA3_START_p;
  sign_expand_mask_sampling &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, sign_expand_mask_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_expand_mask_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == (8'd1 + $past(sign_expand_mask_idx, 2)) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_expand_mask_sampling_to_sign_expand_mask_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_to_sign_expand_mask_SHA3_START_p);


property ctrl_sign_expand_mask_sampling_to_sign_expand_mask_sampling_p;
  sign_expand_mask_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_sampling_to_sign_expand_mask_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_to_sign_expand_mask_sampling_p);


property ctrl_sign_expand_mask_sampling_to_sign_ntt_y_idle_p;
  sign_expand_mask_sampling &&
  sampler_done_in &&
  ((64'd1 + ({ 56'h0, sign_expand_mask_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_ntt_y_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  sign_expand_mask_idx == 8'd0 &&
  sign_ntt_y_idx == 8'd0 &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_sampling_to_sign_ntt_y_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_to_sign_ntt_y_idle_p);


property ctrl_sign_expand_mask_start_to_sign_expand_mask_write_rho_prime_p;
  sign_expand_mask_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_rho_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_start_to_sign_expand_mask_write_rho_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_start_to_sign_expand_mask_write_rho_prime_p);


property ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_sampling_start_p;
  sign_expand_mask_write_kappa_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_7_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_sampling_start_p);


property ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_write_kappa_immediate_msg_done_p;
  sign_expand_mask_write_kappa_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_kappa_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_write_kappa_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_msg_done_to_sign_expand_mask_write_kappa_immediate_msg_done_p);


property ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_p;
  sign_expand_mask_write_kappa_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_kappa_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_p);


property ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_msg_done_p;
  sign_expand_mask_write_kappa_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_kappa_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == 64'(($past(registers.kappa, 1) + ({ 8'h0, $past(sign_expand_mask_idx, 1)} ))) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_to_sign_expand_mask_write_kappa_immediate_msg_done_p);


property ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_kappa_immediate_p;
  sign_expand_mask_write_rho_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_kappa_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_kappa_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_kappa_immediate_p);


property ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_p;
  sign_expand_mask_write_rho_prime &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_rho_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_p);


property ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_1_p;
  sign_expand_mask_write_rho_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_expand_mask_write_rho_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_2_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_rho_prime_to_sign_expand_mask_write_rho_prime_1_p);


property ctrl_sign_load_mu_SHA3_START_to_sign_load_mu_start_p;
  sign_load_mu_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_SHA3_START_to_sign_load_mu_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_SHA3_START_to_sign_load_mu_start_p);


property ctrl_sign_load_mu_idle_to_sign_load_mu_SHA3_START_p;
  sign_load_mu_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_SHA3_START &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 1 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_idle_to_sign_load_mu_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_idle_to_sign_load_mu_SHA3_START_p);


property ctrl_sign_load_mu_msg_done_to_sign_load_mu_msg_done_p;
  sign_load_mu_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_msg_done_to_sign_load_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_msg_done_to_sign_load_mu_msg_done_p);


property ctrl_sign_load_mu_msg_done_to_sign_load_mu_wait_p;
  sign_load_mu_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_msg_done_to_sign_load_mu_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_msg_done_to_sign_load_mu_wait_p);


property ctrl_sign_load_mu_start_to_sign_load_mu_p;
  sign_load_mu_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_start_to_sign_load_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_start_to_sign_load_mu_p);


property ctrl_sign_load_mu_to_sign_load_mu_p;
  sign_load_mu &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_load_mu_to_sign_load_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_to_sign_load_mu_p);


property ctrl_sign_load_mu_to_sign_load_mu_1_p;
  sign_load_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_load_mu_to_sign_load_mu_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_to_sign_load_mu_1_p);


property ctrl_sign_load_mu_to_sign_load_mu_msg_done_p;
  sign_load_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_load_mu_to_sign_load_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_to_sign_load_mu_msg_done_p);


property ctrl_sign_load_mu_wait_to_sign_decompose_w_start_p;
  sign_load_mu_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_decompose_w_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_decompose == $past(to_decompose_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_decompose_vld == 1;
endproperty
ctrl_sign_load_mu_wait_to_sign_decompose_w_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_wait_to_sign_decompose_w_start_p);


property ctrl_sign_ntt_y_idle_to_sign_ntt_y_start_p;
  sign_ntt_y_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_ntt_y_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_ntt == $past(to_ntt_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_ntt_vld == 1;
endproperty
ctrl_sign_ntt_y_idle_to_sign_ntt_y_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_idle_to_sign_ntt_y_start_p);


property ctrl_sign_ntt_y_start_to_sign_ntt_y_p;
  sign_ntt_y_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_ntt_y &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_ntt_y_start_to_sign_ntt_y_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_start_to_sign_ntt_y_p);


property ctrl_sign_ntt_y_to_sign_ntt_y_p;
  sign_ntt_y &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_ntt_y &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_ntt_y_to_sign_ntt_y_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_to_sign_ntt_y_p);


property ctrl_sign_ntt_y_to_sign_ntt_y_idle_p;
  sign_ntt_y &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, sign_ntt_y_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_ntt_y_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  sign_ntt_y_idx == (8'd1 + $past(sign_ntt_y_idx, 1)) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_ntt_y_to_sign_ntt_y_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_to_sign_ntt_y_idle_p);


property ctrl_sign_ntt_y_to_sign_wait_for_w0_clear_p;
  sign_ntt_y &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, sign_ntt_y_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  sign_ntt_y_idx == 8'd0 &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_ntt_y_to_sign_wait_for_w0_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_to_sign_wait_for_w0_clear_p);


property ctrl_sign_rnd_seed_SHA3_START_to_sign_rnd_seed_start_p;
  sign_rnd_seed_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_rnd_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_rnd_seed_SHA3_START_to_sign_rnd_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_SHA3_START_to_sign_rnd_seed_start_p);


property ctrl_sign_rnd_seed_lfsr_to_idle_p;
  sign_rnd_seed_lfsr &&
  (api_in.instr != Sign) &&
  (api_in.instr != KeygenSign) &&
  (api_in.instr != Verify)
|->
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  enable_lfsr == 0 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_sign_rnd_seed_lfsr_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_lfsr_to_idle_p);


property ctrl_sign_rnd_seed_lfsr_to_sign_check_mode_p;
  sign_rnd_seed_lfsr &&
  ((api_in.instr == Sign))
|->
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##1 (enable_lfsr == 0)[*2] and
  ##2
  sign_check_mode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_rnd_seed_lfsr_to_sign_check_mode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_lfsr_to_sign_check_mode_p);


property ctrl_sign_rnd_seed_lfsr_to_verify_pk_decode_start_p;
  sign_rnd_seed_lfsr &&
  (api_in.instr == Verify)
|->
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode_start &&
  enable_lfsr == 0 &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_pk_decode == $past(to_pk_decode_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_pk_decode_vld == 1;
endproperty
//ctrl_sign_rnd_seed_lfsr_to_verify_pk_decode_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_lfsr_to_verify_pk_decode_start_p);


property ctrl_sign_rnd_seed_start_to_sign_write_entropy_p;
  sign_rnd_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_rnd_seed_start_to_sign_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_start_to_sign_write_entropy_p);


property ctrl_sign_rnd_seed_wait_to_sign_write_counter_p;
  sign_rnd_seed_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_rnd_seed_wait_to_sign_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_wait_to_sign_write_counter_p);


property ctrl_sign_sample_in_ball_SHA3_START_to_sign_sample_in_ball_start_p;
  sign_sample_in_ball_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_SHA3_START_to_sign_sample_in_ball_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_SHA3_START_to_sign_sample_in_ball_start_p);


property ctrl_sign_sample_in_ball_sampling_start_to_sign_sample_in_ball_sampling_p;
  sign_sample_in_ball_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_sampling_start_to_sign_sample_in_ball_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_sampling_start_to_sign_sample_in_ball_sampling_p);


property ctrl_sign_sample_in_ball_sampling_to_sign_sample_in_ball_sampling_p;
  sign_sample_in_ball_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_sampling_to_sign_sample_in_ball_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_sampling_to_sign_sample_in_ball_sampling_p);


property ctrl_sign_sample_in_ball_sampling_to_sign_set_c_valid_p;
  sign_sample_in_ball_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_set_c_valid &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_c_valid_out == 1 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_sampling_to_sign_set_c_valid_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_sampling_to_sign_set_c_valid_p);


property ctrl_sign_sample_in_ball_start_to_sign_sample_in_ball_write_c_p;
  sign_sample_in_ball_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_start_to_sign_sample_in_ball_write_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_start_to_sign_sample_in_ball_write_c_p);


property ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_sampling_start_p;
  sign_sample_in_ball_write_c_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == to_sampler_10_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_sampling_start_p);


property ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_write_c_msg_done_p;
  sign_sample_in_ball_write_c_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_write_c_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_write_c_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_msg_done_to_sign_sample_in_ball_write_c_msg_done_p);


property ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_p;
  sign_sample_in_ball_write_c &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_p);


property ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_1_p;
  sign_sample_in_ball_write_c &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_sig_c_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_1_p);


property ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_msg_done_p;
  sign_sample_in_ball_write_c &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_in_ball_write_c_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_sig_c_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_to_sign_sample_in_ball_write_c_msg_done_p);


property ctrl_sign_sample_rnd_seed_start_to_sign_sample_rnd_seed_p;
  sign_sample_rnd_seed_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_rnd_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_rnd_seed_start_to_sign_sample_rnd_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_rnd_seed_start_to_sign_sample_rnd_seed_p);


property ctrl_sign_sample_rnd_seed_to_sign_rnd_seed_lfsr_p;
  sign_sample_rnd_seed &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_rnd_seed_lfsr &&
  enable_lfsr == 1 &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_sample_rnd_seed_to_sign_rnd_seed_lfsr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_rnd_seed_to_sign_rnd_seed_lfsr_p);


property ctrl_sign_sample_rnd_seed_to_sign_sample_rnd_seed_p;
  sign_sample_rnd_seed &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_rnd_seed &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_sample_rnd_seed_to_sign_sample_rnd_seed_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_rnd_seed_to_sign_sample_rnd_seed_p);


property ctrl_sign_set_c_valid_to_sign_end_of_challenge_p;
  sign_set_c_valid
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_end_of_challenge &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_c_valid_out == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_set_c_valid_to_sign_end_of_challenge_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_c_valid_to_sign_end_of_challenge_p);


property ctrl_sign_set_w0_valid_to_sign_wait_for_c_clear_p;
  sign_set_w0_valid
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_c_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_w0_valid_out == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_set_w0_valid_to_sign_wait_for_c_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_w0_valid_to_sign_wait_for_c_clear_p);


property ctrl_sign_set_y_valid_to_sign_load_mu_idle_p;
  sign_set_y_valid
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_load_mu_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  set_y_valid_out == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_set_y_valid_to_sign_load_mu_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_y_valid_to_sign_load_mu_idle_p);


property ctrl_sign_wait_for_c_clear_to_sign_compute_c_start_p;
  sign_wait_for_c_clear &&
  !c_valid_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_c_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_sampler == $past(to_sampler_9_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_wait_for_c_clear_to_sign_compute_c_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_c_clear_to_sign_compute_c_start_p);


property ctrl_sign_wait_for_c_clear_to_sign_wait_for_c_clear_p;
  sign_wait_for_c_clear &&
  c_valid_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_c_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_wait_for_c_clear_to_sign_wait_for_c_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_c_clear_to_sign_wait_for_c_clear_p);


property ctrl_sign_wait_for_w0_clear_to_sign_compute_w0_pwm_SHA3_START_p;
  sign_wait_for_w0_clear &&
  !w0_valid_in &&
  !sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_w0_pwm_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == 8'd0 &&
  sign_compute_w0_y_idx == 8'd0 &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_wait_for_w0_clear_to_sign_compute_w0_pwm_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_w0_clear_to_sign_compute_w0_pwm_SHA3_START_p);


property ctrl_sign_wait_for_w0_clear_to_sign_end_state_p;
  sign_wait_for_w0_clear &&
  sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_wait_for_w0_clear_to_sign_end_state_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_w0_clear_to_sign_end_state_p);


property ctrl_sign_wait_for_w0_clear_to_sign_wait_for_w0_clear_p;
  sign_wait_for_w0_clear &&
  w0_valid_in &&
  !sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_wait_for_w0_clear_to_sign_wait_for_w0_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_w0_clear_to_sign_wait_for_w0_clear_p);


property ctrl_sign_wait_for_y_and_w0_clear_to_sign_compute_lfsr_seed_SHA3_START_p;
  sign_wait_for_y_and_w0_clear &&
  !y_valid_in &&
  !sig_vld_chk_done_in &&
  !w0_valid_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  sign_compute_lfsr_seed_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_sign_wait_for_y_and_w0_clear_to_sign_compute_lfsr_seed_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_y_and_w0_clear_to_sign_compute_lfsr_seed_SHA3_START_p);


property ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_p;
  sign_wait_for_y_and_w0_clear &&
  (y_valid_in || w0_valid_in) &&
  !sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_y_and_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_p);


property ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_1_p;
  sign_wait_for_y_and_w0_clear &&
  (!(y_valid_in || w0_valid_in) || sig_vld_chk_done_in) &&
  sig_vld_chk_done_in &&
  (vld_lcl_w0 != 1'd1) &&
  !jump_if_invalid
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_wait_for_y_and_w0_clear &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_y_and_w0_clear_to_sign_wait_for_y_and_w0_clear_1_p);


property ctrl_sign_wait_for_y_and_w0_clear_to_sign_end_state_p;
  sign_wait_for_y_and_w0_clear &&
  sig_vld_chk_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_wait_for_y_and_w0_clear_to_sign_end_state_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_y_and_w0_clear_to_sign_end_state_p);

property ctrl_sign_write_counter_msg_done_to_sign_sample_rnd_seed_start_p;
  sign_write_counter_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_sample_rnd_seed_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_sign_write_counter_msg_done_to_sign_sample_rnd_seed_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_msg_done_to_sign_sample_rnd_seed_start_p);


property ctrl_sign_write_counter_msg_done_to_sign_write_counter_msg_done_p;
  sign_write_counter_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_write_counter_msg_done_to_sign_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_msg_done_to_sign_write_counter_msg_done_p);


property ctrl_sign_write_counter_to_sign_write_counter_p;
  sign_write_counter &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_write_counter_to_sign_write_counter_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_to_sign_write_counter_p);


property ctrl_sign_write_counter_to_sign_write_counter_1_p;
  sign_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_counter &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_write_counter_to_sign_write_counter_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_to_sign_write_counter_1_p);


property ctrl_sign_write_counter_to_sign_write_counter_msg_done_p;
  sign_write_counter &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd2)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_counter_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_write_counter_to_sign_write_counter_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_to_sign_write_counter_msg_done_p);


property ctrl_sign_write_entropy_msg_done_to_sign_rnd_seed_wait_p;
  sign_write_entropy_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_rnd_seed_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_write_entropy_msg_done_to_sign_rnd_seed_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_msg_done_to_sign_rnd_seed_wait_p);


property ctrl_sign_write_entropy_msg_done_to_sign_write_entropy_msg_done_p;
  sign_write_entropy_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_write_entropy_msg_done_to_sign_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_msg_done_to_sign_write_entropy_msg_done_p);


property ctrl_sign_write_entropy_to_sign_write_entropy_p;
  sign_write_entropy &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_sign_write_entropy_to_sign_write_entropy_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_to_sign_write_entropy_p);


property ctrl_sign_write_entropy_to_sign_write_entropy_1_p;
  sign_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_entropy &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_write_entropy_to_sign_write_entropy_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_to_sign_write_entropy_1_p);


property ctrl_sign_write_entropy_to_sign_write_entropy_msg_done_p;
  sign_write_entropy &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  sign_write_entropy_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_sign_write_entropy_to_sign_write_entropy_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_to_sign_write_entropy_msg_done_p);


property ctrl_verify_check_mode_to_verify_compute_mu_SHA3_START_p;
  verify_check_mode &&
  !from_ext_mu_mode_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_mu_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_check_mode_to_verify_compute_mu_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_check_mode_to_verify_compute_mu_SHA3_START_p);


property ctrl_verify_check_mode_to_verify_sample_in_ball_SHA3_START_p;
  verify_check_mode &&
  from_ext_mu_mode_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_SHA3_START &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 1 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_check_mode_to_verify_sample_in_ball_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_check_mode_to_verify_sample_in_ball_SHA3_START_p);


property ctrl_verify_compute_az_SHA3_START_to_verify_compute_az_start_p;
  verify_compute_az_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_SHA3_START_to_verify_compute_az_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_SHA3_START_to_verify_compute_az_start_p);


property ctrl_verify_compute_az_pwm_start_to_verify_compute_az_pwm_p;
  verify_compute_az_pwm_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_pwm_start_to_verify_compute_az_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_start_to_verify_compute_az_pwm_p);


property ctrl_verify_compute_az_pwm_to_verify_compute_az_SHA3_START_p;
  verify_compute_az_pwm &&
  sampler_done_in &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_compute_az_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_az_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == (8'd1 + $past(verify_compute_az_idx, 2)) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_compute_az_pwm_to_verify_compute_az_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_to_verify_compute_az_SHA3_START_p);


property ctrl_verify_compute_az_pwm_to_verify_compute_az_pwm_p;
  verify_compute_az_pwm &&
  !(sampler_done_in && ntt_done_in)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_pwm_to_verify_compute_az_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_to_verify_compute_az_pwm_p);


property ctrl_verify_compute_az_pwm_to_verify_compute_w0_pwm_start_p;
  verify_compute_az_pwm &&
  sampler_done_in &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_compute_az_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_w0_pwm_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_13_i, 2) &&
  verify_compute_az_idx == 8'd0 &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_compute_az_pwm_to_verify_compute_w0_pwm_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_to_verify_compute_w0_pwm_start_p);


property ctrl_verify_compute_az_sampling_start_to_verify_compute_az_pwm_start_p;
  verify_compute_az_sampling_start
|->
  verify_compute_az_pwm_start &&
  keygen_ntt_s1_idx == keygen_ntt_s1_idx &&
  keygen_pwm_a_idx == keygen_pwm_a_idx &&
  keygen_t_idx == keygen_t_idx &&
  registers == registers &&
  rejbounded_counter == rejbounded_counter &&
  sign_compute_w0_idx == sign_compute_w0_idx &&
  sign_compute_w0_y_idx == sign_compute_w0_y_idx &&
  sign_expand_mask_idx == sign_expand_mask_idx &&
  sign_ntt_y_idx == sign_ntt_y_idx &&
  to_ntt == to_ntt_12_i &&
  verify_compute_az_idx == verify_compute_az_idx &&
  verify_compute_w0_idx == verify_compute_w0_idx &&
  verify_norm_check_idx == verify_norm_check_idx &&
  verify_ntt_t_idx == verify_ntt_t_idx &&
  verify_ntt_z_idx == verify_ntt_z_idx &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_compute_az_sampling_start_to_verify_compute_az_pwm_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_sampling_start_to_verify_compute_az_pwm_start_p);


property ctrl_verify_compute_az_start_to_verify_compute_az_write_rho_p;
  verify_compute_az_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_start_to_verify_compute_az_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_start_to_verify_compute_az_write_rho_p);


property ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_sampling_start_p;
  verify_compute_az_write_immediate_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 1) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_11_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_sampling_start_p);


property ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_write_immediate_msg_done_p;
  verify_compute_az_write_immediate_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_msg_done_to_verify_compute_az_write_immediate_msg_done_p);


property ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_p;
  verify_compute_az_write_immediate &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_p);


property ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_msg_done_p;
  verify_compute_az_write_immediate &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_immediate_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == ({ { 64'({ $past(verify_compute_w0_idx, 1) }) }[55:0], $past(verify_compute_az_idx, 1)} ) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_to_verify_compute_az_write_immediate_msg_done_p);


property ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_immediate_p;
  verify_compute_az_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_immediate &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_immediate_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_immediate_p);


property ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_p;
  verify_compute_az_write_rho &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_p);


property ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_1_p;
  verify_compute_az_write_rho &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd4)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_az_write_rho &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_3_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_rho_to_verify_compute_az_write_rho_1_p);


property ctrl_verify_compute_mu_SHA3_START_to_verify_compute_mu_start_p;
  verify_compute_mu_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_SHA3_START_to_verify_compute_mu_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_SHA3_START_to_verify_compute_mu_start_p);


property ctrl_verify_compute_mu_sampling_start_to_verify_compute_mu_sampling_p;
  verify_compute_mu_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_sampling_start_to_verify_compute_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_sampling_start_to_verify_compute_mu_sampling_p);


property ctrl_verify_compute_mu_sampling_to_verify_compute_mu_sampling_p;
  verify_compute_mu_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  registers == $past(registers_2_i, 1) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_sampling_to_verify_compute_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_sampling_to_verify_compute_mu_sampling_p);


property ctrl_verify_compute_mu_sampling_to_verify_sample_in_ball_SHA3_START_p;
  verify_compute_mu_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_sample_in_ball_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers_2_i, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_compute_mu_sampling_to_verify_sample_in_ball_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_sampling_to_verify_sample_in_ball_SHA3_START_p);


property ctrl_verify_compute_mu_start_to_verify_compute_mu_write_tr_p;
  verify_compute_mu_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_start_to_verify_compute_mu_write_tr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_start_to_verify_compute_mu_write_tr_p);


property ctrl_verify_compute_mu_wait_to_verify_compute_mu_write_msg_prime_p;
  verify_compute_mu_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_wait_to_verify_compute_mu_write_msg_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_wait_to_verify_compute_mu_write_msg_prime_p);


property ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_sampling_start_p;
  verify_compute_mu_write_msg_prime_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_sampling_start_p);


property ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_write_msg_prime_msg_done_p;
  verify_compute_mu_write_msg_prime_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_msg_prime_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_write_msg_prime_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_msg_done_to_verify_compute_mu_write_msg_prime_msg_done_p);


property ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_p;
  verify_compute_mu_write_msg_prime &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_p);


property ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_1_p;
  verify_compute_mu_write_msg_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_msg_prime &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_msg_p_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_1_p);


property ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_msg_done_p;
  verify_compute_mu_write_msg_prime &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_msg_prime_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_msg_p_1_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_to_verify_compute_mu_write_msg_prime_msg_done_p);


property ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_wait_p;
  verify_compute_mu_write_tr_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_wait_p);


property ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_write_tr_msg_done_p;
  verify_compute_mu_write_tr_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_tr_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_write_tr_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_msg_done_to_verify_compute_mu_write_tr_msg_done_p);


property ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_p;
  verify_compute_mu_write_tr &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_p);


property ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_1_p;
  verify_compute_mu_write_tr &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_tr &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_1_p);


property ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_msg_done_p;
  verify_compute_mu_write_tr &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_mu_write_tr_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_4_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_to_verify_compute_mu_write_tr_msg_done_p);


property ctrl_verify_compute_tr_SHA3_START_to_verify_compute_tr_start_p;
  verify_compute_tr_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_SHA3_START_to_verify_compute_tr_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_SHA3_START_to_verify_compute_tr_start_p);


property ctrl_verify_compute_tr_sampling_start_to_verify_compute_tr_sampling_p;
  verify_compute_tr_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_sampling_start_to_verify_compute_tr_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_start_to_verify_compute_tr_sampling_p);


property ctrl_verify_compute_tr_sampling_to_verify_check_mode_p;
  verify_compute_tr_sampling &&
  from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_check_mode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
//ctrl_verify_compute_tr_sampling_to_verify_check_mode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_to_verify_check_mode_p);


property ctrl_verify_compute_tr_sampling_to_verify_check_mode_1_p;
  verify_compute_tr_sampling &&
  !from_keccak_piso_vld_in &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_check_mode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_sampling_to_verify_check_mode_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_to_verify_check_mode_1_p);


property ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_p;
  verify_compute_tr_sampling &&
  from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_p);


property ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_1_p;
  verify_compute_tr_sampling &&
  !from_keccak_piso_vld_in &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_to_verify_compute_tr_sampling_1_p);


property ctrl_verify_compute_tr_start_to_verify_compute_tr_write_pk_p;
  verify_compute_tr_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_start_to_verify_compute_tr_write_pk_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_start_to_verify_compute_tr_write_pk_p);


property ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_sampling_start_p;
  verify_compute_tr_write_pk_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == $past(to_sampler_5_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_sampling_start_p);


property ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_write_pk_msg_done_p;
  verify_compute_tr_write_pk_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_write_pk_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_msg_done_to_verify_compute_tr_write_pk_msg_done_p);


property ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_p;
  verify_compute_tr_write_pk &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_p);


property ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_1_p;
  verify_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx >= 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == func_concat_0_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_1_p);


property ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_2_p;
  verify_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx < 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_pk_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_2_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_2_p);


property ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_msg_done_p;
  verify_compute_tr_write_pk &&
  to_keccak_rdy &&
  (sipo_chunk_idx >= 16'd4) &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd325)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_tr_write_pk_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == func_concat_0_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_to_verify_compute_tr_write_pk_msg_done_p);


property ctrl_verify_compute_w0_intt_idle_to_verify_compute_w0_intt_start_p;
  verify_compute_w0_intt_idle
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_intt_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_ntt == $past(to_ntt_15_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_compute_w0_intt_idle_to_verify_compute_w0_intt_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_idle_to_verify_compute_w0_intt_start_p);


property ctrl_verify_compute_w0_intt_start_to_verify_compute_w0_intt_p;
  verify_compute_w0_intt_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_intt &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_intt_start_to_verify_compute_w0_intt_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_start_to_verify_compute_w0_intt_p);


property ctrl_verify_compute_w0_intt_to_verify_compute_az_SHA3_START_p;
  verify_compute_w0_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_compute_w0_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_az_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == 8'd0 &&
  verify_compute_w0_idx == (8'd1 + $past(verify_compute_w0_idx, 2)) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_compute_w0_intt_to_verify_compute_az_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_to_verify_compute_az_SHA3_START_p);


property ctrl_verify_compute_w0_intt_to_verify_compute_w0_intt_p;
  verify_compute_w0_intt &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_intt &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_intt_to_verify_compute_w0_intt_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_to_verify_compute_w0_intt_p);


property ctrl_verify_compute_w0_intt_to_verify_sig_decode_h_start_p;
  verify_compute_w0_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_compute_w0_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_sig_decode_h_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_sig_decode_h == $past(to_sig_decode_h_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == 8'd0 &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_sig_decode_h_vld == 1;
endproperty
ctrl_verify_compute_w0_intt_to_verify_sig_decode_h_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_to_verify_sig_decode_h_start_p);


property ctrl_verify_compute_w0_pwm_start_to_verify_compute_w0_pwm_p;
  verify_compute_w0_pwm_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_pwm_start_to_verify_compute_w0_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pwm_start_to_verify_compute_w0_pwm_p);


property ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pwm_p;
  verify_compute_w0_pwm &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_pwm &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pwm_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pwm_p);


property ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pws_start_p;
  verify_compute_w0_pwm &&
  ntt_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_w0_pws_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_14_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pws_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pwm_to_verify_compute_w0_pws_start_p);


property ctrl_verify_compute_w0_pws_start_to_verify_compute_w0_pws_p;
  verify_compute_w0_pws_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_pws &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_pws_start_to_verify_compute_w0_pws_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pws_start_to_verify_compute_w0_pws_p);


property ctrl_verify_compute_w0_pws_to_verify_compute_w0_intt_idle_p;
  verify_compute_w0_pws &&
  ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_intt_idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_pws_to_verify_compute_w0_intt_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pws_to_verify_compute_w0_intt_idle_p);


property ctrl_verify_compute_w0_pws_to_verify_compute_w0_pws_p;
  verify_compute_w0_pws &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_compute_w0_pws &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_compute_w0_pws_to_verify_compute_w0_pws_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pws_to_verify_compute_w0_pws_p);


property ctrl_verify_end_state_to_idle_p;
  verify_end_state
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  idle &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_end_state_to_idle_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_end_state_to_idle_p);


property ctrl_verify_load_mu_SHA3_START_to_verify_load_mu_start_p;
  verify_load_mu_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_load_mu_SHA3_START_to_verify_load_mu_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_SHA3_START_to_verify_load_mu_start_p);


property ctrl_verify_load_mu_msg_done_to_verify_load_mu_msg_done_p;
  verify_load_mu_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_load_mu_msg_done_to_verify_load_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_msg_done_to_verify_load_mu_msg_done_p);


property ctrl_verify_load_mu_msg_done_to_verify_load_mu_wait_p;
  verify_load_mu_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu_wait &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_load_mu_msg_done_to_verify_load_mu_wait_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_msg_done_to_verify_load_mu_wait_p);


property ctrl_verify_load_mu_start_to_verify_load_mu_p;
  verify_load_mu_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_load_mu_start_to_verify_load_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_start_to_verify_load_mu_p);


property ctrl_verify_load_mu_to_verify_load_mu_p;
  verify_load_mu &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_load_mu_to_verify_load_mu_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_to_verify_load_mu_p);


property ctrl_verify_load_mu_to_verify_load_mu_1_p;
  verify_load_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_load_mu_to_verify_load_mu_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_to_verify_load_mu_1_p);


property ctrl_verify_load_mu_to_verify_load_mu_msg_done_p;
  verify_load_mu &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_load_mu_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(getChunk_6_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_load_mu_to_verify_load_mu_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_to_verify_load_mu_msg_done_p);


property ctrl_verify_load_mu_wait_to_verify_use_hint_start_p;
  verify_load_mu_wait
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1
  verify_use_hint_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_use_hint == $past(to_use_hint_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_use_hint_vld == 1;
endproperty
ctrl_verify_load_mu_wait_to_verify_use_hint_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_wait_to_verify_use_hint_start_p);


property ctrl_verify_mu_sampling_start_to_verify_mu_sampling_p;
  verify_mu_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_mu_sampling_start_to_verify_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_mu_sampling_start_to_verify_mu_sampling_p);


property ctrl_verify_mu_sampling_to_verify_end_state_p;
  verify_mu_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_end_state &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_mu_sampling_to_verify_end_state_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_mu_sampling_to_verify_end_state_p);


property ctrl_verify_mu_sampling_to_verify_mu_sampling_p;
  verify_mu_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_mu_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_mu_sampling_to_verify_mu_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_mu_sampling_to_verify_mu_sampling_p);


property ctrl_verify_norm_check_start_to_verify_norm_check_p;
  verify_norm_check_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_norm_check &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_norm_check_start_to_verify_norm_check_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_start_to_verify_norm_check_p);


property ctrl_verify_norm_check_to_verify_compute_tr_SHA3_START_p;
  verify_norm_check &&
  norm_check_done_in &&
  ((64'd1 + ({ 56'h0, verify_norm_check_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_tr_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == 8'd0 &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_norm_check_to_verify_compute_tr_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_to_verify_compute_tr_SHA3_START_p);


property ctrl_verify_norm_check_to_verify_norm_check_p;
  verify_norm_check &&
  !norm_check_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_norm_check &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_norm_check_to_verify_norm_check_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_to_verify_norm_check_p);


property ctrl_verify_norm_check_to_verify_norm_check_start_p;
  verify_norm_check &&
  norm_check_done_in &&
  ((64'd1 + ({ 56'h0, verify_norm_check_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_norm_check_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_norm_check == $past(to_norm_check_1_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == (8'd1 + $past(verify_norm_check_idx, 2)) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_norm_check_vld == 1;
endproperty
ctrl_verify_norm_check_to_verify_norm_check_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_to_verify_norm_check_start_p);


property ctrl_verify_ntt_c_start_to_verify_ntt_c_p;
  verify_ntt_c_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_c_start_to_verify_ntt_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_c_start_to_verify_ntt_c_p);


property ctrl_verify_ntt_c_to_verify_ntt_c_p;
  verify_ntt_c &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_c_to_verify_ntt_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_c_to_verify_ntt_c_p);


property ctrl_verify_ntt_c_to_verify_ntt_t_start_p;
  verify_ntt_c &&
  ntt_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_ntt_t_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_8_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == 8'd0 &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_ntt_c_to_verify_ntt_t_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_c_to_verify_ntt_t_start_p);


property ctrl_verify_ntt_t_start_to_verify_ntt_t_p;
  verify_ntt_t_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_t &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_t_start_to_verify_ntt_t_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_start_to_verify_ntt_t_p);


property ctrl_verify_ntt_t_to_verify_ntt_t_p;
  verify_ntt_t &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_t &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_t_to_verify_ntt_t_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_to_verify_ntt_t_p);


property ctrl_verify_ntt_t_to_verify_ntt_t_start_p;
  verify_ntt_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_ntt_t_idx} )) < 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_ntt_t_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_9_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == (8'd1 + $past(verify_ntt_t_idx, 2)) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_ntt_t_to_verify_ntt_t_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_to_verify_ntt_t_start_p);


property ctrl_verify_ntt_t_to_verify_ntt_z_start_p;
  verify_ntt_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_ntt_t_idx} )) >= 64'd8)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_ntt_z_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_10_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == 8'd0 &&
  verify_ntt_z_idx == 8'd0 &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_ntt_t_to_verify_ntt_z_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_to_verify_ntt_z_start_p);


property ctrl_verify_ntt_z_start_to_verify_ntt_z_p;
  verify_ntt_z_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_z &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_z_start_to_verify_ntt_z_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_start_to_verify_ntt_z_p);


property ctrl_verify_ntt_z_to_verify_compute_az_SHA3_START_p;
  verify_ntt_z &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_ntt_z_idx} )) >= 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_compute_az_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == 8'd0 &&
  verify_compute_w0_idx == 8'd0 &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == 8'd0;
endproperty
ctrl_verify_ntt_z_to_verify_compute_az_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_to_verify_compute_az_SHA3_START_p);


property ctrl_verify_ntt_z_to_verify_ntt_z_p;
  verify_ntt_z &&
  !ntt_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_ntt_z &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_ntt_z_to_verify_ntt_z_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_to_verify_ntt_z_p);


property ctrl_verify_ntt_z_to_verify_ntt_z_start_p;
  verify_ntt_z &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, verify_ntt_z_idx} )) < 64'd7)
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_ntt_z_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_11_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == (8'd1 + $past(verify_ntt_z_idx, 2)) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_ntt_z_to_verify_ntt_z_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_to_verify_ntt_z_start_p);


property ctrl_verify_pk_decode_start_to_verify_pk_decode_p;
  verify_pk_decode_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_pk_decode_start_to_verify_pk_decode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_pk_decode_start_to_verify_pk_decode_p);


property ctrl_verify_pk_decode_to_verify_pk_decode_p;
  verify_pk_decode &&
  !pk_decode_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_pk_decode &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_pk_decode_to_verify_pk_decode_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_pk_decode_to_verify_pk_decode_p);


property ctrl_verify_pk_decode_to_verify_sig_decode_z_start_p;
  verify_pk_decode &&
  pk_decode_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_sig_decode_z_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_sig_decode_z == $past(to_sig_decode_z_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_sig_decode_z_vld == 1;
endproperty
ctrl_verify_pk_decode_to_verify_sig_decode_z_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_pk_decode_to_verify_sig_decode_z_start_p);


property ctrl_verify_sample_in_ball_SHA3_START_to_verify_sample_in_ball_start_p;
  verify_sample_in_ball_SHA3_START
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 1 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  sha3_start_o == 0 &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_SHA3_START_to_verify_sample_in_ball_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_SHA3_START_to_verify_sample_in_ball_start_p);


property ctrl_verify_sample_in_ball_sampling_start_to_verify_sample_in_ball_sampling_p;
  verify_sample_in_ball_sampling_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_sampling_start_to_verify_sample_in_ball_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_sampling_start_to_verify_sample_in_ball_sampling_p);


property ctrl_verify_sample_in_ball_sampling_to_verify_ntt_c_start_p;
  verify_sample_in_ball_sampling &&
  sampler_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_ntt_c_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_ntt == $past(to_ntt_7_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_ntt_vld == 1;
endproperty
ctrl_verify_sample_in_ball_sampling_to_verify_ntt_c_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_sampling_to_verify_ntt_c_start_p);


property ctrl_verify_sample_in_ball_sampling_to_verify_sample_in_ball_sampling_p;
  verify_sample_in_ball_sampling &&
  !sampler_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_sampling &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_sampling_to_verify_sample_in_ball_sampling_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_sampling_to_verify_sample_in_ball_sampling_p);


property ctrl_verify_sample_in_ball_start_to_verify_sample_in_ball_write_c_p;
  verify_sample_in_ball_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  msg_start_o == 0 &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_start_to_verify_sample_in_ball_write_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_start_to_verify_sample_in_ball_write_c_p);


property ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_sampling_start_p;
  verify_sample_in_ball_write_c_msg_done &&
  to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_sampling_start &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_sampler == to_sampler_10_i &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_sampler_vld == 1;
endproperty
ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_sampling_start_p);


property ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_write_c_msg_done_p;
  verify_sample_in_ball_write_c_msg_done &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_write_c_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_write_c_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_msg_done_to_verify_sample_in_ball_write_c_msg_done_p);


property ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_p;
  verify_sample_in_ball_write_c &&
  !to_keccak_rdy
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 ($stable(to_keccak_vld) && $stable(to_keccak)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_p);


property ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_1_p;
  verify_sample_in_ball_write_c &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) < 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_write_c &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_sig_c_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_1_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_1_p);


property ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_msg_done_p;
  verify_sample_in_ball_write_c &&
  to_keccak_rdy &&
  ((64'd1 + ({ 48'h0, sipo_chunk_idx} )) >= 64'd9)
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sample_in_ball_write_c_msg_done &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  to_keccak == $past(func_concat_sig_c_0_i, 1) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx) &&
  to_keccak_vld == 1;
endproperty
ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_msg_done_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_to_verify_sample_in_ball_write_c_msg_done_p);


property ctrl_verify_sig_decode_h_start_to_verify_sig_decode_h_p;
  verify_sig_decode_h_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sig_decode_h &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sig_decode_h_start_to_verify_sig_decode_h_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_h_start_to_verify_sig_decode_h_p);


property ctrl_verify_sig_decode_h_to_verify_load_mu_SHA3_START_p;
  verify_sig_decode_h &&
  sig_decode_h_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_load_mu_SHA3_START &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  msg_start_o == 0 &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sha3_start_o == 1 &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2);
endproperty
ctrl_verify_sig_decode_h_to_verify_load_mu_SHA3_START_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_h_to_verify_load_mu_SHA3_START_p);


property ctrl_verify_sig_decode_h_to_verify_sig_decode_h_p;
  verify_sig_decode_h &&
  !sig_decode_h_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sig_decode_h &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sig_decode_h_to_verify_sig_decode_h_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_h_to_verify_sig_decode_h_p);


property ctrl_verify_sig_decode_z_start_to_verify_sig_decode_z_p;
  verify_sig_decode_z_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sig_decode_z &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sig_decode_z_start_to_verify_sig_decode_z_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_z_start_to_verify_sig_decode_z_p);


property ctrl_verify_sig_decode_z_to_verify_norm_check_start_p;
  verify_sig_decode_z &&
  sig_decode_z_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0)[*2] and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_norm_check_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_norm_check == $past(to_norm_check_0_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == 8'd0 &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_norm_check_vld == 1;
endproperty
ctrl_verify_sig_decode_z_to_verify_norm_check_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_z_to_verify_norm_check_start_p);


property ctrl_verify_sig_decode_z_to_verify_sig_decode_z_p;
  verify_sig_decode_z &&
  !sig_decode_z_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_sig_decode_z &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_sig_decode_z_to_verify_sig_decode_z_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_z_to_verify_sig_decode_z_p);


property ctrl_verify_use_hint_start_to_verify_use_hint_p;
  verify_use_hint_start
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_use_hint &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_use_hint_start_to_verify_use_hint_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_use_hint_start_to_verify_use_hint_p);


property ctrl_verify_use_hint_to_verify_mu_sampling_start_p;
  verify_use_hint &&
  use_hint_done_in
|->
  ##1 ($stable(enable_lfsr))[*2] and
  ##1 ($stable(msg_start_o))[*2] and
  ##1 ($stable(set_c_valid_out))[*2] and
  ##1 ($stable(set_w0_valid_out))[*2] and
  ##1 ($stable(set_y_valid_out))[*2] and
  ##1 ($stable(sha3_start_o))[*2] and
  ##1 (to_decompose_vld == 0)[*2] and
  ##1 (to_keccak_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_pk_decode_vld == 0)[*2] and
  ##1 (to_power_2_round_vld == 0)[*2] and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0)[*2] and
  ##1 (to_sig_decode_z_vld == 0)[*2] and
  ##1 (to_sk_encode_vld == 0)[*2] and
  ##1 (to_use_hint_vld == 0)[*2] and
  ##2
  verify_mu_sampling_start &&
  keygen_ntt_s1_idx == $past(keygen_ntt_s1_idx, 2) &&
  keygen_pwm_a_idx == $past(keygen_pwm_a_idx, 2) &&
  keygen_t_idx == $past(keygen_t_idx, 2) &&
  registers == $past(registers, 2) &&
  rejbounded_counter == $past(rejbounded_counter, 2) &&
  sign_compute_w0_idx == $past(sign_compute_w0_idx, 2) &&
  sign_compute_w0_y_idx == $past(sign_compute_w0_y_idx, 2) &&
  sign_expand_mask_idx == $past(sign_expand_mask_idx, 2) &&
  sign_ntt_y_idx == $past(sign_ntt_y_idx, 2) &&
  to_sampler == $past(to_sampler_12_i, 2) &&
  verify_compute_az_idx == $past(verify_compute_az_idx, 2) &&
  verify_compute_w0_idx == $past(verify_compute_w0_idx, 2) &&
  verify_norm_check_idx == $past(verify_norm_check_idx, 2) &&
  verify_ntt_t_idx == $past(verify_ntt_t_idx, 2) &&
  verify_ntt_z_idx == $past(verify_ntt_z_idx, 2) &&
  to_sampler_vld == 1;
endproperty
ctrl_verify_use_hint_to_verify_mu_sampling_start_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_use_hint_to_verify_mu_sampling_start_p);


property ctrl_verify_use_hint_to_verify_use_hint_p;
  verify_use_hint &&
  !use_hint_done_in
|->
  ##1 ($stable(enable_lfsr)) and
  ##1 ($stable(msg_start_o)) and
  ##1 ($stable(set_c_valid_out)) and
  ##1 ($stable(set_w0_valid_out)) and
  ##1 ($stable(set_y_valid_out)) and
  ##1 ($stable(sha3_start_o)) and
  ##1 (to_decompose_vld == 0) and
  ##1 (to_keccak_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_pk_decode_vld == 0) and
  ##1 (to_power_2_round_vld == 0) and
  ##1 (to_sampler_vld == 0) and
  ##1 (to_sig_decode_h_vld == 0) and
  ##1 (to_sig_decode_z_vld == 0) and
  ##1 (to_sk_encode_vld == 0) and
  ##1 (to_use_hint_vld == 0) and
  ##1
  verify_use_hint &&
  $stable(keygen_ntt_s1_idx) &&
  $stable(keygen_pwm_a_idx) &&
  $stable(keygen_t_idx) &&
  $stable(registers) &&
  $stable(rejbounded_counter) &&
  $stable(sign_compute_w0_idx) &&
  $stable(sign_compute_w0_y_idx) &&
  $stable(sign_expand_mask_idx) &&
  $stable(sign_ntt_y_idx) &&
  $stable(verify_compute_az_idx) &&
  $stable(verify_compute_w0_idx) &&
  $stable(verify_norm_check_idx) &&
  $stable(verify_ntt_t_idx) &&
  $stable(verify_ntt_z_idx);
endproperty
ctrl_verify_use_hint_to_verify_use_hint_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_use_hint_to_verify_use_hint_p);


property ctrl_idle_eventually_left_p;
  idle &&
   ((api_in.instr == Keygen) || (api_in.instr == KeygenSign) ||
   (api_in.instr == Sign) || (api_in.instr == Verify))
|->
  s_eventually(!idle);
endproperty
ctrl_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_idle_eventually_left_p);


property ctrl_keygen_rnd_seed_SHA3_START_eventually_left_p;
  keygen_rnd_seed_SHA3_START
|->
  s_eventually(!keygen_rnd_seed_SHA3_START);
endproperty
ctrl_keygen_rnd_seed_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_SHA3_START_eventually_left_p);


property ctrl_keygen_rnd_seed_start_eventually_left_p;
  keygen_rnd_seed_start
|->
  s_eventually(!keygen_rnd_seed_start);
endproperty
ctrl_keygen_rnd_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_start_eventually_left_p);


property ctrl_keygen_write_entropy_eventually_left_p;
  keygen_write_entropy
|->
  s_eventually(!keygen_write_entropy);
endproperty
ctrl_keygen_write_entropy_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_eventually_left_p);


property ctrl_keygen_write_entropy_msg_done_eventually_left_p;
  keygen_write_entropy_msg_done
|->
  s_eventually(!keygen_write_entropy_msg_done);
endproperty
ctrl_keygen_write_entropy_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_entropy_msg_done_eventually_left_p);


property ctrl_keygen_rnd_seed_wait_eventually_left_p;
  keygen_rnd_seed_wait
|->
  s_eventually(!keygen_rnd_seed_wait);
endproperty
ctrl_keygen_rnd_seed_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_wait_eventually_left_p);


property ctrl_keygen_write_counter_eventually_left_p;
  keygen_write_counter
|->
  s_eventually(!keygen_write_counter);
endproperty
ctrl_keygen_write_counter_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_eventually_left_p);


property ctrl_keygen_write_counter_msg_done_eventually_left_p;
  keygen_write_counter_msg_done
|->
  s_eventually(!keygen_write_counter_msg_done);
endproperty
ctrl_keygen_write_counter_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_counter_msg_done_eventually_left_p);


property ctrl_keygen_sample_rnd_seed_start_eventually_left_p;
  keygen_sample_rnd_seed_start
|->
  s_eventually(!keygen_sample_rnd_seed_start);
endproperty
ctrl_keygen_sample_rnd_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sample_rnd_seed_start_eventually_left_p);


property ctrl_keygen_sample_rnd_seed_eventually_left_p;
  keygen_sample_rnd_seed
|->
  s_eventually(!keygen_sample_rnd_seed);
endproperty
ctrl_keygen_sample_rnd_seed_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sample_rnd_seed_eventually_left_p);


property ctrl_keygen_rnd_seed_lfsr_eventually_left_p;
  keygen_rnd_seed_lfsr
|->
  s_eventually(!keygen_rnd_seed_lfsr);
endproperty
ctrl_keygen_rnd_seed_lfsr_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_lfsr_eventually_left_p);


property ctrl_keygen_rnd_seed_done_eventually_left_p;
  keygen_rnd_seed_done
|->
  s_eventually(!keygen_rnd_seed_done);
endproperty
ctrl_keygen_rnd_seed_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rnd_seed_done_eventually_left_p);


property ctrl_keygen_expand_seed_SHA3_START_eventually_left_p;
  keygen_expand_seed_SHA3_START
|->
  s_eventually(!keygen_expand_seed_SHA3_START);
endproperty
ctrl_keygen_expand_seed_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_SHA3_START_eventually_left_p);


property ctrl_keygen_expand_seed_start_eventually_left_p;
  keygen_expand_seed_start
|->
  s_eventually(!keygen_expand_seed_start);
endproperty
ctrl_keygen_expand_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_start_eventually_left_p);


property ctrl_keygen_write_seed_eventually_left_p;
  keygen_write_seed
|->
  s_eventually(!keygen_write_seed);
endproperty
ctrl_keygen_write_seed_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_eventually_left_p);


property ctrl_keygen_write_seed_immediate_eventually_left_p;
  keygen_write_seed_immediate
|->
  s_eventually(!keygen_write_seed_immediate);
endproperty
ctrl_keygen_write_seed_immediate_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_immediate_eventually_left_p);


property ctrl_keygen_write_seed_msg_done_eventually_left_p;
  keygen_write_seed_msg_done
|->
  s_eventually(!keygen_write_seed_msg_done);
endproperty
ctrl_keygen_write_seed_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_seed_msg_done_eventually_left_p);


property ctrl_keygen_expand_seed_sampling_start_eventually_left_p;
  keygen_expand_seed_sampling_start
|->
  s_eventually(!keygen_expand_seed_sampling_start);
endproperty
ctrl_keygen_expand_seed_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_sampling_start_eventually_left_p);


property ctrl_keygen_expand_seed_sampling_eventually_left_p;
  keygen_expand_seed_sampling
|->
  s_eventually(!keygen_expand_seed_sampling);
endproperty
ctrl_keygen_expand_seed_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_expand_seed_sampling_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s1_SHA3_START_eventually_left_p;
  keygen_write_rejbounded_input_s1_SHA3_START
|->
  s_eventually(!keygen_write_rejbounded_input_s1_SHA3_START);
endproperty
ctrl_keygen_write_rejbounded_input_s1_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_SHA3_START_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s1_start_eventually_left_p;
  keygen_write_rejbounded_input_s1_start
|->
  s_eventually(!keygen_write_rejbounded_input_s1_start);
endproperty
ctrl_keygen_write_rejbounded_input_s1_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_start_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s1_eventually_left_p;
  keygen_write_rejbounded_input_s1
|->
  s_eventually(!keygen_write_rejbounded_input_s1);
endproperty
ctrl_keygen_write_rejbounded_input_s1_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s1_eventually_left_p);


property ctrl_keygen_write_rejbounded_immediate_s1_eventually_left_p;
  keygen_write_rejbounded_immediate_s1
|->
  s_eventually(!keygen_write_rejbounded_immediate_s1);
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_eventually_left_p);


property ctrl_keygen_write_rejbounded_immediate_s1_msg_done_eventually_left_p;
  keygen_write_rejbounded_immediate_s1_msg_done
|->
  s_eventually(!keygen_write_rejbounded_immediate_s1_msg_done);
endproperty
ctrl_keygen_write_rejbounded_immediate_s1_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s1_msg_done_eventually_left_p);


property ctrl_keygen_rejbounded_s1_start_eventually_left_p;
  keygen_rejbounded_s1_start
|->
  s_eventually(!keygen_rejbounded_s1_start);
endproperty
ctrl_keygen_rejbounded_s1_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_start_eventually_left_p);


property ctrl_keygen_rejbounded_s1_eventually_left_p;
  keygen_rejbounded_s1
|->
  s_eventually(!keygen_rejbounded_s1);
endproperty
ctrl_keygen_rejbounded_s1_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s1_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s2_SHA3_START_eventually_left_p;
  keygen_write_rejbounded_input_s2_SHA3_START
|->
  s_eventually(!keygen_write_rejbounded_input_s2_SHA3_START);
endproperty
ctrl_keygen_write_rejbounded_input_s2_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_SHA3_START_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s2_start_eventually_left_p;
  keygen_write_rejbounded_input_s2_start
|->
  s_eventually(!keygen_write_rejbounded_input_s2_start);
endproperty
ctrl_keygen_write_rejbounded_input_s2_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_start_eventually_left_p);


property ctrl_keygen_write_rejbounded_input_s2_eventually_left_p;
  keygen_write_rejbounded_input_s2
|->
  s_eventually(!keygen_write_rejbounded_input_s2);
endproperty
ctrl_keygen_write_rejbounded_input_s2_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_input_s2_eventually_left_p);


property ctrl_keygen_write_rejbounded_immediate_s2_eventually_left_p;
  keygen_write_rejbounded_immediate_s2
|->
  s_eventually(!keygen_write_rejbounded_immediate_s2);
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_eventually_left_p);


property ctrl_keygen_write_rejbounded_immediate_s2_msg_done_eventually_left_p;
  keygen_write_rejbounded_immediate_s2_msg_done
|->
  s_eventually(!keygen_write_rejbounded_immediate_s2_msg_done);
endproperty
ctrl_keygen_write_rejbounded_immediate_s2_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_write_rejbounded_immediate_s2_msg_done_eventually_left_p);


property ctrl_keygen_rejbounded_s2_start_eventually_left_p;
  keygen_rejbounded_s2_start
|->
  s_eventually(!keygen_rejbounded_s2_start);
endproperty
ctrl_keygen_rejbounded_s2_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_start_eventually_left_p);


property ctrl_keygen_rejbounded_s2_eventually_left_p;
  keygen_rejbounded_s2
|->
  s_eventually(!keygen_rejbounded_s2);
endproperty
ctrl_keygen_rejbounded_s2_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_rejbounded_s2_eventually_left_p);


property ctrl_Keygen_ntt_s1_idle_eventually_left_p;
  Keygen_ntt_s1_idle
|->
  s_eventually(!Keygen_ntt_s1_idle);
endproperty
ctrl_Keygen_ntt_s1_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_Keygen_ntt_s1_idle_eventually_left_p);


property ctrl_keygen_ntt_s1_start_eventually_left_p;
  keygen_ntt_s1_start
|->
  s_eventually(!keygen_ntt_s1_start);
endproperty
ctrl_keygen_ntt_s1_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_start_eventually_left_p);


property ctrl_keygen_ntt_s1_eventually_left_p;
  keygen_ntt_s1
|->
  s_eventually(!keygen_ntt_s1);
endproperty
ctrl_keygen_ntt_s1_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_ntt_s1_eventually_left_p);


property ctrl_keygen_pwm_a_write_rho_SHA3_START_eventually_left_p;
  keygen_pwm_a_write_rho_SHA3_START
|->
  s_eventually(!keygen_pwm_a_write_rho_SHA3_START);
endproperty
ctrl_keygen_pwm_a_write_rho_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_SHA3_START_eventually_left_p);


property ctrl_keygen_pwm_a_write_rho_start_eventually_left_p;
  keygen_pwm_a_write_rho_start
|->
  s_eventually(!keygen_pwm_a_write_rho_start);
endproperty
ctrl_keygen_pwm_a_write_rho_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_start_eventually_left_p);


property ctrl_keygen_pwm_a_write_rho_eventually_left_p;
  keygen_pwm_a_write_rho
|->
  s_eventually(!keygen_pwm_a_write_rho);
endproperty
ctrl_keygen_pwm_a_write_rho_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_rho_eventually_left_p);


property ctrl_keygen_pwm_a_write_immediate_eventually_left_p;
  keygen_pwm_a_write_immediate
|->
  s_eventually(!keygen_pwm_a_write_immediate);
endproperty
ctrl_keygen_pwm_a_write_immediate_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_eventually_left_p);


property ctrl_keygen_pwm_a_write_immediate_msg_done_eventually_left_p;
  keygen_pwm_a_write_immediate_msg_done
|->
  s_eventually(!keygen_pwm_a_write_immediate_msg_done);
endproperty
ctrl_keygen_pwm_a_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_write_immediate_msg_done_eventually_left_p);


property ctrl_keygen_pwm_a_rejection_sampling_start_eventually_left_p;
  keygen_pwm_a_rejection_sampling_start
|->
  s_eventually(!keygen_pwm_a_rejection_sampling_start);
endproperty
ctrl_keygen_pwm_a_rejection_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_rejection_sampling_start_eventually_left_p);


property ctrl_keygen_pwm_a_start_eventually_left_p;
  keygen_pwm_a_start
|->
  s_eventually(!keygen_pwm_a_start);
endproperty
ctrl_keygen_pwm_a_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_start_eventually_left_p);


property ctrl_keygen_pwm_a_eventually_left_p;
  keygen_pwm_a
|->
  s_eventually(!keygen_pwm_a);
endproperty
ctrl_keygen_pwm_a_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_pwm_a_eventually_left_p);


property ctrl_keygen_intt_a_idle_eventually_left_p;
  keygen_intt_a_idle
|->
  s_eventually(!keygen_intt_a_idle);
endproperty
ctrl_keygen_intt_a_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_idle_eventually_left_p);


property ctrl_keygen_intt_a_start_eventually_left_p;
  keygen_intt_a_start
|->
  s_eventually(!keygen_intt_a_start);
endproperty
ctrl_keygen_intt_a_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_start_eventually_left_p);


property ctrl_keygen_intt_a_eventually_left_p;
  keygen_intt_a
|->
  s_eventually(!keygen_intt_a);
endproperty
ctrl_keygen_intt_a_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_intt_a_eventually_left_p);


property ctrl_keygen_compute_t_start_eventually_left_p;
  keygen_compute_t_start
|->
  s_eventually(!keygen_compute_t_start);
endproperty
ctrl_keygen_compute_t_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_start_eventually_left_p);


property ctrl_keygen_compute_t_eventually_left_p;
  keygen_compute_t
|->
  s_eventually(!keygen_compute_t);
endproperty
ctrl_keygen_compute_t_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_t_eventually_left_p);


property ctrl_keygen_power_2_round_start_eventually_left_p;
  keygen_power_2_round_start
|->
  s_eventually(!keygen_power_2_round_start);
endproperty
ctrl_keygen_power_2_round_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_power_2_round_start_eventually_left_p);


property ctrl_keygen_power_2_round_eventually_left_p;
  keygen_power_2_round
|->
  s_eventually(!keygen_power_2_round);
endproperty
ctrl_keygen_power_2_round_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_power_2_round_eventually_left_p);


property ctrl_keygen_compute_tr_write_pk_SHA3_START_eventually_left_p;
  keygen_compute_tr_write_pk_SHA3_START
|->
  s_eventually(!keygen_compute_tr_write_pk_SHA3_START);
endproperty
ctrl_keygen_compute_tr_write_pk_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_SHA3_START_eventually_left_p);


property ctrl_keygen_compute_tr_write_pk_start_eventually_left_p;
  keygen_compute_tr_write_pk_start
|->
  s_eventually(!keygen_compute_tr_write_pk_start);
endproperty
ctrl_keygen_compute_tr_write_pk_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_start_eventually_left_p);


property ctrl_keygen_compute_tr_write_pk_eventually_left_p;
  keygen_compute_tr_write_pk
|->
  s_eventually(!keygen_compute_tr_write_pk);
endproperty
ctrl_keygen_compute_tr_write_pk_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_eventually_left_p);


property ctrl_keygen_compute_tr_write_pk_msg_done_eventually_left_p;
  keygen_compute_tr_write_pk_msg_done
|->
  s_eventually(!keygen_compute_tr_write_pk_msg_done);
endproperty
ctrl_keygen_compute_tr_write_pk_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_write_pk_msg_done_eventually_left_p);


property ctrl_keygen_compute_tr_sampling_start_eventually_left_p;
  keygen_compute_tr_sampling_start
|->
  s_eventually(!keygen_compute_tr_sampling_start);
endproperty
ctrl_keygen_compute_tr_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_sampling_start_eventually_left_p);


property ctrl_keygen_compute_tr_sampling_eventually_left_p;
  keygen_compute_tr_sampling
|->
  s_eventually(!keygen_compute_tr_sampling);
endproperty
ctrl_keygen_compute_tr_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_compute_tr_sampling_eventually_left_p);


property ctrl_keygen_sk_encode_start_eventually_left_p;
  keygen_sk_encode_start
|->
  s_eventually(!keygen_sk_encode_start);
endproperty
ctrl_keygen_sk_encode_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sk_encode_start_eventually_left_p);


property ctrl_keygen_sk_encode_eventually_left_p;
  keygen_sk_encode
|->
  s_eventually(!keygen_sk_encode);
endproperty
ctrl_keygen_sk_encode_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_sk_encode_eventually_left_p);


property ctrl_keygen_jump_sign_eventually_left_p;
  keygen_jump_sign
|->
  s_eventually(!keygen_jump_sign);
endproperty
ctrl_keygen_jump_sign_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_jump_sign_eventually_left_p);


property ctrl_keygen_end_state_eventually_left_p;
  keygen_end_state
|->
  s_eventually(!keygen_end_state);
endproperty
ctrl_keygen_end_state_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_keygen_end_state_eventually_left_p);


property ctrl_sign_rnd_seed_SHA3_START_eventually_left_p;
  sign_rnd_seed_SHA3_START
|->
  s_eventually(!sign_rnd_seed_SHA3_START);
endproperty
ctrl_sign_rnd_seed_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_SHA3_START_eventually_left_p);


property ctrl_sign_rnd_seed_start_eventually_left_p;
  sign_rnd_seed_start
|->
  s_eventually(!sign_rnd_seed_start);
endproperty
ctrl_sign_rnd_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_start_eventually_left_p);


property ctrl_sign_write_entropy_eventually_left_p;
  sign_write_entropy
|->
  s_eventually(!sign_write_entropy);
endproperty
ctrl_sign_write_entropy_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_eventually_left_p);


property ctrl_sign_write_entropy_msg_done_eventually_left_p;
  sign_write_entropy_msg_done
|->
  s_eventually(!sign_write_entropy_msg_done);
endproperty
ctrl_sign_write_entropy_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_entropy_msg_done_eventually_left_p);


property ctrl_sign_rnd_seed_wait_eventually_left_p;
  sign_rnd_seed_wait
|->
  s_eventually(!sign_rnd_seed_wait);
endproperty
ctrl_sign_rnd_seed_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_wait_eventually_left_p);


property ctrl_sign_write_counter_eventually_left_p;
  sign_write_counter
|->
  s_eventually(!sign_write_counter);
endproperty
ctrl_sign_write_counter_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_eventually_left_p);


property ctrl_sign_write_counter_msg_done_eventually_left_p;
  sign_write_counter_msg_done
|->
  s_eventually(!sign_write_counter_msg_done);
endproperty
ctrl_sign_write_counter_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_write_counter_msg_done_eventually_left_p);


property ctrl_sign_sample_rnd_seed_start_eventually_left_p;
  sign_sample_rnd_seed_start
|->
  s_eventually(!sign_sample_rnd_seed_start);
endproperty
ctrl_sign_sample_rnd_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_rnd_seed_start_eventually_left_p);


property ctrl_sign_sample_rnd_seed_eventually_left_p;
  sign_sample_rnd_seed
|->
  s_eventually(!sign_sample_rnd_seed);
endproperty
ctrl_sign_sample_rnd_seed_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_rnd_seed_eventually_left_p);


property ctrl_sign_rnd_seed_lfsr_eventually_left_p;
  sign_rnd_seed_lfsr
|->
  s_eventually(!sign_rnd_seed_lfsr);
endproperty
ctrl_sign_rnd_seed_lfsr_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_rnd_seed_lfsr_eventually_left_p);


property ctrl_sign_check_mode_eventually_left_p;
  sign_check_mode
|->
  s_eventually(!sign_check_mode);
endproperty
ctrl_sign_check_mode_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_check_mode_eventually_left_p);

property ctrl_sign_compute_mu_idle_eventually_left_p;
  sign_compute_mu_idle
|->
  s_eventually(!sign_compute_mu_idle);
endproperty
ctrl_sign_compute_mu_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_idle_eventually_left_p);


property ctrl_sign_compute_mu_SHA3_START_eventually_left_p;
  sign_compute_mu_SHA3_START
|->
  s_eventually(!sign_compute_mu_SHA3_START);
endproperty
ctrl_sign_compute_mu_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_SHA3_START_eventually_left_p);


property ctrl_sign_compute_mu_start_eventually_left_p;
  sign_compute_mu_start
|->
  s_eventually(!sign_compute_mu_start);
endproperty
ctrl_sign_compute_mu_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_start_eventually_left_p);


property ctrl_sign_compute_mu_write_tr_eventually_left_p;
  sign_compute_mu_write_tr
|->
  s_eventually(!sign_compute_mu_write_tr);
endproperty
ctrl_sign_compute_mu_write_tr_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_eventually_left_p);


property ctrl_sign_compute_mu_write_tr_msg_done_eventually_left_p;
  sign_compute_mu_write_tr_msg_done
|->
  s_eventually(!sign_compute_mu_write_tr_msg_done);
endproperty
ctrl_sign_compute_mu_write_tr_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_tr_msg_done_eventually_left_p);


property ctrl_sign_compute_mu_wait_eventually_left_p;
  sign_compute_mu_wait
|->
  s_eventually(!sign_compute_mu_wait);
endproperty
ctrl_sign_compute_mu_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_wait_eventually_left_p);


property ctrl_sign_compute_mu_write_msg_prime_eventually_left_p;
  sign_compute_mu_write_msg_prime
|->
  s_eventually(!sign_compute_mu_write_msg_prime);
endproperty
ctrl_sign_compute_mu_write_msg_prime_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_eventually_left_p);


property ctrl_sign_compute_mu_write_msg_prime_msg_done_eventually_left_p;
  sign_compute_mu_write_msg_prime_msg_done
|->
  s_eventually(!sign_compute_mu_write_msg_prime_msg_done);
endproperty
ctrl_sign_compute_mu_write_msg_prime_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_write_msg_prime_msg_done_eventually_left_p);


property ctrl_sign_compute_mu_sampling_start_eventually_left_p;
  sign_compute_mu_sampling_start
|->
  s_eventually(!sign_compute_mu_sampling_start);
endproperty
ctrl_sign_compute_mu_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_sampling_start_eventually_left_p);


property ctrl_sign_compute_mu_sampling_eventually_left_p;
  sign_compute_mu_sampling
|->
  s_eventually(!sign_compute_mu_sampling);
endproperty
ctrl_sign_compute_mu_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_mu_sampling_eventually_left_p);


property ctrl_sign_compute_rho_prime_SHA3_START_eventually_left_p;
  sign_compute_rho_prime_SHA3_START
|->
  s_eventually(!sign_compute_rho_prime_SHA3_START);
endproperty
ctrl_sign_compute_rho_prime_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_SHA3_START_eventually_left_p);


property ctrl_sign_compute_rho_prime_start_eventually_left_p;
  sign_compute_rho_prime_start
|->
  s_eventually(!sign_compute_rho_prime_start);
endproperty
ctrl_sign_compute_rho_prime_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_start_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_K_eventually_left_p;
  sign_compute_rho_prime_write_K
|->
  s_eventually(!sign_compute_rho_prime_write_K);
endproperty
ctrl_sign_compute_rho_prime_write_K_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_K_msg_done_eventually_left_p;
  sign_compute_rho_prime_write_K_msg_done
|->
  s_eventually(!sign_compute_rho_prime_write_K_msg_done);
endproperty
ctrl_sign_compute_rho_prime_write_K_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_K_msg_done_eventually_left_p);


property ctrl_sign_compute_rho_prime_wait_0_eventually_left_p;
  sign_compute_rho_prime_wait_0
|->
  s_eventually(!sign_compute_rho_prime_wait_0);
endproperty
ctrl_sign_compute_rho_prime_wait_0_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_wait_0_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_eventually_left_p;
  sign_compute_rho_prime_write_sign_rnd
|->
  s_eventually(!sign_compute_rho_prime_write_sign_rnd);
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_eventually_left_p;
  sign_compute_rho_prime_write_sign_rnd_msg_done
|->
  s_eventually(!sign_compute_rho_prime_write_sign_rnd_msg_done);
endproperty
ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_sign_rnd_msg_done_eventually_left_p);


property ctrl_sign_compute_rho_prime_wait_1_eventually_left_p;
  sign_compute_rho_prime_wait_1
|->
  s_eventually(!sign_compute_rho_prime_wait_1);
endproperty
ctrl_sign_compute_rho_prime_wait_1_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_wait_1_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_mu_eventually_left_p;
  sign_compute_rho_prime_write_mu
|->
  s_eventually(!sign_compute_rho_prime_write_mu);
endproperty
ctrl_sign_compute_rho_prime_write_mu_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_eventually_left_p);


property ctrl_sign_compute_rho_prime_write_mu_msg_done_eventually_left_p;
  sign_compute_rho_prime_write_mu_msg_done
|->
  s_eventually(!sign_compute_rho_prime_write_mu_msg_done);
endproperty
ctrl_sign_compute_rho_prime_write_mu_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_write_mu_msg_done_eventually_left_p);


property ctrl_sign_compute_rho_prime_sampling_start_eventually_left_p;
  sign_compute_rho_prime_sampling_start
|->
  s_eventually(!sign_compute_rho_prime_sampling_start);
endproperty
ctrl_sign_compute_rho_prime_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_sampling_start_eventually_left_p);


property ctrl_sign_compute_rho_prime_sampling_eventually_left_p;
  sign_compute_rho_prime_sampling
|->
  s_eventually(!sign_compute_rho_prime_sampling);
endproperty
ctrl_sign_compute_rho_prime_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_rho_prime_sampling_eventually_left_p);


property ctrl_sign_wait_for_y_and_w0_clear_eventually_left_p;
  sign_wait_for_y_and_w0_clear
|->
  s_eventually(!sign_wait_for_y_and_w0_clear);
endproperty
ctrl_sign_wait_for_y_and_w0_clear_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_y_and_w0_clear_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_SHA3_START_eventually_left_p;
  sign_compute_lfsr_seed_SHA3_START
|->
  s_eventually(!sign_compute_lfsr_seed_SHA3_START);
endproperty
ctrl_sign_compute_lfsr_seed_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_SHA3_START_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_start_eventually_left_p;
  sign_compute_lfsr_seed_start
|->
  s_eventually(!sign_compute_lfsr_seed_start);
endproperty
ctrl_sign_compute_lfsr_seed_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_start_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_eventually_left_p;
  sign_compute_lfsr_seed_write_entropy
|->
  s_eventually(!sign_compute_lfsr_seed_write_entropy);
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_eventually_left_p;
  sign_compute_lfsr_seed_write_entropy_msg_done
|->
  s_eventually(!sign_compute_lfsr_seed_write_entropy_msg_done);
endproperty
ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_entropy_msg_done_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_wait_eventually_left_p;
  sign_compute_lfsr_seed_wait
|->
  s_eventually(!sign_compute_lfsr_seed_wait);
endproperty
ctrl_sign_compute_lfsr_seed_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_wait_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_write_counter_eventually_left_p;
  sign_compute_lfsr_seed_write_counter
|->
  s_eventually(!sign_compute_lfsr_seed_write_counter);
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_write_counter_msg_done_eventually_left_p;
  sign_compute_lfsr_seed_write_counter_msg_done
|->
  s_eventually(!sign_compute_lfsr_seed_write_counter_msg_done);
endproperty
ctrl_sign_compute_lfsr_seed_write_counter_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_write_counter_msg_done_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_sampling_start_eventually_left_p;
  sign_compute_lfsr_seed_sampling_start
|->
  s_eventually(!sign_compute_lfsr_seed_sampling_start);
endproperty
ctrl_sign_compute_lfsr_seed_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_sampling_start_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_sampling_eventually_left_p;
  sign_compute_lfsr_seed_sampling
|->
  s_eventually(!sign_compute_lfsr_seed_sampling);
endproperty
ctrl_sign_compute_lfsr_seed_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_sampling_eventually_left_p);


property ctrl_sign_compute_lfsr_seed_lfsr_eventually_left_p;
  sign_compute_lfsr_seed_lfsr
|->
  s_eventually(!sign_compute_lfsr_seed_lfsr);
endproperty
ctrl_sign_compute_lfsr_seed_lfsr_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_lfsr_seed_lfsr_eventually_left_p);


property ctrl_sign_expand_mask_done_eventually_left_p;
  sign_expand_mask_done
|->
  s_eventually(!sign_expand_mask_done);
endproperty
ctrl_sign_expand_mask_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_done_eventually_left_p);


property ctrl_sign_expand_mask_SHA3_START_eventually_left_p;
  sign_expand_mask_SHA3_START
|->
  s_eventually(!sign_expand_mask_SHA3_START);
endproperty
ctrl_sign_expand_mask_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_SHA3_START_eventually_left_p);


property ctrl_sign_expand_mask_start_eventually_left_p;
  sign_expand_mask_start
|->
  s_eventually(!sign_expand_mask_start);
endproperty
ctrl_sign_expand_mask_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_start_eventually_left_p);


property ctrl_sign_expand_mask_write_rho_prime_eventually_left_p;
  sign_expand_mask_write_rho_prime
|->
  s_eventually(!sign_expand_mask_write_rho_prime);
endproperty
ctrl_sign_expand_mask_write_rho_prime_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_rho_prime_eventually_left_p);


property ctrl_sign_expand_mask_write_kappa_immediate_eventually_left_p;
  sign_expand_mask_write_kappa_immediate
|->
  s_eventually(!sign_expand_mask_write_kappa_immediate);
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_eventually_left_p);


property ctrl_sign_expand_mask_write_kappa_immediate_msg_done_eventually_left_p;
  sign_expand_mask_write_kappa_immediate_msg_done
|->
  s_eventually(!sign_expand_mask_write_kappa_immediate_msg_done);
endproperty
ctrl_sign_expand_mask_write_kappa_immediate_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_write_kappa_immediate_msg_done_eventually_left_p);


property ctrl_sign_expand_mask_sampling_start_eventually_left_p;
  sign_expand_mask_sampling_start
|->
  s_eventually(!sign_expand_mask_sampling_start);
endproperty
ctrl_sign_expand_mask_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_start_eventually_left_p);


property ctrl_sign_expand_mask_sampling_eventually_left_p;
  sign_expand_mask_sampling
|->
  s_eventually(!sign_expand_mask_sampling);
endproperty
ctrl_sign_expand_mask_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_expand_mask_sampling_eventually_left_p);


property ctrl_sign_ntt_y_idle_eventually_left_p;
  sign_ntt_y_idle
|->
  s_eventually(!sign_ntt_y_idle);
endproperty
ctrl_sign_ntt_y_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_idle_eventually_left_p);


property ctrl_sign_ntt_y_start_eventually_left_p;
  sign_ntt_y_start
|->
  s_eventually(!sign_ntt_y_start);
endproperty
ctrl_sign_ntt_y_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_start_eventually_left_p);


property ctrl_sign_ntt_y_eventually_left_p;
  sign_ntt_y
|->
  s_eventually(!sign_ntt_y);
endproperty
ctrl_sign_ntt_y_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_ntt_y_eventually_left_p);


property ctrl_sign_wait_for_w0_clear_eventually_left_p;
  sign_wait_for_w0_clear
|->
  s_eventually(!sign_wait_for_w0_clear);
endproperty
ctrl_sign_wait_for_w0_clear_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_w0_clear_eventually_left_p);


property ctrl_sign_compute_w0_pwm_SHA3_START_eventually_left_p;
  sign_compute_w0_pwm_SHA3_START
|->
  s_eventually(!sign_compute_w0_pwm_SHA3_START);
endproperty
ctrl_sign_compute_w0_pwm_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_SHA3_START_eventually_left_p);


property ctrl_sign_compute_w0_pwm_start_eventually_left_p;
  sign_compute_w0_pwm_start
|->
  s_eventually(!sign_compute_w0_pwm_start);
endproperty
ctrl_sign_compute_w0_pwm_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_start_eventually_left_p);


property ctrl_sign_compute_w0_pwm_write_rho_eventually_left_p;
  sign_compute_w0_pwm_write_rho
|->
  s_eventually(!sign_compute_w0_pwm_write_rho);
endproperty
ctrl_sign_compute_w0_pwm_write_rho_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_rho_eventually_left_p);


property ctrl_sign_compute_w0_pwm_write_immediate_eventually_left_p;
  sign_compute_w0_pwm_write_immediate
|->
  s_eventually(!sign_compute_w0_pwm_write_immediate);
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_eventually_left_p);


property ctrl_sign_compute_w0_pwm_write_immediate_msg_done_eventually_left_p;
  sign_compute_w0_pwm_write_immediate_msg_done
|->
  s_eventually(!sign_compute_w0_pwm_write_immediate_msg_done);
endproperty
ctrl_sign_compute_w0_pwm_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_write_immediate_msg_done_eventually_left_p);


property ctrl_sign_compute_w0_pwm_sampling_start_eventually_left_p;
  sign_compute_w0_pwm_sampling_start
|->
  s_eventually(!sign_compute_w0_pwm_sampling_start);
endproperty
ctrl_sign_compute_w0_pwm_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_sampling_start_eventually_left_p);


property ctrl_sign_compute_w0_pwm_samp_ntt_eventually_left_p;
  sign_compute_w0_pwm_samp_ntt
|->
  s_eventually(!sign_compute_w0_pwm_samp_ntt);
endproperty
ctrl_sign_compute_w0_pwm_samp_ntt_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_samp_ntt_eventually_left_p);


property ctrl_sign_compute_w0_pwm_eventually_left_p;
  sign_compute_w0_pwm
|->
  s_eventually(!sign_compute_w0_pwm);
endproperty
ctrl_sign_compute_w0_pwm_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_pwm_eventually_left_p);


property ctrl_sign_compute_w0_intt_idle_eventually_left_p;
  sign_compute_w0_intt_idle
|->
  s_eventually(!sign_compute_w0_intt_idle);
endproperty
ctrl_sign_compute_w0_intt_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_idle_eventually_left_p);


property ctrl_sign_compute_w0_intt_start_eventually_left_p;
  sign_compute_w0_intt_start
|->
  s_eventually(!sign_compute_w0_intt_start);
endproperty
ctrl_sign_compute_w0_intt_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_start_eventually_left_p);


property ctrl_sign_compute_w0_intt_eventually_left_p;
  sign_compute_w0_intt
|->
  s_eventually(!sign_compute_w0_intt);
endproperty
ctrl_sign_compute_w0_intt_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_w0_intt_eventually_left_p);


property ctrl_sign_set_y_valid_eventually_left_p;
  sign_set_y_valid
|->
  s_eventually(!sign_set_y_valid);
endproperty
ctrl_sign_set_y_valid_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_y_valid_eventually_left_p);


property ctrl_sign_load_mu_idle_eventually_left_p;
  sign_load_mu_idle
|->
  s_eventually(!sign_load_mu_idle);
endproperty
ctrl_sign_load_mu_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_idle_eventually_left_p);


property ctrl_sign_load_mu_SHA3_START_eventually_left_p;
  sign_load_mu_SHA3_START
|->
  s_eventually(!sign_load_mu_SHA3_START);
endproperty
ctrl_sign_load_mu_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_SHA3_START_eventually_left_p);


property ctrl_sign_load_mu_start_eventually_left_p;
  sign_load_mu_start
|->
  s_eventually(!sign_load_mu_start);
endproperty
ctrl_sign_load_mu_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_start_eventually_left_p);


property ctrl_sign_load_mu_eventually_left_p;
  sign_load_mu
|->
  s_eventually(!sign_load_mu);
endproperty
ctrl_sign_load_mu_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_eventually_left_p);


property ctrl_sign_load_mu_msg_done_eventually_left_p;
  sign_load_mu_msg_done
|->
  s_eventually(!sign_load_mu_msg_done);
endproperty
ctrl_sign_load_mu_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_msg_done_eventually_left_p);


property ctrl_sign_load_mu_wait_eventually_left_p;
  sign_load_mu_wait
|->
  s_eventually(!sign_load_mu_wait);
endproperty
ctrl_sign_load_mu_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_load_mu_wait_eventually_left_p);


property ctrl_sign_decompose_w_start_eventually_left_p;
  sign_decompose_w_start
|->
  s_eventually(!sign_decompose_w_start);
endproperty
ctrl_sign_decompose_w_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_decompose_w_start_eventually_left_p);


property ctrl_sign_decompose_w_eventually_left_p;
  sign_decompose_w
|->
  s_eventually(!sign_decompose_w);
endproperty
ctrl_sign_decompose_w_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_decompose_w_eventually_left_p);


property ctrl_sign_set_w0_valid_eventually_left_p;
  sign_set_w0_valid
|->
  s_eventually(!sign_set_w0_valid);
endproperty
ctrl_sign_set_w0_valid_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_w0_valid_eventually_left_p);


property ctrl_sign_wait_for_c_clear_eventually_left_p;
  sign_wait_for_c_clear
|->
  s_eventually(!sign_wait_for_c_clear);
endproperty
ctrl_sign_wait_for_c_clear_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_wait_for_c_clear_eventually_left_p);


property ctrl_sign_compute_c_start_eventually_left_p;
  sign_compute_c_start
|->
  s_eventually(!sign_compute_c_start);
endproperty
ctrl_sign_compute_c_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_c_start_eventually_left_p);


property ctrl_sign_compute_c_eventually_left_p;
  sign_compute_c
|->
  s_eventually(!sign_compute_c);
endproperty
ctrl_sign_compute_c_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_compute_c_eventually_left_p);


property ctrl_sign_sample_in_ball_SHA3_START_eventually_left_p;
  sign_sample_in_ball_SHA3_START
|->
  s_eventually(!sign_sample_in_ball_SHA3_START);
endproperty
ctrl_sign_sample_in_ball_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_SHA3_START_eventually_left_p);


property ctrl_sign_sample_in_ball_start_eventually_left_p;
  sign_sample_in_ball_start
|->
  s_eventually(!sign_sample_in_ball_start);
endproperty
ctrl_sign_sample_in_ball_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_start_eventually_left_p);


property ctrl_sign_sample_in_ball_write_c_eventually_left_p;
  sign_sample_in_ball_write_c
|->
  s_eventually(!sign_sample_in_ball_write_c);
endproperty
ctrl_sign_sample_in_ball_write_c_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_eventually_left_p);


property ctrl_sign_sample_in_ball_write_c_msg_done_eventually_left_p;
  sign_sample_in_ball_write_c_msg_done
|->
  s_eventually(!sign_sample_in_ball_write_c_msg_done);
endproperty
ctrl_sign_sample_in_ball_write_c_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_write_c_msg_done_eventually_left_p);


property ctrl_sign_sample_in_ball_sampling_start_eventually_left_p;
  sign_sample_in_ball_sampling_start
|->
  s_eventually(!sign_sample_in_ball_sampling_start);
endproperty
ctrl_sign_sample_in_ball_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_sampling_start_eventually_left_p);


property ctrl_sign_sample_in_ball_sampling_eventually_left_p;
  sign_sample_in_ball_sampling
|->
  s_eventually(!sign_sample_in_ball_sampling);
endproperty
ctrl_sign_sample_in_ball_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_sample_in_ball_sampling_eventually_left_p);


property ctrl_sign_set_c_valid_eventually_left_p;
  sign_set_c_valid
|->
  s_eventually(!sign_set_c_valid);
endproperty
ctrl_sign_set_c_valid_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_set_c_valid_eventually_left_p);


property ctrl_sign_end_of_challenge_eventually_left_p;
  sign_end_of_challenge
|->
  s_eventually(!sign_end_of_challenge);
endproperty
ctrl_sign_end_of_challenge_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_of_challenge_eventually_left_p);


property ctrl_sign_end_state_eventually_left_p;
  sign_end_state
|->
  s_eventually(!sign_end_state);
endproperty
ctrl_sign_end_state_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_sign_end_state_eventually_left_p);


property ctrl_verify_pk_decode_start_eventually_left_p;
  verify_pk_decode_start
|->
  s_eventually(!verify_pk_decode_start);
endproperty
ctrl_verify_pk_decode_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_pk_decode_start_eventually_left_p);


property ctrl_verify_pk_decode_eventually_left_p;
  verify_pk_decode
|->
  s_eventually(!verify_pk_decode);
endproperty
ctrl_verify_pk_decode_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_pk_decode_eventually_left_p);


property ctrl_verify_sig_decode_z_start_eventually_left_p;
  verify_sig_decode_z_start
|->
  s_eventually(!verify_sig_decode_z_start);
endproperty
ctrl_verify_sig_decode_z_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_z_start_eventually_left_p);


property ctrl_verify_sig_decode_z_eventually_left_p;
  verify_sig_decode_z
|->
  s_eventually(!verify_sig_decode_z);
endproperty
ctrl_verify_sig_decode_z_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_z_eventually_left_p);


property ctrl_verify_norm_check_start_eventually_left_p;
  verify_norm_check_start
|->
  s_eventually(!verify_norm_check_start);
endproperty
ctrl_verify_norm_check_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_start_eventually_left_p);


property ctrl_verify_norm_check_eventually_left_p;
  verify_norm_check
|->
  s_eventually(!verify_norm_check);
endproperty
ctrl_verify_norm_check_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_norm_check_eventually_left_p);


property ctrl_verify_compute_tr_SHA3_START_eventually_left_p;
  verify_compute_tr_SHA3_START
|->
  s_eventually(!verify_compute_tr_SHA3_START);
endproperty
ctrl_verify_compute_tr_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_SHA3_START_eventually_left_p);


property ctrl_verify_compute_tr_start_eventually_left_p;
  verify_compute_tr_start
|->
  s_eventually(!verify_compute_tr_start);
endproperty
ctrl_verify_compute_tr_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_start_eventually_left_p);


property ctrl_verify_compute_tr_write_pk_eventually_left_p;
  verify_compute_tr_write_pk
|->
  s_eventually(!verify_compute_tr_write_pk);
endproperty
ctrl_verify_compute_tr_write_pk_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_eventually_left_p);


property ctrl_verify_compute_tr_write_pk_msg_done_eventually_left_p;
  verify_compute_tr_write_pk_msg_done
|->
  s_eventually(!verify_compute_tr_write_pk_msg_done);
endproperty
ctrl_verify_compute_tr_write_pk_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_write_pk_msg_done_eventually_left_p);


property ctrl_verify_compute_tr_sampling_start_eventually_left_p;
  verify_compute_tr_sampling_start
|->
  s_eventually(!verify_compute_tr_sampling_start);
endproperty
ctrl_verify_compute_tr_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_start_eventually_left_p);


property ctrl_verify_compute_tr_sampling_eventually_left_p;
  verify_compute_tr_sampling
|->
  s_eventually(!verify_compute_tr_sampling);
endproperty
ctrl_verify_compute_tr_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_tr_sampling_eventually_left_p);


property ctrl_verify_check_mode_eventually_left_p;
  verify_check_mode
|->
  s_eventually(!verify_check_mode);
endproperty
ctrl_verify_check_mode_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_check_mode_eventually_left_p);


property ctrl_verify_compute_mu_SHA3_START_eventually_left_p;
  verify_compute_mu_SHA3_START
|->
  s_eventually(!verify_compute_mu_SHA3_START);
endproperty
ctrl_verify_compute_mu_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_SHA3_START_eventually_left_p);


property ctrl_verify_compute_mu_start_eventually_left_p;
  verify_compute_mu_start
|->
  s_eventually(!verify_compute_mu_start);
endproperty
ctrl_verify_compute_mu_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_start_eventually_left_p);


property ctrl_verify_compute_mu_write_tr_eventually_left_p;
  verify_compute_mu_write_tr
|->
  s_eventually(!verify_compute_mu_write_tr);
endproperty
ctrl_verify_compute_mu_write_tr_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_eventually_left_p);


property ctrl_verify_compute_mu_write_tr_msg_done_eventually_left_p;
  verify_compute_mu_write_tr_msg_done
|->
  s_eventually(!verify_compute_mu_write_tr_msg_done);
endproperty
ctrl_verify_compute_mu_write_tr_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_tr_msg_done_eventually_left_p);


property ctrl_verify_compute_mu_wait_eventually_left_p;
  verify_compute_mu_wait
|->
  s_eventually(!verify_compute_mu_wait);
endproperty
ctrl_verify_compute_mu_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_wait_eventually_left_p);


property ctrl_verify_compute_mu_write_msg_prime_eventually_left_p;
  verify_compute_mu_write_msg_prime
|->
  s_eventually(!verify_compute_mu_write_msg_prime);
endproperty
ctrl_verify_compute_mu_write_msg_prime_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_eventually_left_p);


property ctrl_verify_compute_mu_write_msg_prime_msg_done_eventually_left_p;
  verify_compute_mu_write_msg_prime_msg_done
|->
  s_eventually(!verify_compute_mu_write_msg_prime_msg_done);
endproperty
ctrl_verify_compute_mu_write_msg_prime_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_write_msg_prime_msg_done_eventually_left_p);


property ctrl_verify_compute_mu_sampling_start_eventually_left_p;
  verify_compute_mu_sampling_start
|->
  s_eventually(!verify_compute_mu_sampling_start);
endproperty
ctrl_verify_compute_mu_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_sampling_start_eventually_left_p);


property ctrl_verify_compute_mu_sampling_eventually_left_p;
  verify_compute_mu_sampling
|->
  s_eventually(!verify_compute_mu_sampling);
endproperty
ctrl_verify_compute_mu_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_mu_sampling_eventually_left_p);


property ctrl_verify_sample_in_ball_SHA3_START_eventually_left_p;
  verify_sample_in_ball_SHA3_START
|->
  s_eventually(!verify_sample_in_ball_SHA3_START);
endproperty
ctrl_verify_sample_in_ball_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_SHA3_START_eventually_left_p);


property ctrl_verify_sample_in_ball_start_eventually_left_p;
  verify_sample_in_ball_start
|->
  s_eventually(!verify_sample_in_ball_start);
endproperty
ctrl_verify_sample_in_ball_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_start_eventually_left_p);


property ctrl_verify_sample_in_ball_write_c_eventually_left_p;
  verify_sample_in_ball_write_c
|->
  s_eventually(!verify_sample_in_ball_write_c);
endproperty
ctrl_verify_sample_in_ball_write_c_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_eventually_left_p);


property ctrl_verify_sample_in_ball_write_c_msg_done_eventually_left_p;
  verify_sample_in_ball_write_c_msg_done
|->
  s_eventually(!verify_sample_in_ball_write_c_msg_done);
endproperty
ctrl_verify_sample_in_ball_write_c_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_write_c_msg_done_eventually_left_p);


property ctrl_verify_sample_in_ball_sampling_start_eventually_left_p;
  verify_sample_in_ball_sampling_start
|->
  s_eventually(!verify_sample_in_ball_sampling_start);
endproperty
ctrl_verify_sample_in_ball_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_sampling_start_eventually_left_p);


property ctrl_verify_sample_in_ball_sampling_eventually_left_p;
  verify_sample_in_ball_sampling
|->
  s_eventually(!verify_sample_in_ball_sampling);
endproperty
ctrl_verify_sample_in_ball_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sample_in_ball_sampling_eventually_left_p);


property ctrl_verify_ntt_c_start_eventually_left_p;
  verify_ntt_c_start
|->
  s_eventually(!verify_ntt_c_start);
endproperty
ctrl_verify_ntt_c_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_c_start_eventually_left_p);


property ctrl_verify_ntt_c_eventually_left_p;
  verify_ntt_c
|->
  s_eventually(!verify_ntt_c);
endproperty
ctrl_verify_ntt_c_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_c_eventually_left_p);


property ctrl_verify_ntt_t_start_eventually_left_p;
  verify_ntt_t_start
|->
  s_eventually(!verify_ntt_t_start);
endproperty
ctrl_verify_ntt_t_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_start_eventually_left_p);


property ctrl_verify_ntt_t_eventually_left_p;
  verify_ntt_t
|->
  s_eventually(!verify_ntt_t);
endproperty
ctrl_verify_ntt_t_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_t_eventually_left_p);


property ctrl_verify_ntt_z_start_eventually_left_p;
  verify_ntt_z_start
|->
  s_eventually(!verify_ntt_z_start);
endproperty
ctrl_verify_ntt_z_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_start_eventually_left_p);


property ctrl_verify_ntt_z_eventually_left_p;
  verify_ntt_z
|->
  s_eventually(!verify_ntt_z);
endproperty
ctrl_verify_ntt_z_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_ntt_z_eventually_left_p);


property ctrl_verify_compute_az_SHA3_START_eventually_left_p;
  verify_compute_az_SHA3_START
|->
  s_eventually(!verify_compute_az_SHA3_START);
endproperty
ctrl_verify_compute_az_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_SHA3_START_eventually_left_p);


property ctrl_verify_compute_az_start_eventually_left_p;
  verify_compute_az_start
|->
  s_eventually(!verify_compute_az_start);
endproperty
ctrl_verify_compute_az_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_start_eventually_left_p);


property ctrl_verify_compute_az_write_rho_eventually_left_p;
  verify_compute_az_write_rho
|->
  s_eventually(!verify_compute_az_write_rho);
endproperty
ctrl_verify_compute_az_write_rho_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_rho_eventually_left_p);


property ctrl_verify_compute_az_write_immediate_eventually_left_p;
  verify_compute_az_write_immediate
|->
  s_eventually(!verify_compute_az_write_immediate);
endproperty
ctrl_verify_compute_az_write_immediate_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_eventually_left_p);


property ctrl_verify_compute_az_write_immediate_msg_done_eventually_left_p;
  verify_compute_az_write_immediate_msg_done
|->
  s_eventually(!verify_compute_az_write_immediate_msg_done);
endproperty
ctrl_verify_compute_az_write_immediate_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_write_immediate_msg_done_eventually_left_p);


property ctrl_verify_compute_az_sampling_start_eventually_left_p;
  verify_compute_az_sampling_start
|->
  s_eventually(!verify_compute_az_sampling_start);
endproperty
ctrl_verify_compute_az_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_sampling_start_eventually_left_p);


property ctrl_verify_compute_az_pwm_start_eventually_left_p;
  verify_compute_az_pwm_start
|->
  s_eventually(!verify_compute_az_pwm_start);
endproperty
ctrl_verify_compute_az_pwm_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_start_eventually_left_p);


property ctrl_verify_compute_az_pwm_eventually_left_p;
  verify_compute_az_pwm
|->
  s_eventually(!verify_compute_az_pwm);
endproperty
ctrl_verify_compute_az_pwm_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_az_pwm_eventually_left_p);


property ctrl_verify_compute_w0_pwm_start_eventually_left_p;
  verify_compute_w0_pwm_start
|->
  s_eventually(!verify_compute_w0_pwm_start);
endproperty
ctrl_verify_compute_w0_pwm_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pwm_start_eventually_left_p);


property ctrl_verify_compute_w0_pwm_eventually_left_p;
  verify_compute_w0_pwm
|->
  s_eventually(!verify_compute_w0_pwm);
endproperty
ctrl_verify_compute_w0_pwm_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pwm_eventually_left_p);


property ctrl_verify_compute_w0_pws_start_eventually_left_p;
  verify_compute_w0_pws_start
|->
  s_eventually(!verify_compute_w0_pws_start);
endproperty
ctrl_verify_compute_w0_pws_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pws_start_eventually_left_p);


property ctrl_verify_compute_w0_pws_eventually_left_p;
  verify_compute_w0_pws
|->
  s_eventually(!verify_compute_w0_pws);
endproperty
ctrl_verify_compute_w0_pws_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_pws_eventually_left_p);


property ctrl_verify_compute_w0_intt_idle_eventually_left_p;
  verify_compute_w0_intt_idle
|->
  s_eventually(!verify_compute_w0_intt_idle);
endproperty
ctrl_verify_compute_w0_intt_idle_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_idle_eventually_left_p);


property ctrl_verify_compute_w0_intt_start_eventually_left_p;
  verify_compute_w0_intt_start
|->
  s_eventually(!verify_compute_w0_intt_start);
endproperty
ctrl_verify_compute_w0_intt_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_start_eventually_left_p);


property ctrl_verify_compute_w0_intt_eventually_left_p;
  verify_compute_w0_intt
|->
  s_eventually(!verify_compute_w0_intt);
endproperty
ctrl_verify_compute_w0_intt_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_compute_w0_intt_eventually_left_p);


property ctrl_verify_sig_decode_h_start_eventually_left_p;
  verify_sig_decode_h_start
|->
  s_eventually(!verify_sig_decode_h_start);
endproperty
ctrl_verify_sig_decode_h_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_h_start_eventually_left_p);


property ctrl_verify_sig_decode_h_eventually_left_p;
  verify_sig_decode_h
|->
  s_eventually(!verify_sig_decode_h);
endproperty
ctrl_verify_sig_decode_h_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_sig_decode_h_eventually_left_p);


property ctrl_verify_load_mu_SHA3_START_eventually_left_p;
  verify_load_mu_SHA3_START
|->
  s_eventually(!verify_load_mu_SHA3_START);
endproperty
ctrl_verify_load_mu_SHA3_START_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_SHA3_START_eventually_left_p);


property ctrl_verify_load_mu_start_eventually_left_p;
  verify_load_mu_start
|->
  s_eventually(!verify_load_mu_start);
endproperty
ctrl_verify_load_mu_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_start_eventually_left_p);


property ctrl_verify_load_mu_eventually_left_p;
  verify_load_mu
|->
  s_eventually(!verify_load_mu);
endproperty
ctrl_verify_load_mu_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_eventually_left_p);


property ctrl_verify_load_mu_msg_done_eventually_left_p;
  verify_load_mu_msg_done
|->
  s_eventually(!verify_load_mu_msg_done);
endproperty
ctrl_verify_load_mu_msg_done_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_msg_done_eventually_left_p);


property ctrl_verify_load_mu_wait_eventually_left_p;
  verify_load_mu_wait
|->
  s_eventually(!verify_load_mu_wait);
endproperty
ctrl_verify_load_mu_wait_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_load_mu_wait_eventually_left_p);


property ctrl_verify_use_hint_start_eventually_left_p;
  verify_use_hint_start
|->
  s_eventually(!verify_use_hint_start);
endproperty
ctrl_verify_use_hint_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_use_hint_start_eventually_left_p);


property ctrl_verify_use_hint_eventually_left_p;
  verify_use_hint
|->
  s_eventually(!verify_use_hint);
endproperty
ctrl_verify_use_hint_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_use_hint_eventually_left_p);


property ctrl_verify_mu_sampling_start_eventually_left_p;
  verify_mu_sampling_start
|->
  s_eventually(!verify_mu_sampling_start);
endproperty
ctrl_verify_mu_sampling_start_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_mu_sampling_start_eventually_left_p);


property ctrl_verify_mu_sampling_eventually_left_p;
  verify_mu_sampling
|->
  s_eventually(!verify_mu_sampling);
endproperty
ctrl_verify_mu_sampling_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_mu_sampling_eventually_left_p);


property ctrl_verify_end_state_eventually_left_p;
  verify_end_state
|->
  s_eventually(!verify_end_state);
endproperty
ctrl_verify_end_state_eventually_left_a: assert property (disable iff(!mldsa_ctrl.rst_b || mldsa_ctrl.zeroize || mldsa_ctrl.error_flag) ctrl_verify_end_state_eventually_left_p);


parameter CONSISTENCY = 1;
if (CONSISTENCY) begin
  // Check that no more than 1 state condition is met at the same time
  ctrl_consistency_onehot0_state: assert property($onehot0({ Keygen_ntt_s1_idle, idle, keygen_compute_t, keygen_compute_t_start, keygen_compute_tr_sampling, keygen_compute_tr_sampling_start, keygen_compute_tr_write_pk, keygen_compute_tr_write_pk_SHA3_START, keygen_compute_tr_write_pk_msg_done, keygen_compute_tr_write_pk_start, keygen_end_state, keygen_expand_seed_SHA3_START, keygen_expand_seed_sampling, keygen_expand_seed_sampling_start, keygen_expand_seed_start, keygen_intt_a, keygen_intt_a_idle,sign_check_mode, keygen_intt_a_start, keygen_jump_sign, keygen_ntt_s1, keygen_ntt_s1_start, keygen_power_2_round, keygen_power_2_round_start, keygen_pwm_a, keygen_pwm_a_start, keygen_pwm_a_write_immediate, keygen_pwm_a_write_immediate_msg_done, keygen_pwm_a_write_rho, keygen_pwm_a_write_rho_SHA3_START, keygen_pwm_a_write_rho_start, keygen_rejbounded_s1, keygen_rejbounded_s1_start, keygen_rejbounded_s2, keygen_rejbounded_s2_start, keygen_rnd_seed_SHA3_START, keygen_rnd_seed_done, keygen_rnd_seed_lfsr, keygen_rnd_seed_start, keygen_rnd_seed_wait, keygen_sample_rnd_seed, keygen_sample_rnd_seed_start, keygen_sk_encode, keygen_sk_encode_start, keygen_write_counter, keygen_write_counter_msg_done, keygen_write_entropy, keygen_write_entropy_msg_done, keygen_write_rejbounded_immediate_s1, keygen_write_rejbounded_immediate_s1_msg_done, keygen_write_rejbounded_immediate_s2, keygen_write_rejbounded_immediate_s2_msg_done, keygen_write_rejbounded_input_s1, keygen_write_rejbounded_input_s1_SHA3_START, keygen_write_rejbounded_input_s1_start, keygen_write_rejbounded_input_s2, keygen_write_rejbounded_input_s2_SHA3_START, keygen_write_rejbounded_input_s2_start, keygen_write_seed, keygen_write_seed_immediate, keygen_write_seed_msg_done, sign_compute_c, sign_compute_c_start, sign_compute_lfsr_seed_SHA3_START, sign_compute_lfsr_seed_lfsr, sign_compute_lfsr_seed_sampling, sign_compute_lfsr_seed_sampling_start, sign_compute_lfsr_seed_start, sign_compute_lfsr_seed_wait, sign_compute_lfsr_seed_write_counter, sign_compute_lfsr_seed_write_counter_msg_done, sign_compute_lfsr_seed_write_entropy, sign_compute_lfsr_seed_write_entropy_msg_done, sign_compute_mu_SHA3_START, sign_compute_mu_idle, sign_compute_mu_sampling, sign_compute_mu_sampling_start, sign_compute_mu_start, sign_compute_mu_wait, sign_compute_mu_write_msg_prime, sign_compute_mu_write_msg_prime_msg_done, sign_compute_mu_write_tr, sign_compute_mu_write_tr_msg_done, sign_compute_rho_prime_SHA3_START, sign_compute_rho_prime_sampling, sign_compute_rho_prime_sampling_start, sign_compute_rho_prime_start, sign_compute_rho_prime_wait_0, sign_compute_rho_prime_wait_1, sign_compute_rho_prime_write_K, sign_compute_rho_prime_write_K_msg_done, sign_compute_rho_prime_write_mu, sign_compute_rho_prime_write_mu_msg_done, sign_compute_rho_prime_write_sign_rnd, sign_compute_rho_prime_write_sign_rnd_msg_done, sign_compute_w0_intt, sign_compute_w0_intt_idle, sign_compute_w0_intt_start, sign_compute_w0_pwm, sign_compute_w0_pwm_SHA3_START, sign_compute_w0_pwm_samp_ntt, sign_compute_w0_pwm_start, sign_compute_w0_pwm_write_immediate, sign_compute_w0_pwm_write_immediate_msg_done, sign_compute_w0_pwm_write_rho, sign_decompose_w, sign_decompose_w_start, sign_end_of_challenge, sign_end_state, sign_expand_mask_SHA3_START, sign_expand_mask_done, sign_expand_mask_sampling, sign_expand_mask_sampling_start, sign_expand_mask_start, sign_expand_mask_write_kappa_immediate, sign_expand_mask_write_kappa_immediate_msg_done, sign_expand_mask_write_rho_prime, sign_load_mu, sign_load_mu_SHA3_START, sign_load_mu_idle, sign_load_mu_msg_done, sign_load_mu_start, sign_load_mu_wait, sign_ntt_y, sign_ntt_y_idle, sign_ntt_y_start, sign_rnd_seed_SHA3_START, sign_rnd_seed_lfsr, sign_rnd_seed_start, sign_rnd_seed_wait, sign_sample_in_ball_SHA3_START, sign_sample_in_ball_sampling, sign_sample_in_ball_sampling_start, sign_sample_in_ball_start, sign_sample_in_ball_write_c, sign_sample_in_ball_write_c_msg_done, sign_sample_rnd_seed, sign_sample_rnd_seed_start, sign_set_c_valid, sign_set_w0_valid, sign_set_y_valid, sign_wait_for_c_clear, sign_wait_for_w0_clear, sign_wait_for_y_and_w0_clear, sign_write_counter, sign_write_counter_msg_done, sign_write_entropy, sign_write_entropy_msg_done, verify_check_mode, verify_compute_az_SHA3_START, verify_compute_az_pwm, verify_compute_az_pwm_start, verify_compute_az_start, verify_compute_az_write_immediate, verify_compute_az_write_immediate_msg_done, verify_compute_az_write_rho, verify_compute_mu_SHA3_START, verify_compute_mu_sampling, verify_compute_mu_sampling_start, verify_compute_mu_start, verify_compute_mu_wait, verify_compute_mu_write_msg_prime, verify_compute_mu_write_msg_prime_msg_done, verify_compute_mu_write_tr, verify_compute_mu_write_tr_msg_done, verify_compute_tr_SHA3_START, verify_compute_tr_sampling, verify_compute_tr_sampling_start, verify_compute_tr_start, verify_compute_tr_write_pk, verify_compute_tr_write_pk_msg_done, verify_compute_w0_intt, verify_compute_w0_intt_idle, verify_compute_w0_intt_start, verify_compute_w0_pwm, verify_compute_w0_pwm_start, verify_compute_w0_pws, verify_compute_w0_pws_start, verify_end_state, verify_load_mu, verify_load_mu_SHA3_START, verify_load_mu_msg_done, verify_load_mu_start, verify_load_mu_wait, verify_mu_sampling, verify_mu_sampling_start, verify_norm_check, verify_norm_check_start, verify_ntt_c, verify_ntt_c_start, verify_ntt_t, verify_ntt_t_start, verify_ntt_z, verify_ntt_z_start, verify_pk_decode, verify_pk_decode_start, verify_sample_in_ball_SHA3_START, verify_sample_in_ball_sampling, verify_sample_in_ball_sampling_start, verify_sample_in_ball_start, verify_sample_in_ball_write_c, verify_sample_in_ball_write_c_msg_done, verify_sig_decode_h, verify_sig_decode_h_start, verify_sig_decode_z, verify_sig_decode_z_start, verify_use_hint, verify_use_hint_start }));
end


endmodule
