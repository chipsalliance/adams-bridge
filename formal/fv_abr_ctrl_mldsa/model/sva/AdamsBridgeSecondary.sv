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
// | Created on 02.12.2024 at 12:59                    |
=======
// | Created on 12.12.2024 at 10:40                    |
>>>>>>> issue1/adamsbridge_ctrl_esl
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import global_package::*;
import AdamsBridge_functions::*;
import mldsa_params_pkg::*;
import mldsa_ctrl_pkg::*;


module fv_AdamsBridgeSecondary_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic unsigned [14:0] sk_s1_offset_in,

  input a_unsigned_15_7 s1_addrs_in,

  input a_unsigned_15_8 t_addrs_in,

  input logic unsigned [14:0] temp_addr_in,

  input a_unsigned_15_8 s2_addrs_in,

  input logic unsigned [14:0] c_addr_in,

  input logic unsigned [14:0] c_ntt_addr_in,

  input logic unsigned [14:0] cs1_addr_in,

  input a_unsigned_15_7 y_addrs_in,

  input logic unsigned [14:0] z_addr_in,

  input a_unsigned_15_8 ct_addrs_in,

  input logic unsigned [14:0] cs2_addr_in,

  input a_unsigned_15_8 w0_addrs_in,

  input logic unsigned [14:0] r0_addr_in,

  input a_unsigned_15_8 hint_r_addrs_in,

  input logic sign_start_in,

  input logic c_valid_in,

  input logic y_valid_in,

  input logic clear_y_valid_out,

  input logic w0_valid_in,

  input logic clear_w0_valid_out,

  input logic to_sk_decode_vld,
  input logic to_sk_decode_rdy,
  input st_SkDecodeType to_sk_decode,

  input logic sk_decode_done_in,

  input logic to_ntt_vld,
  input logic to_ntt_rdy,
  input st_NttType to_ntt,

  input logic ntt_done_in,

  input logic to_norm_check_vld,
  input logic to_norm_check_rdy,
  input st_NormCheckType to_norm_check,

  input logic norm_check_done_in,

  input logic norm_check_invalid,

  input logic to_sig_encode_vld,
  input logic to_sig_encode_rdy,
  input st_SigEncodeType to_sig_encode,

  input logic sig_encode_done_in,

  input logic to_makehint_vld,
  input logic to_makehint_rdy,
  input st_ToMakehintType to_makehint,

  input st_FromMakehintType from_makehint,

  input logic makehint_done_in,

  input logic makehint_invalid_in,

  // Registers
  input logic unsigned [7:0] compute_ct_idx,
  input logic unsigned [7:0] compute_ct_intt_idx,
  input logic unsigned [7:0] compute_r_idx,
  input logic unsigned [7:0] compute_z_idx,
  input logic unsigned [7:0] s1_ntt_idx,
  input logic unsigned [7:0] s2_ntt_idx,
  input a_unsigned_32_21 signature_h,
  input logic signature_valid,
  input logic unsigned [7:0] t_ntt_idx,

  // States
  input logic secondary_idle,
  input logic secondary_sk_decode_start,
  input logic secondary_sk_decode,
  input logic secondary_ntt_t_start,
  input logic secondary_ntt_t,
  input logic secondary_ntt_s1_start,
  input logic secondary_ntt_s1,
  input logic secondary_ntt_s2_start,
  input logic secondary_ntt_s2,
  input logic secondary_wait_for_c,
  input logic secondary_ntt_c_start,
  input logic secondary_ntt_c,
  input logic secondary_wait_for_y_and_w0,
  input logic secondary_z_pwm_start,
  input logic secondary_z_pwm,
  input logic secondary_z_intt_start,
  input logic secondary_z_intt,
  input logic secondary_z_pwa_start,
  input logic secondary_z_pwa,
  input logic secondary_z_norm_check_start,
  input logic secondary_z_norm_check,
  input logic secondary_z_sig_encode_start,
  input logic secondary_z_sig_encode,
  input logic secondary_clear_y_valid,
  input logic secondary_after_clear_y_valid,
  input logic secondary_compute_ct_start,
  input logic secondary_compute_ct,
  input logic secondary_compute_ct_intt_start,
  input logic secondary_compute_ct_intt,
  input logic secondary_wait_for_w0,
  input logic secondary_r_pwm_start,
  input logic secondary_r_pwm,
  input logic secondary_r_intt_start,
  input logic secondary_r_intt,
  input logic secondary_r_pws_start,
  input logic secondary_r_pws,
  input logic secondary_r_norm_check_r0_start,
  input logic secondary_r_norm_check_r0,
  input logic secondary_r_norm_check_ct0_start,
  input logic secondary_r_norm_check_ct0,
  input logic secondary_r_pwa_start,
  input logic secondary_r_pwa,
  input logic secondary_clear_w0_valid,
  input logic secondary_after_clear_w0_valid,
  input logic secondary_makehint_start,
  input logic secondary_makehint
);


default clocking default_clk @(posedge clk); endclocking


a_unsigned_32_21 signature_h_0_i;
assign signature_h_0_i = '{
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
  16: 0,
  17: 0,
  18: 0,
  19: 0,
  20: 0
};

st_SkDecodeType to_sk_decode_0_i;
assign to_sk_decode_0_i = '{
  source_operand: sk_s1_offset_in,
  destination_addr: s1_addrs_in[64'd0]
};

st_NttType to_ntt_0_i;
assign to_ntt_0_i = '{
  mode: Ntt,
  operand1: t_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: t_addrs_in[8'd0]
};

st_NttType to_ntt_1_i;
assign to_ntt_1_i = '{
  mode: Ntt,
  operand1: t_addrs_in[(8'd1 + t_ntt_idx)],
  operand2: temp_addr_in,
  destination: t_addrs_in[(8'd1 + t_ntt_idx)]
};

st_NttType to_ntt_2_i;
assign to_ntt_2_i = '{
  mode: Ntt,
  operand1: s1_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: s1_addrs_in[8'd0]
};

st_NttType to_ntt_3_i;
assign to_ntt_3_i = '{
  mode: Ntt,
  operand1: s1_addrs_in[(8'd1 + s1_ntt_idx)],
  operand2: temp_addr_in,
  destination: s1_addrs_in[(8'd1 + s1_ntt_idx)]
};

st_NttType to_ntt_4_i;
assign to_ntt_4_i = '{
  mode: Ntt,
  operand1: s2_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: s2_addrs_in[8'd0]
};

st_NttType to_ntt_5_i;
assign to_ntt_5_i = '{
  mode: Ntt,
  operand1: s2_addrs_in[(8'd1 + s2_ntt_idx)],
  operand2: temp_addr_in,
  destination: s2_addrs_in[(8'd1 + s2_ntt_idx)]
};

st_NttType to_ntt_6_i;
assign to_ntt_6_i = '{
  mode: Ntt,
  operand1: c_addr_in,
  operand2: temp_addr_in,
  destination: c_ntt_addr_in
};

st_NttType to_ntt_7_i;
assign to_ntt_7_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: s1_addrs_in[8'd0],
  destination: cs1_addr_in
};

st_NttType to_ntt_8_i;
assign to_ntt_8_i = '{
  mode: Intt,
  operand1: cs1_addr_in,
  operand2: temp_addr_in,
  destination: cs1_addr_in
};

st_NttType to_ntt_9_i;
assign to_ntt_9_i = '{
  mode: Pwa,
  operand1: y_addrs_in[compute_z_idx],
  operand2: cs1_addr_in,
  destination: z_addr_in
};

st_NormCheckType to_norm_check_0_i;
assign to_norm_check_0_i = '{
  immediate: norm_check_z_immediate,
  source_addr: z_addr_in
};

st_SigEncodeType to_sig_encode_0_i;
assign to_sig_encode_0_i = '{
  source_addr: z_addr_in,
  immediate: (64'h40 * ({ 56'h0, compute_z_idx} ))
};

st_NttType to_ntt_10_i;
assign to_ntt_10_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: s1_addrs_in[(8'd1 + compute_z_idx)],
  destination: cs1_addr_in
};

st_NttType to_ntt_11_i;
assign to_ntt_11_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: t_addrs_in[8'd0],
  destination: ct_addrs_in[8'd0]
};

st_NttType to_ntt_12_i;
assign to_ntt_12_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: t_addrs_in[(8'd1 + compute_ct_idx)],
  destination: ct_addrs_in[(8'd1 + compute_ct_idx)]
};

st_NttType to_ntt_13_i;
assign to_ntt_13_i = '{
  mode: Intt,
  operand1: ct_addrs_in[8'd0],
  operand2: temp_addr_in,
  destination: ct_addrs_in[8'd0]
};

st_NttType to_ntt_14_i;
assign to_ntt_14_i = '{
  mode: Intt,
  operand1: ct_addrs_in[(8'd1 + compute_ct_intt_idx)],
  operand2: temp_addr_in,
  destination: ct_addrs_in[(8'd1 + compute_ct_intt_idx)]
};

st_NttType to_ntt_15_i;
assign to_ntt_15_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: s2_addrs_in[8'd0],
  destination: cs2_addr_in
};

st_NttType to_ntt_16_i;
assign to_ntt_16_i = '{
  mode: Intt,
  operand1: cs2_addr_in,
  operand2: temp_addr_in,
  destination: cs2_addr_in
};

st_NttType to_ntt_17_i;
assign to_ntt_17_i = '{
  mode: Pws,
  operand1: cs2_addr_in,
  operand2: w0_addrs_in[compute_r_idx],
  destination: r0_addr_in
};

st_NormCheckType to_norm_check_1_i;
assign to_norm_check_1_i = '{
  immediate: norm_check_r0_immediate,
  source_addr: r0_addr_in
};

st_NormCheckType to_norm_check_2_i;
assign to_norm_check_2_i = '{
  immediate: norm_check_ct0_immediate,
  source_addr: ct_addrs_in[compute_r_idx]
};

st_NttType to_ntt_18_i;
assign to_ntt_18_i = '{
  mode: Pwa,
  operand1: r0_addr_in,
  operand2: ct_addrs_in[compute_r_idx],
  destination: hint_r_addrs_in[compute_r_idx]
};

st_NttType to_ntt_19_i;
assign to_ntt_19_i = '{
  mode: Pwm,
  operand1: c_ntt_addr_in,
  operand2: s2_addrs_in[(8'd1 + compute_r_idx)],
  destination: cs2_addr_in
};

st_ToMakehintType to_makehint_0_i;
assign to_makehint_0_i = '{
  source_addr: hint_r_addrs_in[64'd0]
};

a_unsigned_32_21 signature_h_1_i;
assign signature_h_1_i = '{
  0: ((16'(from_makehint.makehint_addr) == 16'd0) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[0]),
  1: ((16'(from_makehint.makehint_addr) == 16'd1) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[1]),
  2: ((16'(from_makehint.makehint_addr) == 16'd2) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[2]),
  3: ((16'(from_makehint.makehint_addr) == 16'd3) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[3]),
  4: ((16'(from_makehint.makehint_addr) == 16'd4) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[4]),
  5: ((16'(from_makehint.makehint_addr) == 16'd5) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[5]),
  6: ((16'(from_makehint.makehint_addr) == 16'd6) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[6]),
  7: ((16'(from_makehint.makehint_addr) == 16'd7) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[7]),
  8: ((16'(from_makehint.makehint_addr) == 16'd8) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[8]),
  9: ((16'(from_makehint.makehint_addr) == 16'd9) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[9]),
  10: ((16'(from_makehint.makehint_addr) == 16'd10) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[10]),
  11: ((16'(from_makehint.makehint_addr) == 16'd11) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[11]),
  12: ((16'(from_makehint.makehint_addr) == 16'd12) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[12]),
  13: ((16'(from_makehint.makehint_addr) == 16'd13) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[13]),
  14: ((16'(from_makehint.makehint_addr) == 16'd14) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[14]),
  15: ((16'(from_makehint.makehint_addr) == 16'd15) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[15]),
  16: ((16'(from_makehint.makehint_addr) == 16'd16) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[16]),
  17: ((16'(from_makehint.makehint_addr) == 16'd17) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[17]),
  18: ((16'(from_makehint.makehint_addr) == 16'd18) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[18]),
  19: ((16'(from_makehint.makehint_addr) == 16'd19) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[19]),
  20: ((16'(from_makehint.makehint_addr) == 16'd20) ? (signature_h[16'(from_makehint.makehint_addr)] | from_makehint.makehint_data) : signature_h[20])
};


sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence


property reset_p;
  reset_sequence |->
  secondary_idle &&
  clear_w0_valid_out == 0 &&
  clear_y_valid_out == 0 &&
  compute_ct_idx == 8'd0 &&
  compute_ct_intt_idx == 8'd0 &&
  compute_r_idx == 8'd0 &&
  compute_z_idx == 8'd0 &&
  s1_ntt_idx == 8'd0 &&
  s2_ntt_idx == 8'd0 &&
  t_ntt_idx == 8'd0 &&
  to_makehint_vld == 0 &&
  to_norm_check_vld == 0 &&
  to_ntt_vld == 0 &&
  to_sig_encode_vld == 0 &&
  to_sk_decode_vld == 0;
endproperty
reset_a: assert property (reset_p);


property secondary_after_clear_w0_valid_to_secondary_makehint_start_p;
  secondary_after_clear_w0_valid
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_makehint_start &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx) &&
  to_makehint == $past(to_makehint_0_i, 1) &&
  to_makehint_vld == 1;
endproperty
secondary_after_clear_w0_valid_to_secondary_makehint_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_after_clear_w0_valid_to_secondary_makehint_start_p);


property secondary_after_clear_y_valid_to_secondary_compute_ct_start_p;
  secondary_after_clear_y_valid
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_compute_ct_start &&
  compute_ct_idx == 8'd0 &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx) &&
  to_ntt == $past(to_ntt_11_i, 1) &&
  to_ntt_vld == 1;
endproperty
secondary_after_clear_y_valid_to_secondary_compute_ct_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_after_clear_y_valid_to_secondary_compute_ct_start_p);


property secondary_clear_w0_valid_to_secondary_after_clear_w0_valid_p;
  secondary_clear_w0_valid
|->
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_after_clear_w0_valid &&
  clear_w0_valid_out == 0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_clear_w0_valid_to_secondary_after_clear_w0_valid_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_clear_w0_valid_to_secondary_after_clear_w0_valid_p);


property secondary_clear_y_valid_to_secondary_after_clear_y_valid_p;
  secondary_clear_y_valid
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_after_clear_y_valid &&
  clear_y_valid_out == 0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_clear_y_valid_to_secondary_after_clear_y_valid_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_clear_y_valid_to_secondary_after_clear_y_valid_p);


property secondary_compute_ct_intt_start_to_secondary_compute_ct_intt_p;
  secondary_compute_ct_intt_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_compute_ct_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_compute_ct_intt_start_to_secondary_compute_ct_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_start_to_secondary_compute_ct_intt_p);


property secondary_compute_ct_intt_to_secondary_compute_ct_intt_p;
  secondary_compute_ct_intt &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_compute_ct_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_compute_ct_intt_to_secondary_compute_ct_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_to_secondary_compute_ct_intt_p);


property secondary_compute_ct_intt_to_secondary_compute_ct_intt_start_p;
  secondary_compute_ct_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_ct_intt_idx} )) < 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_compute_ct_intt_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == (8'd1 + $past(compute_ct_intt_idx, 2)) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_14_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_compute_ct_intt_to_secondary_compute_ct_intt_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_to_secondary_compute_ct_intt_start_p);


property secondary_compute_ct_intt_to_secondary_wait_for_w0_p;
  secondary_compute_ct_intt &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_ct_intt_idx} )) >= 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_w0 &&
  $stable(compute_ct_idx) &&
  compute_ct_intt_idx == 8'd0 &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_compute_ct_intt_to_secondary_wait_for_w0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_to_secondary_wait_for_w0_p);


property secondary_compute_ct_start_to_secondary_compute_ct_p;
  secondary_compute_ct_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_compute_ct &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_compute_ct_start_to_secondary_compute_ct_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_start_to_secondary_compute_ct_p);


property secondary_compute_ct_to_secondary_compute_ct_p;
  secondary_compute_ct &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_compute_ct &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_compute_ct_to_secondary_compute_ct_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_to_secondary_compute_ct_p);


property secondary_compute_ct_to_secondary_compute_ct_intt_start_p;
  secondary_compute_ct &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_ct_idx} )) >= 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_compute_ct_intt_start &&
  compute_ct_idx == 8'd0 &&
  compute_ct_intt_idx == 8'd0 &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_13_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_compute_ct_to_secondary_compute_ct_intt_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_to_secondary_compute_ct_intt_start_p);


property secondary_compute_ct_to_secondary_compute_ct_start_p;
  secondary_compute_ct &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_ct_idx} )) < 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_compute_ct_start &&
  compute_ct_idx == (8'd1 + $past(compute_ct_idx, 2)) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_12_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_compute_ct_to_secondary_compute_ct_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_to_secondary_compute_ct_start_p);


property secondary_idle_to_secondary_idle_p;
  secondary_idle &&
  !sign_start_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_idle &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_idle_to_secondary_idle_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_idle_to_secondary_idle_p);


property secondary_idle_to_secondary_sk_decode_start_p;
  secondary_idle &&
  sign_start_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0) and
  ##2
  secondary_sk_decode_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_sk_decode == $past(to_sk_decode_0_i, 2) &&
  to_sk_decode_vld == 1;
endproperty
secondary_idle_to_secondary_sk_decode_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_idle_to_secondary_sk_decode_start_p);


property secondary_makehint_start_to_secondary_makehint_p;
  secondary_makehint_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_makehint &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_makehint_start_to_secondary_makehint_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_start_to_secondary_makehint_p);


property secondary_makehint_to_secondary_idle_p;
  secondary_makehint &&
  from_makehint.makehint_wren &&
  makehint_done_in &&
  signature_valid &&
  !makehint_invalid_in
|->
  ##1 ($stable(clear_w0_valid_out))[*10] and
  ##1 ($stable(clear_y_valid_out))[*10] and
  ##1 (to_makehint_vld == 0)[*10] and
  ##1 (to_norm_check_vld == 0)[*10] and
  ##1 (to_ntt_vld == 0)[*10] and
  ##1 (to_sig_encode_vld == 0)[*10] and
  ##1 (to_sk_decode_vld == 0)[*10] and
  ##10
  secondary_idle &&
  compute_ct_idx == $past(compute_ct_idx, 10) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 10) &&
  compute_r_idx == $past(compute_r_idx, 10) &&
  compute_z_idx == $past(compute_z_idx, 10) &&
  s1_ntt_idx == $past(s1_ntt_idx, 10) &&
  s2_ntt_idx == $past(s2_ntt_idx, 10) &&
  t_ntt_idx == $past(t_ntt_idx, 10);
endproperty
secondary_makehint_to_secondary_idle_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_idle_p);


property secondary_makehint_to_secondary_idle_1_p;
  secondary_makehint &&
  !from_makehint.makehint_wren &&
  makehint_done_in &&
  signature_valid &&
  !makehint_invalid_in
|->
  ##1 ($stable(clear_w0_valid_out))[*10] and
  ##1 ($stable(clear_y_valid_out))[*10] and
  ##1 (to_makehint_vld == 0)[*10] and
  ##1 (to_norm_check_vld == 0)[*10] and
  ##1 (to_ntt_vld == 0)[*10] and
  ##1 (to_sig_encode_vld == 0)[*10] and
  ##1 (to_sk_decode_vld == 0)[*10] and
  ##10
  secondary_idle &&
  compute_ct_idx == $past(compute_ct_idx, 10) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 10) &&
  compute_r_idx == $past(compute_r_idx, 10) &&
  compute_z_idx == $past(compute_z_idx, 10) &&
  s1_ntt_idx == $past(s1_ntt_idx, 10) &&
  s2_ntt_idx == $past(s2_ntt_idx, 10) &&
  t_ntt_idx == $past(t_ntt_idx, 10);
endproperty
secondary_makehint_to_secondary_idle_1_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_idle_1_p);


property secondary_makehint_to_secondary_makehint_p;
  secondary_makehint &&
  from_makehint.makehint_wren &&
  !makehint_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_makehint &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_makehint_to_secondary_makehint_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_makehint_p);


property secondary_makehint_to_secondary_makehint_1_p;
  secondary_makehint &&
  !from_makehint.makehint_wren &&
  !makehint_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_makehint &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_makehint_to_secondary_makehint_1_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_makehint_1_p);


property secondary_makehint_to_secondary_wait_for_c_p;
  secondary_makehint &&
  from_makehint.makehint_wren &&
  makehint_done_in &&
  (!signature_valid || makehint_invalid_in)
|->
  ##1 ($stable(clear_w0_valid_out))[*3] and
  ##1 ($stable(clear_y_valid_out))[*3] and
  ##1 (to_makehint_vld == 0)[*3] and
  ##1 (to_norm_check_vld == 0)[*3] and
  ##1 (to_ntt_vld == 0)[*3] and
  ##1 (to_sig_encode_vld == 0)[*3] and
  ##1 (to_sk_decode_vld == 0)[*3] and
  ##3
  secondary_wait_for_c &&
  compute_ct_idx == $past(compute_ct_idx, 3) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 3) &&
  compute_r_idx == $past(compute_r_idx, 3) &&
  compute_z_idx == $past(compute_z_idx, 3) &&
  s1_ntt_idx == $past(s1_ntt_idx, 3) &&
  s2_ntt_idx == $past(s2_ntt_idx, 3) &&
  t_ntt_idx == $past(t_ntt_idx, 3);
endproperty
secondary_makehint_to_secondary_wait_for_c_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_wait_for_c_p);


property secondary_makehint_to_secondary_wait_for_c_1_p;
  secondary_makehint &&
  !from_makehint.makehint_wren &&
  makehint_done_in &&
  (!signature_valid || makehint_invalid_in)
|->
  ##1 ($stable(clear_w0_valid_out))[*3] and
  ##1 ($stable(clear_y_valid_out))[*3] and
  ##1 (to_makehint_vld == 0)[*3] and
  ##1 (to_norm_check_vld == 0)[*3] and
  ##1 (to_ntt_vld == 0)[*3] and
  ##1 (to_sig_encode_vld == 0)[*3] and
  ##1 (to_sk_decode_vld == 0)[*3] and
  ##3
  secondary_wait_for_c &&
  compute_ct_idx == $past(compute_ct_idx, 3) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 3) &&
  compute_r_idx == $past(compute_r_idx, 3) &&
  compute_z_idx == $past(compute_z_idx, 3) &&
  s1_ntt_idx == $past(s1_ntt_idx, 3) &&
  s2_ntt_idx == $past(s2_ntt_idx, 3) &&
  t_ntt_idx == $past(t_ntt_idx, 3);
endproperty
secondary_makehint_to_secondary_wait_for_c_1_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_to_secondary_wait_for_c_1_p);


property secondary_ntt_c_start_to_secondary_ntt_c_p;
  secondary_ntt_c_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_c &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_c_start_to_secondary_ntt_c_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_c_start_to_secondary_ntt_c_p);


property secondary_ntt_c_to_secondary_ntt_c_p;
  secondary_ntt_c &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_c &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_c_to_secondary_ntt_c_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_c_to_secondary_ntt_c_p);


property secondary_ntt_c_to_secondary_wait_for_y_and_w0_p;
  secondary_ntt_c &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_y_and_w0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_c_to_secondary_wait_for_y_and_w0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_c_to_secondary_wait_for_y_and_w0_p);


property secondary_ntt_s1_start_to_secondary_ntt_s1_p;
  secondary_ntt_s1_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_s1 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_s1_start_to_secondary_ntt_s1_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_start_to_secondary_ntt_s1_p);


property secondary_ntt_s1_to_secondary_ntt_s1_p;
  secondary_ntt_s1 &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_s1 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_s1_to_secondary_ntt_s1_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_to_secondary_ntt_s1_p);


property secondary_ntt_s1_to_secondary_ntt_s1_start_p;
  secondary_ntt_s1 &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, s1_ntt_idx} )) < 64'd7)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_s1_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == (8'd1 + $past(s1_ntt_idx, 2)) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_3_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_ntt_s1_to_secondary_ntt_s1_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_to_secondary_ntt_s1_start_p);


property secondary_ntt_s1_to_secondary_ntt_s2_start_p;
  secondary_ntt_s1 &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, s1_ntt_idx} )) >= 64'd7)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_s2_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == 8'd0 &&
  s2_ntt_idx == 8'd0 &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_4_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_ntt_s1_to_secondary_ntt_s2_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_to_secondary_ntt_s2_start_p);


property secondary_ntt_s2_start_to_secondary_ntt_s2_p;
  secondary_ntt_s2_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_s2 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_s2_start_to_secondary_ntt_s2_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_start_to_secondary_ntt_s2_p);


property secondary_ntt_s2_to_secondary_ntt_s2_p;
  secondary_ntt_s2 &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_s2 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_s2_to_secondary_ntt_s2_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_to_secondary_ntt_s2_p);


property secondary_ntt_s2_to_secondary_ntt_s2_start_p;
  secondary_ntt_s2 &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, s2_ntt_idx} )) < 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_s2_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == (8'd1 + $past(s2_ntt_idx, 2)) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_5_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_ntt_s2_to_secondary_ntt_s2_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_to_secondary_ntt_s2_start_p);


property secondary_ntt_s2_to_secondary_wait_for_c_p;
  secondary_ntt_s2 &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, s2_ntt_idx} )) >= 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_c &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  s2_ntt_idx == 8'd0 &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_s2_to_secondary_wait_for_c_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_to_secondary_wait_for_c_p);


property secondary_ntt_t_start_to_secondary_ntt_t_p;
  secondary_ntt_t_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_t &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_t_start_to_secondary_ntt_t_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_start_to_secondary_ntt_t_p);


property secondary_ntt_t_to_secondary_ntt_s1_start_p;
  secondary_ntt_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, t_ntt_idx} )) >= 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_s1_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == 8'd0 &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == 8'd0 &&
  to_ntt == $past(to_ntt_2_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_ntt_t_to_secondary_ntt_s1_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_to_secondary_ntt_s1_start_p);


property secondary_ntt_t_to_secondary_ntt_t_p;
  secondary_ntt_t &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_ntt_t &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_ntt_t_to_secondary_ntt_t_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_to_secondary_ntt_t_p);


property secondary_ntt_t_to_secondary_ntt_t_start_p;
  secondary_ntt_t &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, t_ntt_idx} )) < 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_t_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == (8'd1 + $past(t_ntt_idx, 2)) &&
  to_ntt == $past(to_ntt_1_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_ntt_t_to_secondary_ntt_t_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_to_secondary_ntt_t_start_p);


property secondary_r_intt_start_to_secondary_r_intt_p;
  secondary_r_intt_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_intt_start_to_secondary_r_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_intt_start_to_secondary_r_intt_p);


property secondary_r_intt_to_secondary_r_intt_p;
  secondary_r_intt &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_intt_to_secondary_r_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_intt_to_secondary_r_intt_p);


property secondary_r_intt_to_secondary_r_pws_start_p;
  secondary_r_intt &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_pws_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_17_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_r_intt_to_secondary_r_pws_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_intt_to_secondary_r_pws_start_p);


property secondary_r_norm_check_ct0_start_to_secondary_r_norm_check_ct0_p;
  secondary_r_norm_check_ct0_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_norm_check_ct0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_norm_check_ct0_start_to_secondary_r_norm_check_ct0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_ct0_start_to_secondary_r_norm_check_ct0_p);


property secondary_r_norm_check_ct0_to_secondary_r_norm_check_ct0_p;
  secondary_r_norm_check_ct0 &&
  !norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_norm_check_ct0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_norm_check_ct0_to_secondary_r_norm_check_ct0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_ct0_to_secondary_r_norm_check_ct0_p);


property secondary_r_norm_check_ct0_to_secondary_r_pwa_start_p;
  secondary_r_norm_check_ct0 &&
  norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_pwa_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_18_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_r_norm_check_ct0_to_secondary_r_pwa_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_ct0_to_secondary_r_pwa_start_p);


property secondary_r_norm_check_r0_start_to_secondary_r_norm_check_r0_p;
  secondary_r_norm_check_r0_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_norm_check_r0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_norm_check_r0_start_to_secondary_r_norm_check_r0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_r0_start_to_secondary_r_norm_check_r0_p);


property secondary_r_norm_check_r0_to_secondary_r_norm_check_ct0_start_p;
  secondary_r_norm_check_r0 &&
  norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_norm_check_ct0_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_norm_check == $past(to_norm_check_2_i, 2) &&
  to_norm_check_vld == 1;
endproperty
secondary_r_norm_check_r0_to_secondary_r_norm_check_ct0_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_r0_to_secondary_r_norm_check_ct0_start_p);


property secondary_r_norm_check_r0_to_secondary_r_norm_check_r0_p;
  secondary_r_norm_check_r0 &&
  !norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_norm_check_r0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_norm_check_r0_to_secondary_r_norm_check_r0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_r0_to_secondary_r_norm_check_r0_p);


property secondary_r_pwa_start_to_secondary_r_pwa_p;
  secondary_r_pwa_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pwa &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pwa_start_to_secondary_r_pwa_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_start_to_secondary_r_pwa_p);


property secondary_r_pwa_to_secondary_clear_w0_valid_p;
  secondary_r_pwa &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_r_idx} )) >= 64'd8)
|->
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_clear_w0_valid &&
  clear_w0_valid_out == 1 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  compute_r_idx == 8'd0 &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pwa_to_secondary_clear_w0_valid_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_to_secondary_clear_w0_valid_p);


property secondary_r_pwa_to_secondary_r_pwa_p;
  secondary_r_pwa &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pwa &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pwa_to_secondary_r_pwa_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_to_secondary_r_pwa_p);


property secondary_r_pwa_to_secondary_r_pwm_start_p;
  secondary_r_pwa &&
  ntt_done_in &&
  ((64'd1 + ({ 56'h0, compute_r_idx} )) < 64'd8)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_pwm_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == (8'd1 + $past(compute_r_idx, 2)) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_19_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_r_pwa_to_secondary_r_pwm_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_to_secondary_r_pwm_start_p);


property secondary_r_pwm_start_to_secondary_r_pwm_p;
  secondary_r_pwm_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pwm &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pwm_start_to_secondary_r_pwm_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwm_start_to_secondary_r_pwm_p);


property secondary_r_pwm_to_secondary_r_intt_start_p;
  secondary_r_pwm &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_intt_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_16_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_r_pwm_to_secondary_r_intt_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwm_to_secondary_r_intt_start_p);


property secondary_r_pwm_to_secondary_r_pwm_p;
  secondary_r_pwm &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pwm &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pwm_to_secondary_r_pwm_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwm_to_secondary_r_pwm_p);


property secondary_r_pws_start_to_secondary_r_pws_p;
  secondary_r_pws_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pws &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pws_start_to_secondary_r_pws_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pws_start_to_secondary_r_pws_p);


property secondary_r_pws_to_secondary_r_norm_check_r0_start_p;
  secondary_r_pws &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_norm_check_r0_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_norm_check == $past(to_norm_check_1_i, 2) &&
  to_norm_check_vld == 1;
endproperty
secondary_r_pws_to_secondary_r_norm_check_r0_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pws_to_secondary_r_norm_check_r0_start_p);


property secondary_r_pws_to_secondary_r_pws_p;
  secondary_r_pws &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_r_pws &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_r_pws_to_secondary_r_pws_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pws_to_secondary_r_pws_p);


property secondary_sk_decode_start_to_secondary_sk_decode_p;
  secondary_sk_decode_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_sk_decode &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_sk_decode_start_to_secondary_sk_decode_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_sk_decode_start_to_secondary_sk_decode_p);


property secondary_sk_decode_to_secondary_ntt_t_start_p;
  secondary_sk_decode &&
  sk_decode_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_t_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == 8'd0 &&
  to_ntt == $past(to_ntt_0_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_sk_decode_to_secondary_ntt_t_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_sk_decode_to_secondary_ntt_t_start_p);


property secondary_sk_decode_to_secondary_sk_decode_p;
  secondary_sk_decode &&
  !sk_decode_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_sk_decode &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_sk_decode_to_secondary_sk_decode_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_sk_decode_to_secondary_sk_decode_p);


property secondary_wait_for_c_to_secondary_ntt_c_start_p;
  secondary_wait_for_c &&
  c_valid_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_ntt_c_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_6_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_wait_for_c_to_secondary_ntt_c_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_c_to_secondary_ntt_c_start_p);


property secondary_wait_for_c_to_secondary_wait_for_c_p;
  secondary_wait_for_c &&
  !c_valid_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_c &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_wait_for_c_to_secondary_wait_for_c_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_c_to_secondary_wait_for_c_p);


property secondary_wait_for_w0_to_secondary_r_pwm_start_p;
  secondary_wait_for_w0 &&
  w0_valid_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_r_pwm_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == 8'd0 &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_15_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_wait_for_w0_to_secondary_r_pwm_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_w0_to_secondary_r_pwm_start_p);


property secondary_wait_for_w0_to_secondary_wait_for_w0_p;
  secondary_wait_for_w0 &&
  !w0_valid_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_w0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_wait_for_w0_to_secondary_wait_for_w0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_w0_to_secondary_wait_for_w0_p);


property secondary_wait_for_y_and_w0_to_secondary_wait_for_y_and_w0_p;
  secondary_wait_for_y_and_w0 &&
  !(y_valid_in && w0_valid_in)
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_wait_for_y_and_w0 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_wait_for_y_and_w0_to_secondary_wait_for_y_and_w0_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_y_and_w0_to_secondary_wait_for_y_and_w0_p);


property secondary_wait_for_y_and_w0_to_secondary_z_pwm_start_p;
  secondary_wait_for_y_and_w0 &&
  y_valid_in &&
  w0_valid_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_pwm_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == 8'd0 &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_7_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_wait_for_y_and_w0_to_secondary_z_pwm_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_y_and_w0_to_secondary_z_pwm_start_p);


property secondary_z_intt_start_to_secondary_z_intt_p;
  secondary_z_intt_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_intt_start_to_secondary_z_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_intt_start_to_secondary_z_intt_p);


property secondary_z_intt_to_secondary_z_intt_p;
  secondary_z_intt &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_intt &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_intt_to_secondary_z_intt_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_intt_to_secondary_z_intt_p);


property secondary_z_intt_to_secondary_z_pwa_start_p;
  secondary_z_intt &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_pwa_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_9_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_z_intt_to_secondary_z_pwa_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_intt_to_secondary_z_pwa_start_p);


property secondary_z_norm_check_start_to_secondary_z_norm_check_p;
  secondary_z_norm_check_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_norm_check &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_norm_check_start_to_secondary_z_norm_check_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_norm_check_start_to_secondary_z_norm_check_p);


property secondary_z_norm_check_to_secondary_z_norm_check_p;
  secondary_z_norm_check &&
  !norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_norm_check &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_norm_check_to_secondary_z_norm_check_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_norm_check_to_secondary_z_norm_check_p);


property secondary_z_norm_check_to_secondary_z_sig_encode_start_p;
  secondary_z_norm_check &&
  norm_check_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_sig_encode_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_sig_encode == $past(to_sig_encode_0_i, 2) &&
  to_sig_encode_vld == 1;
endproperty
secondary_z_norm_check_to_secondary_z_sig_encode_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_norm_check_to_secondary_z_sig_encode_start_p);


property secondary_z_pwa_start_to_secondary_z_pwa_p;
  secondary_z_pwa_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_pwa &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_pwa_start_to_secondary_z_pwa_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwa_start_to_secondary_z_pwa_p);


property secondary_z_pwa_to_secondary_z_norm_check_start_p;
  secondary_z_pwa &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0)[*2] and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_norm_check_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_norm_check == $past(to_norm_check_0_i, 2) &&
  to_norm_check_vld == 1;
endproperty
secondary_z_pwa_to_secondary_z_norm_check_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwa_to_secondary_z_norm_check_start_p);


property secondary_z_pwa_to_secondary_z_pwa_p;
  secondary_z_pwa &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_pwa &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_pwa_to_secondary_z_pwa_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwa_to_secondary_z_pwa_p);


property secondary_z_pwm_start_to_secondary_z_pwm_p;
  secondary_z_pwm_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_pwm &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_pwm_start_to_secondary_z_pwm_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwm_start_to_secondary_z_pwm_p);


property secondary_z_pwm_to_secondary_z_intt_start_p;
  secondary_z_pwm &&
  ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_intt_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == $past(compute_z_idx, 2) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_8_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_z_pwm_to_secondary_z_intt_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwm_to_secondary_z_intt_start_p);


property secondary_z_pwm_to_secondary_z_pwm_p;
  secondary_z_pwm &&
  !ntt_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_pwm &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_pwm_to_secondary_z_pwm_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwm_to_secondary_z_pwm_p);


property secondary_z_sig_encode_start_to_secondary_z_sig_encode_p;
  secondary_z_sig_encode_start
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_sig_encode &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_sig_encode_start_to_secondary_z_sig_encode_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_start_to_secondary_z_sig_encode_p);


property secondary_z_sig_encode_to_secondary_clear_y_valid_p;
  secondary_z_sig_encode &&
  sig_encode_done_in &&
  ((64'd1 + ({ 56'h0, compute_z_idx} )) >= 64'd7)
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_clear_y_valid &&
  clear_y_valid_out == 1 &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  compute_z_idx == 8'd0 &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_sig_encode_to_secondary_clear_y_valid_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_to_secondary_clear_y_valid_p);


property secondary_z_sig_encode_to_secondary_z_pwm_start_p;
  secondary_z_sig_encode &&
  sig_encode_done_in &&
  ((64'd1 + ({ 56'h0, compute_z_idx} )) < 64'd7)
|->
  ##1 ($stable(clear_w0_valid_out))[*2] and
  ##1 ($stable(clear_y_valid_out))[*2] and
  ##1 (to_makehint_vld == 0)[*2] and
  ##1 (to_norm_check_vld == 0)[*2] and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0)[*2] and
  ##1 (to_sk_decode_vld == 0)[*2] and
  ##2
  secondary_z_pwm_start &&
  compute_ct_idx == $past(compute_ct_idx, 2) &&
  compute_ct_intt_idx == $past(compute_ct_intt_idx, 2) &&
  compute_r_idx == $past(compute_r_idx, 2) &&
  compute_z_idx == (8'd1 + $past(compute_z_idx, 2)) &&
  s1_ntt_idx == $past(s1_ntt_idx, 2) &&
  s2_ntt_idx == $past(s2_ntt_idx, 2) &&
  t_ntt_idx == $past(t_ntt_idx, 2) &&
  to_ntt == $past(to_ntt_10_i, 2) &&
  to_ntt_vld == 1;
endproperty
secondary_z_sig_encode_to_secondary_z_pwm_start_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_to_secondary_z_pwm_start_p);


property secondary_z_sig_encode_to_secondary_z_sig_encode_p;
  secondary_z_sig_encode &&
  !sig_encode_done_in
|->
  ##1 ($stable(clear_w0_valid_out)) and
  ##1 ($stable(clear_y_valid_out)) and
  ##1 (to_makehint_vld == 0) and
  ##1 (to_norm_check_vld == 0) and
  ##1 (to_ntt_vld == 0) and
  ##1 (to_sig_encode_vld == 0) and
  ##1 (to_sk_decode_vld == 0) and
  ##1
  secondary_z_sig_encode &&
  $stable(compute_ct_idx) &&
  $stable(compute_ct_intt_idx) &&
  $stable(compute_r_idx) &&
  $stable(compute_z_idx) &&
  $stable(s1_ntt_idx) &&
  $stable(s2_ntt_idx) &&
  $stable(t_ntt_idx);
endproperty
secondary_z_sig_encode_to_secondary_z_sig_encode_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_to_secondary_z_sig_encode_p);


property secondary_after_clear_w0_valid_eventually_left_p;
  secondary_after_clear_w0_valid
|->
  s_eventually(!secondary_after_clear_w0_valid);
endproperty
secondary_after_clear_w0_valid_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_after_clear_w0_valid_eventually_left_p);


property secondary_after_clear_y_valid_eventually_left_p;
  secondary_after_clear_y_valid
|->
  s_eventually(!secondary_after_clear_y_valid);
endproperty
secondary_after_clear_y_valid_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_after_clear_y_valid_eventually_left_p);


property secondary_clear_w0_valid_eventually_left_p;
  secondary_clear_w0_valid
|->
  s_eventually(!secondary_clear_w0_valid);
endproperty
secondary_clear_w0_valid_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_clear_w0_valid_eventually_left_p);


property secondary_clear_y_valid_eventually_left_p;
  secondary_clear_y_valid
|->
  s_eventually(!secondary_clear_y_valid);
endproperty
secondary_clear_y_valid_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_clear_y_valid_eventually_left_p);


property secondary_compute_ct_eventually_left_p;
  secondary_compute_ct
|->
  s_eventually(!secondary_compute_ct);
endproperty
secondary_compute_ct_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_eventually_left_p);


property secondary_compute_ct_intt_eventually_left_p;
  secondary_compute_ct_intt
|->
  s_eventually(!secondary_compute_ct_intt);
endproperty
secondary_compute_ct_intt_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_eventually_left_p);


property secondary_compute_ct_intt_start_eventually_left_p;
  secondary_compute_ct_intt_start
|->
  s_eventually(!secondary_compute_ct_intt_start);
endproperty
secondary_compute_ct_intt_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_intt_start_eventually_left_p);


property secondary_compute_ct_start_eventually_left_p;
  secondary_compute_ct_start
|->
  s_eventually(!secondary_compute_ct_start);
endproperty
secondary_compute_ct_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_compute_ct_start_eventually_left_p);


property secondary_idle_eventually_left_p;
  secondary_idle
|->
  s_eventually(!secondary_idle);
endproperty
secondary_idle_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_idle_eventually_left_p);


property secondary_makehint_eventually_left_p;
  secondary_makehint
|->
  s_eventually(!secondary_makehint);
endproperty
secondary_makehint_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_eventually_left_p);


property secondary_makehint_start_eventually_left_p;
  secondary_makehint_start
|->
  s_eventually(!secondary_makehint_start);
endproperty
secondary_makehint_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_makehint_start_eventually_left_p);


property secondary_ntt_c_eventually_left_p;
  secondary_ntt_c
|->
  s_eventually(!secondary_ntt_c);
endproperty
secondary_ntt_c_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_c_eventually_left_p);


property secondary_ntt_c_start_eventually_left_p;
  secondary_ntt_c_start
|->
  s_eventually(!secondary_ntt_c_start);
endproperty
secondary_ntt_c_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_c_start_eventually_left_p);


property secondary_ntt_s1_eventually_left_p;
  secondary_ntt_s1
|->
  s_eventually(!secondary_ntt_s1);
endproperty
secondary_ntt_s1_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_eventually_left_p);


property secondary_ntt_s1_start_eventually_left_p;
  secondary_ntt_s1_start
|->
  s_eventually(!secondary_ntt_s1_start);
endproperty
secondary_ntt_s1_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s1_start_eventually_left_p);


property secondary_ntt_s2_eventually_left_p;
  secondary_ntt_s2
|->
  s_eventually(!secondary_ntt_s2);
endproperty
secondary_ntt_s2_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_eventually_left_p);


property secondary_ntt_s2_start_eventually_left_p;
  secondary_ntt_s2_start
|->
  s_eventually(!secondary_ntt_s2_start);
endproperty
secondary_ntt_s2_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_s2_start_eventually_left_p);


property secondary_ntt_t_eventually_left_p;
  secondary_ntt_t
|->
  s_eventually(!secondary_ntt_t);
endproperty
secondary_ntt_t_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_eventually_left_p);


property secondary_ntt_t_start_eventually_left_p;
  secondary_ntt_t_start
|->
  s_eventually(!secondary_ntt_t_start);
endproperty
secondary_ntt_t_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_ntt_t_start_eventually_left_p);


property secondary_r_intt_eventually_left_p;
  secondary_r_intt
|->
  s_eventually(!secondary_r_intt);
endproperty
secondary_r_intt_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_intt_eventually_left_p);


property secondary_r_intt_start_eventually_left_p;
  secondary_r_intt_start
|->
  s_eventually(!secondary_r_intt_start);
endproperty
secondary_r_intt_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_intt_start_eventually_left_p);


property secondary_r_norm_check_ct0_eventually_left_p;
  secondary_r_norm_check_ct0
|->
  s_eventually(!secondary_r_norm_check_ct0);
endproperty
secondary_r_norm_check_ct0_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_ct0_eventually_left_p);


property secondary_r_norm_check_ct0_start_eventually_left_p;
  secondary_r_norm_check_ct0_start
|->
  s_eventually(!secondary_r_norm_check_ct0_start);
endproperty
secondary_r_norm_check_ct0_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_ct0_start_eventually_left_p);


property secondary_r_norm_check_r0_eventually_left_p;
  secondary_r_norm_check_r0
|->
  s_eventually(!secondary_r_norm_check_r0);
endproperty
secondary_r_norm_check_r0_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_r0_eventually_left_p);


property secondary_r_norm_check_r0_start_eventually_left_p;
  secondary_r_norm_check_r0_start
|->
  s_eventually(!secondary_r_norm_check_r0_start);
endproperty
secondary_r_norm_check_r0_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_norm_check_r0_start_eventually_left_p);


property secondary_r_pwa_eventually_left_p;
  secondary_r_pwa
|->
  s_eventually(!secondary_r_pwa);
endproperty
secondary_r_pwa_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_eventually_left_p);


property secondary_r_pwa_start_eventually_left_p;
  secondary_r_pwa_start
|->
  s_eventually(!secondary_r_pwa_start);
endproperty
secondary_r_pwa_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwa_start_eventually_left_p);


property secondary_r_pwm_eventually_left_p;
  secondary_r_pwm
|->
  s_eventually(!secondary_r_pwm);
endproperty
secondary_r_pwm_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwm_eventually_left_p);


property secondary_r_pwm_start_eventually_left_p;
  secondary_r_pwm_start
|->
  s_eventually(!secondary_r_pwm_start);
endproperty
secondary_r_pwm_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pwm_start_eventually_left_p);


property secondary_r_pws_eventually_left_p;
  secondary_r_pws
|->
  s_eventually(!secondary_r_pws);
endproperty
secondary_r_pws_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pws_eventually_left_p);


property secondary_r_pws_start_eventually_left_p;
  secondary_r_pws_start
|->
  s_eventually(!secondary_r_pws_start);
endproperty
secondary_r_pws_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_r_pws_start_eventually_left_p);


property secondary_sk_decode_eventually_left_p;
  secondary_sk_decode
|->
  s_eventually(!secondary_sk_decode);
endproperty
secondary_sk_decode_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_sk_decode_eventually_left_p);


property secondary_sk_decode_start_eventually_left_p;
  secondary_sk_decode_start
|->
  s_eventually(!secondary_sk_decode_start);
endproperty
secondary_sk_decode_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_sk_decode_start_eventually_left_p);


property secondary_wait_for_c_eventually_left_p;
  secondary_wait_for_c
|->
  s_eventually(!secondary_wait_for_c);
endproperty
secondary_wait_for_c_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_c_eventually_left_p);


property secondary_wait_for_w0_eventually_left_p;
  secondary_wait_for_w0
|->
  s_eventually(!secondary_wait_for_w0);
endproperty
secondary_wait_for_w0_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_w0_eventually_left_p);


property secondary_wait_for_y_and_w0_eventually_left_p;
  secondary_wait_for_y_and_w0
|->
  s_eventually(!secondary_wait_for_y_and_w0);
endproperty
secondary_wait_for_y_and_w0_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_wait_for_y_and_w0_eventually_left_p);


property secondary_z_intt_eventually_left_p;
  secondary_z_intt
|->
  s_eventually(!secondary_z_intt);
endproperty
secondary_z_intt_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_intt_eventually_left_p);


property secondary_z_intt_start_eventually_left_p;
  secondary_z_intt_start
|->
  s_eventually(!secondary_z_intt_start);
endproperty
secondary_z_intt_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_intt_start_eventually_left_p);


property secondary_z_norm_check_eventually_left_p;
  secondary_z_norm_check
|->
  s_eventually(!secondary_z_norm_check);
endproperty
secondary_z_norm_check_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_norm_check_eventually_left_p);


property secondary_z_norm_check_start_eventually_left_p;
  secondary_z_norm_check_start
|->
  s_eventually(!secondary_z_norm_check_start);
endproperty
secondary_z_norm_check_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_norm_check_start_eventually_left_p);


property secondary_z_pwa_eventually_left_p;
  secondary_z_pwa
|->
  s_eventually(!secondary_z_pwa);
endproperty
secondary_z_pwa_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwa_eventually_left_p);


property secondary_z_pwa_start_eventually_left_p;
  secondary_z_pwa_start
|->
  s_eventually(!secondary_z_pwa_start);
endproperty
secondary_z_pwa_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwa_start_eventually_left_p);


property secondary_z_pwm_eventually_left_p;
  secondary_z_pwm
|->
  s_eventually(!secondary_z_pwm);
endproperty
secondary_z_pwm_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwm_eventually_left_p);


property secondary_z_pwm_start_eventually_left_p;
  secondary_z_pwm_start
|->
  s_eventually(!secondary_z_pwm_start);
endproperty
secondary_z_pwm_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_pwm_start_eventually_left_p);


property secondary_z_sig_encode_eventually_left_p;
  secondary_z_sig_encode
|->
  s_eventually(!secondary_z_sig_encode);
endproperty
secondary_z_sig_encode_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_eventually_left_p);


property secondary_z_sig_encode_start_eventually_left_p;
  secondary_z_sig_encode_start
|->
  s_eventually(!secondary_z_sig_encode_start);
endproperty
secondary_z_sig_encode_start_eventually_left_a: assert property (disable iff(!rst_n || mldsa_ctrl.zeroize) secondary_z_sig_encode_start_eventually_left_p);


parameter SANITY = 1;
if (SANITY) begin
// Check that no more than 1 state condition is met at the same time
  sanity_onehot0_state: assert property ( $onehot0({secondary_after_clear_w0_valid, secondary_after_clear_y_valid, secondary_clear_w0_valid, secondary_clear_y_valid, secondary_compute_ct, secondary_compute_ct_intt, secondary_compute_ct_intt_start, secondary_compute_ct_start, secondary_idle, secondary_makehint, secondary_makehint_start, secondary_ntt_c, secondary_ntt_c_start, secondary_ntt_s1, secondary_ntt_s1_start, secondary_ntt_s2, secondary_ntt_s2_start, secondary_ntt_t, secondary_ntt_t_start, secondary_r_intt, secondary_r_intt_start, secondary_r_norm_check_ct0, secondary_r_norm_check_ct0_start, secondary_r_norm_check_r0, secondary_r_norm_check_r0_start, secondary_r_pwa, secondary_r_pwa_start, secondary_r_pwm, secondary_r_pwm_start, secondary_r_pws, secondary_r_pws_start, secondary_sk_decode, secondary_sk_decode_start, secondary_wait_for_c, secondary_wait_for_w0, secondary_wait_for_y_and_w0, secondary_z_intt, secondary_z_intt_start, secondary_z_norm_check, secondary_z_norm_check_start, secondary_z_pwa, secondary_z_pwa_start, secondary_z_pwm, secondary_z_pwm_start, secondary_z_sig_encode, secondary_z_sig_encode_start}) );
end


endmodule
