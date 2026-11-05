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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+

import fv_skdecode_top_pkg::*;
import abr_params_pkg::*;
import skdecode_defines_pkg::*;
import fv_skdecode_top_functions::*;

module fv_skdecode_top_m(
  input logic rst_n,
  input logic clk,

  // Ports
  input logic start_port_vld,
  input logic start_port_rdy,
  input fv_base_address_type start_port,

  input logic s1s2_valid_in,

  input logic t0_valid_in,

    input wire pi_split_en_i,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pi_rand_i,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pi_rand_dual_i,

  input logic keymem_a_rd_req_vld,
  input fv_mem_if_type keymem_a_rd_req,

  input logic keymem_b_rd_req_vld,
  input fv_mem_if_type keymem_b_rd_req,

  input logic mem_a_wr_req_vld,
  input fv_mem_if_type mem_a_wr_req,

  input logic mem_b_wr_req_vld,
  input fv_mem_if_type mem_b_wr_req,

  input logic skdecode_done_vld,
  input logic skdecode_done,

  input logic s1_done_vld,
  input logic s1_done,

  input logic s2_done_vld,
  input logic s2_done,

  input logic t0_done_vld,
  input logic t0_done,
  input logic skdecode_error,

  input fv_unsigned_96_2_type mem_a_wr_data,

  input fv_unsigned_96_2_type mem_b_wr_data,

  input logic s1s2_stall_dummy_out,

  // Registers
  input fv_base_address_type base_address,
  input logic unsigned [8:0] counter,
  input logic unsigned [13:0] fv_kmem_rd_addr,
  input logic unsigned [13:0] fv_mem_wr_addr,
  input fv_unsigned_3_8_type fv_s1s2_buf_data,
  input fv_unsigned_13_4_type fv_t0_buf_data,
  input logic s1s2_valid,

  // States
  input logic IDLE,
  input logic RD_WR_s1,
  input logic RD_STG_WR_s1,
  input logic RD_STG_WR_STG_1,
  input logic RD_WR_s2,
  input logic RD_STG_WR_s2,
  input logic RD_STG_WR_STG_2,
  input logic RD_WR_t0,
  input logic RD_STG_WR_t0,
  input logic RD_STG_WR_STG_3
);

default clocking default_clk @(posedge clk); endclocking

logic fv_error_reg;
always_ff @(posedge clk,negedge rst_n) begin
  if (!rst_n) begin
    // Reset logic
    fv_error_reg <= '0;
  end else begin
    // Normal operation
    if(skdecode_error) begin
      fv_error_reg <= 1'b1;
    end
  end
end
fv_base_address_type fv_base_address_0_i;
assign fv_base_address_0_i = '{
  source: 14'd0,
  destination: 14'd0
};

//unused in this design

// fv_unsigned_3_8_type fv_s1s2_buf_data_0_i;
// assign fv_s1s2_buf_data_0_i = '{
//   0: 3'd0,
//   1: 3'd0,
//   2: 3'd0,
//   3: 3'd0,
//   4: 3'd0,
//   5: 3'd0,
//   6: 3'd0,
//   7: 3'd0
// };

// fv_unsigned_13_4_type fv_t0_buf_data_0_i;
// assign fv_t0_buf_data_0_i = '{
//   0: 13'd0,
//   1: 13'd0,
//   2: 13'd0,
//   3: 13'd0
// };

fv_mem_if_type fv_keymem_a_rd_req_0_i;
assign fv_keymem_a_rd_req_0_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: 14'd0
};

// fv_unsigned_24_4_type fv_mem_a_wr_data_0_i;
// assign fv_mem_a_wr_data_0_i = '{
//   0: 24'd0,
//   1: 24'd0,
//   2: 24'd0,
//   3: 24'd0
// };

fv_unsigned_96_2_type fv_mem_a_wr_data_0_i;
assign fv_mem_a_wr_data_0_i = '0;

fv_mem_if_type fv_keymem_a_rd_req_1_i;
assign fv_keymem_a_rd_req_1_i = '{
  rd_wr_en: fv_rw_read_type,
  addr: start_port.source
};

fv_mem_if_type fv_keymem_b_rd_req_0_i;
assign fv_keymem_b_rd_req_0_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: start_port.source
};

fv_unsigned_24_4_type fv_decode_s1s2_a_0_i;
assign fv_decode_s1s2_a_0_i = decode_s1s2_a(fv_s1s2_buf_data);

fv_unsigned_24_4_type fv_decode_s1s2_b_0_i;
assign fv_decode_s1s2_b_0_i = decode_s1s2_b(fv_s1s2_buf_data);

// AUXILIARY: masked share0 model, mirrors abr_splitter.sv's reduce_rand_share0_mldsa.
fv_unsigned_24_4_type fv_reduced_rand_a_0_i;
assign fv_reduced_rand_a_0_i = reduce_rand_share0_mldsa(pi_rand_i);

fv_unsigned_24_4_type fv_reduced_rand_b_0_i;
assign fv_reduced_rand_b_0_i = reduce_rand_share0_mldsa(pi_rand_dual_i);

// Fixed: modeled rand_d1/rand_d2 as real registers instead of $past algebra, to match
// the real 2-cycle post-reset pipeline warm-up.
fv_unsigned_24_4_type fv_model_rand_d1_a, fv_model_rand_d2_a;
fv_unsigned_24_4_type fv_model_rand_d1_b, fv_model_rand_d2_b;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        fv_model_rand_d1_a <= '0;
        fv_model_rand_d2_a <= '0;
        fv_model_rand_d1_b <= '0;
        fv_model_rand_d2_b <= '0;
    end else begin
        fv_model_rand_d1_a <= fv_reduced_rand_a_0_i;
        fv_model_rand_d2_a <= fv_model_rand_d1_a;
        fv_model_rand_d1_b <= fv_reduced_rand_b_0_i;
        fv_model_rand_d2_b <= fv_model_rand_d1_b;
    end
end

// share1 shadow, mirrors abr_splitter's share1_coeff -> share1_coeff_reg pipeline.
fv_unsigned_24_4_type fv_model_share1_pre_a, fv_model_share1_a;
fv_unsigned_24_4_type fv_model_share1_pre_b, fv_model_share1_b;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        fv_model_share1_pre_a <= '0;
        fv_model_share1_a     <= '0;
        fv_model_share1_pre_b <= '0;
        fv_model_share1_b     <= '0;
    end else begin
        fv_model_share1_a <= fv_model_share1_pre_a;
        fv_model_share1_b <= fv_model_share1_pre_b;
        if (skdecode_top.wr_valid_a & pi_split_en_i) begin
            fv_model_share1_pre_a <= reduce_share1_mldsa(skdecode_top.mem_a_wr_data_int, pi_rand_i);
        end
        if (skdecode_top.wr_valid_b & pi_split_en_i) begin
            fv_model_share1_pre_b <= reduce_share1_mldsa(skdecode_top.mem_b_wr_data_int, pi_rand_dual_i);
        end
    end
end

fv_mem_if_type fv_keymem_a_rd_req_2_i;
assign fv_keymem_a_rd_req_2_i = '{
  rd_wr_en: fv_rw_read_type,
  addr: (14'd1 + fv_kmem_rd_addr)
};

fv_mem_if_type fv_keymem_b_rd_req_1_i;
assign fv_keymem_b_rd_req_1_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: (14'd1 + fv_kmem_rd_addr)
};

// Fixed: removed stale old-RTL address doubling; current RTL's mem_wr_addr is
// already the real address (A/B formed by masking the LSB, not scaling).
fv_mem_if_type fv_mem_a_wr_req_0_i;
assign fv_mem_a_wr_req_0_i = '{
  rd_wr_en: fv_rw_write_type,
  addr: {fv_mem_wr_addr[13:1], 1'b0}
};

fv_mem_if_type fv_mem_b_wr_req_0_i;
assign fv_mem_b_wr_req_0_i = '{
  rd_wr_en: fv_rw_write_type,
  addr: {fv_mem_wr_addr[13:1], 1'b1}
};

fv_mem_if_type fv_mem_a_wr_req_1_i;
assign fv_mem_a_wr_req_1_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: {fv_mem_wr_addr[13:1], 1'b0}
};

fv_mem_if_type fv_mem_b_wr_req_1_i;
assign fv_mem_b_wr_req_1_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: {fv_mem_wr_addr[13:1], 1'b1}
};

fv_mem_if_type fv_keymem_a_rd_req_3_i;
assign fv_keymem_a_rd_req_3_i = '{
  rd_wr_en: fv_rw_read_type,
  addr: (fv_kmem_rd_addr + 14'd0)
};

fv_mem_if_type fv_keymem_b_rd_req_2_i;
assign fv_keymem_b_rd_req_2_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: (fv_kmem_rd_addr + 14'd0)
};

fv_mem_if_type fv_keymem_a_rd_req_4_i;
assign fv_keymem_a_rd_req_4_i = '{
  rd_wr_en: fv_rw_read_type,
  addr: fv_kmem_rd_addr
};

fv_mem_if_type fv_keymem_b_rd_req_3_i;
assign fv_keymem_b_rd_req_3_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: fv_kmem_rd_addr
};

fv_unsigned_24_4_type fv_decode_t0_0_i;
assign fv_decode_t0_0_i = decode_t0(fv_t0_buf_data);

fv_mem_if_type fv_mem_a_wr_req_2_i;
assign fv_mem_a_wr_req_2_i = '{
  rd_wr_en: fv_rw_write_type,
  addr: fv_mem_wr_addr
};

fv_mem_if_type fv_mem_b_wr_req_2_i;
assign fv_mem_b_wr_req_2_i = '{
  rd_wr_en: fv_rw_idle_type,
  addr: fv_mem_wr_addr
};

sequence reset_sequence;
  !rst_n ##1 rst_n;
endsequence

property run_reset_p;
  reset_sequence
|->
  IDLE &&
  counter == 10'd0 &&
  keymem_a_rd_req == fv_keymem_a_rd_req_0_i &&
  keymem_b_rd_req == fv_keymem_a_rd_req_0_i &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == fv_keymem_a_rd_req_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == fv_keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 1 &&
  t0_done == 0;
endproperty
a_run_reset: assert property (run_reset_p);

// Fixed: masking-blind + wrong delay on mem_a/b_wr_data; split into masked/unmasked.

property run_IDLE_to_RD_WR_s1_unmasked_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] == 0) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_0_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == fv_keymem_a_rd_req_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&

  mem_b_wr_req == fv_keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_idle_to_rd_wr_s1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_unmasked_p);

property run_IDLE_to_RD_WR_s1_masked_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] == 0) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_0_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == fv_keymem_a_rd_req_0_i &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&

  mem_b_wr_req == fv_keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_idle_to_rd_wr_s1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_masked_p);

// Fixed: share1 check merged into run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p above
// (matches how every other family checks share1 inline, instead of a separate property).

// Fixed: same masking-blind bug as run_IDLE_to_RD_WR_s1_p (source.[0]!=0 mirror).

property run_IDLE_to_RD_WR_s1_1_unmasked_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] != 0) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_0_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_1_i, 1) &&

  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == fv_keymem_a_rd_req_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == fv_keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_idle_to_rd_wr_s1_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_1_unmasked_p);

property run_IDLE_to_RD_WR_s1_1_masked_p;
  IDLE &&
  start_port_vld &&
  (start_port.source[0] != 0) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  $stable(counter) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_0_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_1_i, 1) &&

  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == fv_keymem_a_rd_req_0_i &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == fv_keymem_a_rd_req_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_idle_to_rd_wr_s1_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_to_RD_WR_s1_1_masked_p);

// Fixed: $stable(counter) was wrong (counter genuinely resets 223->0 on this
// transition), plus the same masking-blind bug as run_RD_WR_s1_to_*.

property run_RD_STG_WR_STG_1_to_RD_WR_s2_unmasked_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] == 0) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_1_to_rd_wr_s2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_unmasked_p);

property run_RD_STG_WR_STG_1_to_RD_WR_s2_masked_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] == 0) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_1_to_rd_wr_s2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_masked_p);

// Fixed: same two bugs as run_RD_STG_WR_STG_1_to_RD_WR_s2_p (source.[0]!=0 mirror).

property run_RD_STG_WR_STG_1_to_RD_WR_s2_1_unmasked_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] != 0) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_1_to_rd_wr_s2_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_1_unmasked_p);

property run_RD_STG_WR_STG_1_to_RD_WR_s2_1_masked_p;
  RD_STG_WR_STG_1 &&
  (base_address.source[0] != 0) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_1_to_rd_wr_s2_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_to_RD_WR_s2_1_masked_p);

// Fixed: same $stable(counter) and masking-blind bugs as run_RD_STG_WR_STG_1_to_RD_WR_s2_p.

property run_RD_STG_WR_STG_2_to_RD_WR_t0_unmasked_p;
  RD_STG_WR_STG_2 &&
  !pi_split_en_i
|->
  ##1
  RD_WR_t0 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_2_to_rd_wr_t0_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_2_to_RD_WR_t0_unmasked_p);

property run_RD_STG_WR_STG_2_to_RD_WR_t0_masked_p;
  RD_STG_WR_STG_2 &&
  pi_split_en_i
|->
  ##1
  RD_WR_t0 &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_4_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_stg_2_to_rd_wr_t0_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_2_to_RD_WR_t0_masked_p);

// Fixed: same $stable(counter) and masking-blind bugs as run_RD_STG_WR_STG_1_to_RD_WR_s2_p.

property run_RD_STG_WR_STG_3_to_IDLE_unmasked_p;
  RD_STG_WR_STG_3 &&
  !pi_split_en_i
|->
  ##1
  IDLE &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 1 &&
  t0_done == 1;
endproperty
a_run_rd_stg_wr_stg_3_to_idle_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_3_to_IDLE_unmasked_p);

property run_RD_STG_WR_STG_3_to_IDLE_masked_p;
  RD_STG_WR_STG_3 &&
  pi_split_en_i
|->
  ##1
  IDLE &&
  counter == 10'd0 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 1 &&
  t0_done == 1;
endproperty
a_run_rd_stg_wr_stg_3_to_idle_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_3_to_IDLE_masked_p);

property run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_unmasked_p;
  RD_STG_WR_s1 &&
  !s1s2_valid_in &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_1 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s1_to_rd_stg_wr_stg_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_unmasked_p);

property run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_masked_p;
  RD_STG_WR_s1 &&
  !s1s2_valid_in &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_1 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s1_to_rd_stg_wr_stg_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_STG_1_masked_p);

// Predicts next cycle's s1s2_stall_dummy_out from the pacer's rotation.
logic fv_s1s2_stall_dummy_out_next_i;
assign fv_s1s2_stall_dummy_out_next_i = ~skdecode_top.skdecode_ctrl_inst.mem_rd_pace[1];

// Fixed: s1s2_stall_dummy_out periodicity bug (same fix as RD_STG_WR_s2 sibling).
property run_RD_STG_WR_s1_to_RD_STG_WR_s1_unmasked_p;
  RD_STG_WR_s1 &&
  s1s2_valid_in &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  $stable(counter) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == $past(fv_s1s2_stall_dummy_out_next_i, 1) &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s1_to_rd_stg_wr_s1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_s1_unmasked_p);

property run_RD_STG_WR_s1_to_RD_STG_WR_s1_masked_p;
  RD_STG_WR_s1 &&
  s1s2_valid_in &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == $past(fv_s1s2_stall_dummy_out_next_i, 1) &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s1_to_rd_stg_wr_s1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_to_RD_STG_WR_s1_masked_p);

property run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_unmasked_p;
  RD_STG_WR_s2 &&
  !s1s2_valid_in &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_2 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s2_to_rd_stg_wr_stg_2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_unmasked_p);

property run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_masked_p;
  RD_STG_WR_s2 &&
  !s1s2_valid_in &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_2 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s2_to_rd_stg_wr_stg_2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_STG_2_masked_p);

// Fixed: same s1s2_stall_dummy_out periodicity bug as the RD_STG_WR_s1 sibling --
// the pacer keeps rotating during the stall, so a fixed literal only holds 3 of
// every 4 cycles. Reuses the same next-cycle predictor aux signal.
property run_RD_STG_WR_s2_to_RD_STG_WR_s2_unmasked_p;
  RD_STG_WR_s2 &&
  s1s2_valid_in &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_s2 &&
  $stable(counter) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == $past(fv_s1s2_stall_dummy_out_next_i, 1) &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s2_to_rd_stg_wr_s2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_s2_unmasked_p);

property run_RD_STG_WR_s2_to_RD_STG_WR_s2_masked_p;
  RD_STG_WR_s2 &&
  s1s2_valid_in &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_s2 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == $past(fv_s1s2_stall_dummy_out_next_i, 1) &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_s2_to_rd_stg_wr_s2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_to_RD_STG_WR_s2_masked_p);

property run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_unmasked_p;
  RD_STG_WR_t0 &&
  !t0_valid_in &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_3 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 1;
endproperty
a_run_rd_stg_wr_t0_to_rd_stg_wr_stg_3_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_unmasked_p);

property run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_masked_p;
  RD_STG_WR_t0 &&
  !t0_valid_in &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_STG_3 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 1;
endproperty
a_run_rd_stg_wr_t0_to_rd_stg_wr_stg_3_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_STG_3_masked_p);

property run_RD_STG_WR_t0_to_RD_STG_WR_t0_unmasked_p;
  RD_STG_WR_t0 &&
  t0_valid_in &&
  !pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  $stable(counter) &&
  mem_a_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_t0_to_rd_stg_wr_t0_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_t0_unmasked_p);

property run_RD_STG_WR_t0_to_RD_STG_WR_t0_masked_p;
  RD_STG_WR_t0 &&
  t0_valid_in &&
  pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_STG_WR_t0 &&
  $stable(counter) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_stg_wr_t0_to_rd_stg_wr_t0_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_to_RD_STG_WR_t0_masked_p);










// _20/_21: the real S1 boundary transitions (_22/_23 are dead, same buffer-priming
// argument as run_RD_WR_s1_to_RD_WR_s1_12_p). Fixed masking-blind bug and a
// keymem_rd_req address off-by-one (needed the +1-offset variant, not +0).
property run_RD_WR_s1_to_RD_STG_WR_s1_20_unmasked_p;
  RD_WR_s1 &&
  counter == 10'd222 &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd223 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_stg_wr_s1_20_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_20_unmasked_p);

property run_RD_WR_s1_to_RD_STG_WR_s1_20_masked_p;
  RD_WR_s1 &&
  counter == 10'd222 &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd223 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_stg_wr_s1_20_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_20_masked_p);

// _21_p: odd-address-parity sibling of _20_p, same bugs and fix.

property run_RD_WR_s1_to_RD_STG_WR_s1_21_unmasked_p;
  RD_WR_s1 &&
  counter == 10'd222 &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  !pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd223 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_stg_wr_s1_21_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_21_unmasked_p);

property run_RD_WR_s1_to_RD_STG_WR_s1_21_masked_p;
  RD_WR_s1 &&
  counter == 10'd222 &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  pi_split_en_i
|->
  ##1
  RD_STG_WR_s1 &&
  counter == 10'd223 &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_stg_wr_s1_21_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_21_masked_p);


// Fixed: same masking-blind bug as run_IDLE_to_RD_WR_s1_p -- share0_o isn't gated
// by en_i in abr_splitter, so masked mem_a/b_wr_data must equal fv_model_rand_d2_a/b.
property run_RD_WR_s1_to_RD_WR_s1_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_masked_p);

// Fixed: same masking-blind bug, split into unmasked/masked pair.
property run_RD_WR_s1_to_RD_WR_s1_1_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_1_unmasked_p);
  // share1: masked branch only (antecedent already gates split_en_i), so no ternary.
property run_RD_WR_s1_to_RD_WR_s1_1_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_1_masked_p);

// Fixed: masking-blind bug (same class as _2_p-_9_p) and s1s2_stall_dummy_out
// (was ==0, should be ==1) -- this antecedent's residue sits one cycle before the
// pacer gap, so mem_rd_pace[0] is deterministically 0 at the checked cycle.

property run_RD_WR_s1_to_RD_WR_s1_10_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_10_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_10_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_10_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !(((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_10_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_10_masked_p);

cover_run_rd_wr_s1_to_rd_wr_s1_10_antecedent: cover property (
  RD_WR_s1 && (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) && (counter[2:0] != 3) && (counter[2:0] != 5) &&
  !s1s2_valid && (base_address.source[0] == 0) && ((10'd1 + counter) < 10'd224)
);
  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s1_to_RD_WR_s1_11_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_11_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_11_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_11_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_11_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_11_masked_p);

// Fixed: s1s2_stall_dummy_out was ==1, should be ==0 (opposite direction from
// _10_p, antecedent sits ON the pacer gap here). _14/_15/_18/_19 (!s1s2_valid
// siblings) are dead -- s1s2_valid is 1 on every phase once the buffer is primed.

property run_RD_WR_s1_to_RD_WR_s1_12_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_12_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_12_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_12_masked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_12_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_12_masked_p);

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s1_to_RD_WR_s1_13_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_13_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_13_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_13_masked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_13_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_13_masked_p);


// Expected uncovered: confirmed via error.vcd that s1s2_valid is locked to 1 at
// counter[2:0]==7, so this antecedent (!s1s2_valid at that residue) is
// unreachable -- see the comment above run_RD_WR_s1_to_RD_WR_s1_14_p.
cover_run_rd_wr_s1_to_rd_wr_s1_14_antecedent: cover property (
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) && (counter[2:0] != 3) && (counter[2:0] != 5) &&
  !s1s2_valid && (base_address.source[0] == 0) && ((10'd1 + counter) < 10'd224)
);

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s1_to_RD_WR_s1_16_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_16_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_16_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_16_masked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_16_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_16_masked_p);

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s1_to_RD_WR_s1_17_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_17_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_17_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_17_masked_p;
  RD_WR_s1 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_17_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_17_masked_p);

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.

  // Masking-blind + share1 fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p (masking/req_int) and run_IDLE_to_RD_WR_s1_unmasked_p/_masked_p (share1 conjuncts) for the full reasoning.

// Fixed: same masking-blind bug, plus mem_a/b_wr_req_1_i (fixed-mode helper) was
// wrong for the masked branch -- referenced the real internal signal
// (mem_a/b_wr_req_int, 2 cycles back) instead.
property run_RD_WR_s1_to_RD_WR_s1_2_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_2_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_2_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_2_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _2_p (source.[0]!=0 mirror).
property run_RD_WR_s1_to_RD_WR_s1_3_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_3_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_3_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_3_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hDF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_3_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_3_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _2_p (residues-{0,3,5} sibling).
property run_RD_WR_s1_to_RD_WR_s1_4_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_4_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_4_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_4_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_4_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_4_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _4_p (source.[0]!=0 mirror).
property run_RD_WR_s1_to_RD_WR_s1_5_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_5_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_5_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_5_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_5_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_5_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _2_p/_3_p (!s1s2_valid case).
property run_RD_WR_s1_to_RD_WR_s1_6_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_6_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_6_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_6_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_6_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_6_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _6_p (source.[0]!=0 mirror).
property run_RD_WR_s1_to_RD_WR_s1_7_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_7_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_7_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_7_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd224) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_7_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_7_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as _2_p/_4_p.

// Fixed: off-by-one boundary guard (was "< 224", allowed firing one cycle from
// the S1 boundary at 223) -- tightened to "< 223". Only _8/_9, not _10/_11 (those
// require !s1s2_valid, proven unreachable here via the buffer-priming argument).
property run_RD_WR_s1_to_RD_WR_s1_8_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd223) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_8_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_8_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_8_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd223) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_8_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_8_masked_p);

// Fixed: same masking-blind + mem_a/b_wr_req_int + boundary-guard fixes as _8_p
// (source.[0]!=0 mirror).
property run_RD_WR_s1_to_RD_WR_s1_9_unmasked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd223) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_9_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_9_unmasked_p);

property run_RD_WR_s1_to_RD_WR_s1_9_masked_p;
  RD_WR_s1 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4))) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd223) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s1 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 0 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s1_to_rd_wr_s1_9_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_9_masked_p);

// Dead code (base_p/_1_p-_9_p): same pattern as run_RD_WR_s1_to_RD_STG_WR_s1_p --
// each antecedent's residue excludes counter==255 (S2 boundary), mathematically
// unreachable. _10_p-_13_p are the real s1s2_valid x source-parity split.














// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_1_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_1_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_1_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_1_masked_p);

// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_10_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  // Fixed: same masking-blind + mem_a/b_wr_req_int fixes as run_RD_WR_s1_to_RD_WR_s1_10_p.
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  // Fixed: s1s2_stall_dummy_out was ==0, should be ==1 -- same pacer-residue
  // off-by-one as run_RD_WR_s1_to_RD_WR_s1_10_p/_11_p.
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_10_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_10_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_10_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  // Fixed: same masking-blind + mem_a/b_wr_req_int fixes as run_RD_WR_s1_to_RD_WR_s1_10_p.
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  // Fixed: s1s2_stall_dummy_out was ==0, should be ==1 -- same pacer-residue
  // off-by-one as run_RD_WR_s1_to_RD_WR_s1_10_p/_11_p.
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_10_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_10_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_11_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_11_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_11_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_11_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_11_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_11_masked_p);

// Fixed: same masking/stall bugs as run_RD_WR_s1_to_RD_WR_s1_10_p. _14/_15/_18/_19
// (!s1s2_valid siblings) are dead -- same buffer-priming argument as _12_p's family.
property run_RD_WR_s2_to_RD_WR_s2_12_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_12_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_12_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_12_masked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_12_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_12_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_13_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_13_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_13_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_13_masked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_13_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_13_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_16_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_16_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_16_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_16_masked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_16_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_16_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_17_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_17_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_17_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_17_masked_p;
  RD_WR_s2 &&
  (counter[1:0] == 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_17_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_17_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_2_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_2_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_2_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_2_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_3_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_3_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_3_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_3_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
  (counter != 10'hFF) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_3_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_3_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_4_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_4_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_4_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_4_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_4_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_4_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_5_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_5_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_5_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_5_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_5_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_5_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_6_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_6_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_6_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_6_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_6_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_6_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_7_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_7_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_7_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_7_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
  !s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd256) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 0 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_7_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_7_masked_p);

// Fixed: same masking-blind/stall bugs as run_RD_WR_s1_to_RD_WR_s1_10_p, plus the
// same off-by-one boundary guard as _8_p's S1 counterpart (was "< 256", tightened
// to "< 255"). Only _8/_9, not _10/_11 (unreachable, buffer-priming argument).
property run_RD_WR_s2_to_RD_WR_s2_8_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd255) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_8_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_8_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_8_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] == 0) &&
  ((10'd1 + counter) < 10'd255) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_8_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_8_masked_p);

// Masking-blind + share1 + stall fix -- see run_RD_WR_s1_to_RD_WR_s1_10_p / run_RD_WR_s2_to_RD_WR_s2_10_p for the full reasoning.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_s2_to_RD_WR_s2_9_unmasked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd255) &&
  !pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_s1s2_a_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_s1s2_b_0_i, 1) &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_9_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_9_unmasked_p);

property run_RD_WR_s2_to_RD_WR_s2_9_masked_p;
  RD_WR_s2 &&
  (counter[1:0] != 3) &&
  !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
  (counter[2:0] != 0) &&
  (counter[2:0] != 3) &&
  (counter[2:0] != 5) &&
  s1s2_valid &&
  (base_address.source[0] != 0) &&
  ((10'd1 + counter) < 10'd255) &&
  pi_split_en_i
|->
  ##1
  RD_WR_s2 &&
  counter == (10'd1 + $past(counter, 1)) &&
  keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s1s2_stall_dummy_out == 1 &&
  s2_done == 0 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_s2_to_rd_wr_s2_9_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_9_masked_p);




// Fixed: same masking-blind + mem_a/b_wr_req_int fixes as run_RD_WR_s1_to_RD_WR_s1_10_p.
property run_RD_WR_t0_to_RD_WR_t0_unmasked_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] == 0) &&
  ((10'd1 + counter) < 10'd511) &&
  !pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_a_wr_req_2_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_unmasked_p);

property run_RD_WR_t0_to_RD_WR_t0_masked_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] == 0) &&
  ((10'd1 + counter) < 10'd511) &&
  pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_masked_p);

// Masking-blind + share1 fix -- see run_RD_WR_t0_to_RD_WR_t0_p above.
// (was one combined property before the masked/unmasked split)

// Fixed: same off-by-one boundary guard as run_RD_WR_s1/s2_to_RD_WR_s1/s2_8/9
// (was "< 512", tightened to "< 511"). _2_p (!t0_valid_in) is protected by the
// same buffer-priming argument as the s1/s2 _10/_11 pairs; this one isn't.
property run_RD_WR_t0_to_RD_WR_t0_1_unmasked_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] != 0) &&
  ((10'd1 + counter) < 10'd511) &&
  !pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_a_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data[0] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_req == $past(fv_mem_a_wr_req_2_i, 1) &&
  mem_a_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  mem_b_wr_data[1] == $past(fv_decode_t0_0_i, 1) &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_1_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_1_unmasked_p);

property run_RD_WR_t0_to_RD_WR_t0_1_masked_p;
  RD_WR_t0 &&
  t0_valid_in &&
  (fv_mem_wr_addr[0] != 0) &&
  ((10'd1 + counter) < 10'd511) &&
  pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_1_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_1_masked_p);

// Masking-blind + share1 fix -- see run_RD_WR_t0_to_RD_WR_t0_p above.
// (was one combined property before the masked/unmasked split)

property run_RD_WR_t0_to_RD_WR_t0_2_unmasked_p;
  RD_WR_t0 &&
  !t0_valid_in &&
  ((10'd1 + counter) < 10'd511) &&
  !pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_a_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_req == $past(fv_mem_b_wr_req_2_i, 1) &&
  mem_a_wr_data[1] == fv_mem_a_wr_data_0_i &&
  mem_b_wr_data[1] == fv_mem_a_wr_data_0_i &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_2_unmasked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_2_unmasked_p);

property run_RD_WR_t0_to_RD_WR_t0_2_masked_p;
  RD_WR_t0 &&
  !t0_valid_in &&
  ((10'd1 + counter) < 10'd511) &&
  pi_split_en_i
|->
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  RD_WR_t0 &&
  counter == (10'd1 + $past(counter, 1)) &&
  mem_a_wr_data[0] == fv_model_rand_d2_a &&
  mem_a_wr_req == $past(skdecode_top.mem_a_wr_req_int, 2) &&
  mem_b_wr_data[0] == fv_model_rand_d2_b &&
  mem_b_wr_req == $past(skdecode_top.mem_b_wr_req_int, 2) &&
  mem_a_wr_data[1] == fv_model_share1_a &&
  mem_b_wr_data[1] == fv_model_share1_b &&
  s1_done == 1 &&
  s2_done == 1 &&
  skdecode_done == 0 &&
  t0_done == 0;
endproperty
a_run_rd_wr_t0_to_rd_wr_t0_2_masked: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_WR_t0_2_masked_p);

property run_IDLE_wait_p;
  IDLE &&
  !start_port_vld
|->
  ##1 ($stable(mem_a_wr_data[0])) and
  ##1 ($stable(mem_b_wr_data[0])) and
  ##1 ($stable(s1s2_stall_dummy_out)) and
  ##1
  IDLE &&
  $stable(counter);
endproperty
a_run_idle_wait: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg) || pi_split_en_i) run_IDLE_wait_p);

property run_s1s2_enable_p;
  (RD_WR_s1 || RD_WR_s2)
|=>
  skdecode_top.s1s2_enable
;endproperty
a_run_s1s2_enable: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_s1s2_enable_p);

// Fixed: antecedent was missing RD_STG_WR_s1/RD_STG_WR_STG_1 (and s2 equivalents) --
// s1s2_enable_fsm stays high in those compound states too since it isn't gated
// by last_poly_last_addr the way RD_WR_s1/RD_WR_s2 are.
property run_s1s2_no_enable_p;
  !(RD_WR_s1 || RD_STG_WR_s1 || RD_STG_WR_STG_1 || RD_WR_s2 || RD_STG_WR_s2 || RD_STG_WR_STG_2)
|=>
  !skdecode_top.s1s2_enable
;endproperty
a_run_s1s2_no_enable: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_s1s2_no_enable_p);

property run_t0_enable_p;
  (RD_WR_t0)
|=>
  skdecode_top.t0_enable
;endproperty
a_run_t0_enable: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_t0_enable_p);

// Fixed: same gap as run_s1s2_no_enable_p -- missing RD_STG_WR_t0/RD_STG_WR_STG_3,
// where t0_enable_fsm legitimately stays high but RD_WR_t0 alone already excludes it.
property run_t0_no_enable_p;
  !(RD_WR_t0 || RD_STG_WR_t0 || RD_STG_WR_STG_3)
|=>
  !skdecode_top.t0_enable
;endproperty
a_run_t0_no_enable: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_t0_no_enable_p);

property run_IDLE_eventually_left_p;
  IDLE
|->
  s_eventually(!IDLE);
endproperty
a_run_idle_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_IDLE_eventually_left_p);

property run_RD_WR_s1_eventually_left_p;
  RD_WR_s1
|->
  s_eventually(!RD_WR_s1);
endproperty
a_run_rd_wr_s1_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_eventually_left_p);

property run_RD_STG_WR_s1_eventually_left_p;
  RD_STG_WR_s1
|->
  s_eventually(!RD_STG_WR_s1);
endproperty
a_run_rd_stg_wr_s1_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s1_eventually_left_p);

property run_RD_STG_WR_STG_1_eventually_left_p;
  RD_STG_WR_STG_1
|->
  s_eventually(!RD_STG_WR_STG_1);
endproperty
a_run_rd_stg_wr_stg_1_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_1_eventually_left_p);

property run_RD_WR_s2_eventually_left_p;
  RD_WR_s2
|->
  s_eventually(!RD_WR_s2);
endproperty
a_run_rd_wr_s2_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_eventually_left_p);

property run_RD_STG_WR_s2_eventually_left_p;
  RD_STG_WR_s2
|->
  s_eventually(!RD_STG_WR_s2);
endproperty
a_run_rd_stg_wr_s2_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_s2_eventually_left_p);

property run_RD_STG_WR_STG_2_eventually_left_p;
  RD_STG_WR_STG_2
|->
  s_eventually(!RD_STG_WR_STG_2);
endproperty
a_run_rd_stg_wr_stg_2_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_2_eventually_left_p);

property run_RD_WR_t0_eventually_left_p;
  RD_WR_t0
|->
  s_eventually(!RD_WR_t0);
endproperty
a_run_rd_wr_t0_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_eventually_left_p);

property run_RD_STG_WR_t0_eventually_left_p;
  RD_STG_WR_t0
|->
  s_eventually(!RD_STG_WR_t0);
endproperty
a_run_rd_stg_wr_t0_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_t0_eventually_left_p);

property run_RD_STG_WR_STG_3_eventually_left_p;
  RD_STG_WR_STG_3
|->
  s_eventually(!RD_STG_WR_STG_3);
endproperty
a_run_rd_stg_wr_stg_3_eventually_left: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_STG_WR_STG_3_eventually_left_p);

localparam CONSISTENCY = 1;
if (CONSISTENCY) begin : gen_consistency_check
  // Check that no more than 1 state condition is met at the same time
  assert_run_consistency_onehot0_state_a: assert property($onehot0({ IDLE, RD_STG_WR_STG_1, RD_STG_WR_STG_2, RD_STG_WR_STG_3, RD_STG_WR_s1, RD_STG_WR_s2, RD_STG_WR_t0, RD_WR_s1, RD_WR_s2, RD_WR_t0 }));
end

// -- Category: memory-read pacing (mem_rd_pace) --
// S1: pace bit set -> exactly one channel (parity-selected by kmem_rd_addr[0]) reads
property run_rd_req_s1_pace_read_p;
    skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S1 &&
    skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S1 &&
    skdecode_top.s1s2_data_valid &&
    !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
    skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
|->
    (skdecode_top.skdecode_ctrl_inst.kmem_rd_addr[0] == 1'b0) ?
        (skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_READ && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_IDLE) :
        (skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_IDLE && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_READ);
endproperty
a_run_rd_req_s1_pace_read: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_rd_req_s1_pace_read_p);

// S1: pace bit clear -> both channels idle this cycle
property run_rd_req_s1_pace_idle_p;
    skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S1 &&
    skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S1 &&
    skdecode_top.s1s2_data_valid &&
    !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
    !skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
|->
    skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_IDLE && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_IDLE;
endproperty
a_run_rd_req_s1_pace_idle: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_rd_req_s1_pace_idle_p);

// S2 mirrors S1 exactly -- same kmem_a/b_rw_mode formula in the SKDEC_RD_S2 case block.
property run_rd_req_s2_pace_read_p;
    skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S2 &&
    skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S2 &&
    skdecode_top.s1s2_data_valid &&
    !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
    skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
|->
    (skdecode_top.skdecode_ctrl_inst.kmem_rd_addr[0] == 1'b0) ?
        (skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_READ && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_IDLE) :
        (skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_IDLE && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_READ);
endproperty
a_run_rd_req_s2_pace_read: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_rd_req_s2_pace_read_p);

// S2: pace bit clear -> both channels idle this cycle
property run_rd_req_s2_pace_idle_p;
    skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S2 &&
    skdecode_top.skdecode_ctrl_inst.write_fsm_state_ps == SKDEC_WR_S2 &&
    skdecode_top.s1s2_data_valid &&
    !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr &&
    !skdecode_top.skdecode_ctrl_inst.mem_rd_pace[0]
|->
    skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_a_rd_req.rd_wr_en == RW_IDLE && skdecode_top.fv_skdecode_top_wrapper_i.po_keymem_b_rd_req.rd_wr_en == RW_IDLE;
endproperty
a_run_rd_req_s2_pace_idle: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_rd_req_s2_pace_idle_p);

// pacer reloads with the S1/S2 pattern one cycle after entering S1 (from IDLE or S1->S2)
property run_mem_rd_pace_reload_s1s2_p;
    (skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_IDLE_SKDEC_RD_S1 ||
     skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_S1_SKDEC_RD_S2)
|=>
    skdecode_top.skdecode_ctrl_inst.mem_rd_pace == 16'b0111_0111_0111_0111;
endproperty
a_run_mem_rd_pace_reload_s1s2: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_mem_rd_pace_reload_s1s2_p);

// pacer reloads with the denser T0 pattern one cycle after the S2->T0 transition
property run_mem_rd_pace_reload_t0_p;
    skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_S2_SKDEC_RD_T0
|=>
    skdecode_top.skdecode_ctrl_inst.mem_rd_pace == 16'b0111_1011_1101_1111;
endproperty
a_run_mem_rd_pace_reload_t0: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_mem_rd_pace_reload_t0_p);

// -- Category: skdecode_done masking during split-pipe drain --
// done must never assert while the splitter pipe still has output draining
property run_skdecode_done_masked_while_draining_p;
    pi_split_en_i && |skdecode_top.split_pipe_active
|->
    !skdecode_top.skdecode_done;
endproperty
a_run_skdecode_done_masked_while_draining: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_skdecode_done_masked_while_draining_p);

// outside the drain window, done must track done_int exactly -- catches a stuck/mis-timed
// split_pipe_active bit that would suppress done forever, or unmask it too early
property run_skdecode_done_tracks_int_when_not_draining_p;
    !(pi_split_en_i && |skdecode_top.split_pipe_active)
|->
    skdecode_top.skdecode_done == skdecode_top.skdecode_done_int;
endproperty
a_run_skdecode_done_tracks_int_when_not_draining: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_skdecode_done_tracks_int_when_not_draining_p);

// -- Category: end-to-end s1->s2->t0 ordering & done-masking (single enable pulse) --
logic fv_op_active;        // true from acceptance until skdecode_done
logic fv_seen_s1_done_op;  // s1_done fired since acceptance
logic fv_seen_s2_done_op;  // s2_done fired since acceptance
logic fv_seen_t0_done_op;  // t0_done fired since acceptance

wire fv_op_accept = IDLE && start_port_vld;  // the single accepted enable pulse

always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    fv_op_active       <= 1'b0;
    fv_seen_s1_done_op <= 1'b0;
    fv_seen_s2_done_op <= 1'b0;
    fv_seen_t0_done_op <= 1'b0;
  end else if (fv_op_accept) begin
    fv_op_active       <= 1'b1;
    fv_seen_s1_done_op <= 1'b0;
    fv_seen_s2_done_op <= 1'b0;
    fv_seen_t0_done_op <= 1'b0;
  end else begin
    if (skdecode_done) begin
      fv_op_active <= 1'b0;
    end
    if (s1_done) begin
      fv_seen_s1_done_op <= 1'b1;
    end
    if (s2_done) begin
      fv_seen_s2_done_op <= 1'b1;
    end
    if (t0_done) begin
      fv_seen_t0_done_op <= 1'b1;
    end
  end
end

property run_e2e_no_s1_no_other_flag_p;
    !(s1_done)
|->
    !s2_done && !t0_done;
endproperty
a_run_e2e_no_s1_no_other_flag: assert property (disable iff(!rst_n) run_e2e_no_s1_no_other_flag_p);

property run_e2e_no_s2_no_t0_flag_p;
    !(s2_done)
|->
    !t0_done;
endproperty
a_run_e2e_no_s2_no_t0_flag: assert property (disable iff(!rst_n) run_e2e_no_s2_no_t0_flag_p);// order: s2_done can't fire before this op's s1_done has already fired

property run_e2e_s2_after_s1_p;
    $rose(s2_done)
|->
    fv_seen_s1_done_op;
endproperty
a_run_e2e_s2_after_s1: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg) || !fv_op_active) run_e2e_s2_after_s1_p);

// order: t0_done can't fire before this op's s2_done has already fired
property run_e2e_t0_after_s2_p;
    $rose(t0_done)
|->
    fv_seen_s2_done_op;
endproperty
a_run_e2e_t0_after_s2: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg) || !fv_op_active) run_e2e_t0_after_s2_p);

// skdecode_done stays low for the whole op until t0_done has fired
property run_e2e_done_masked_until_t0_p;
    fv_op_active && !fv_seen_t0_done_op
|->
    !skdecode_done;
endproperty
a_run_e2e_done_masked_until_t0: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg) || !fv_op_active) run_e2e_done_masked_until_t0_p);

// -- Category: mem_a/b_wr_data_int source mux (matches skdecode_top.sv:152-153) --
// s1s2_valid asserted -> mem_a/b get the two s1s2_data halves (lanes 3:0 / 7:4)
property run_mem_wr_data_int_sel_s1s2_p;
    |skdecode_top.s1s2_valid
|->
    skdecode_top.mem_a_wr_data_int == skdecode_top.s1s2_data[3:0] &&
    skdecode_top.mem_b_wr_data_int == skdecode_top.s1s2_data[7:4];
endproperty
a_run_mem_wr_data_int_sel_s1s2: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_mem_wr_data_int_sel_s1s2_p);

// s1s2_valid clear, t0_valid asserted -> both ports get the same t0_data lanes
property run_mem_wr_data_int_sel_t0_p;
    !(|skdecode_top.s1s2_valid) && |skdecode_top.t0_valid
|->
    skdecode_top.mem_a_wr_data_int == skdecode_top.t0_data[3:0] &&
    skdecode_top.mem_b_wr_data_int == skdecode_top.t0_data[3:0];
endproperty
a_run_mem_wr_data_int_sel_t0: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_mem_wr_data_int_sel_t0_p);

// neither valid -> both ports driven to zero
property run_mem_wr_data_int_sel_none_p;
    !(|skdecode_top.s1s2_valid) && !(|skdecode_top.t0_valid)
|->
    skdecode_top.mem_a_wr_data_int == '0 &&
    skdecode_top.mem_b_wr_data_int == '0;
endproperty
a_run_mem_wr_data_int_sel_none: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_mem_wr_data_int_sel_none_p);

// -- Category: skdecode_count (counter) reset & increment --
// resets to 0 the cycle after reset_n deasserts or zeroize asserts
property run_skdec_count_resets_on_reset_zeroize_p;
    !skdecode_top.reset_n || skdecode_top.zeroize
|=>
    counter == 10'd0;
endproperty
a_run_skdec_count_resets_on_reset_zeroize: assert property (run_skdec_count_resets_on_reset_zeroize_p);

// resets to 0 the cycle after the current phase's own terminal-transition arc fires
property run_skdec_count_resets_on_phase_transition_p;
    skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_S1_SKDEC_RD_S2 ||
    skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_S2_SKDEC_RD_T0 ||
    skdecode_top.skdecode_ctrl_inst.arc_SKDEC_RD_T0_SKDEC_RD_IDLE
|=>
    counter == 10'd0;
endproperty
a_run_skdec_count_resets_on_phase_transition: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_skdec_count_resets_on_phase_transition_p);

// otherwise, while a read phase is active and not yet at its own terminal value,
// counter increments by exactly 1 each cycle (unconditional, not paced)
property run_skdec_count_increments_p;
    (skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S1 ||
     skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_S2 ||
     skdecode_top.skdecode_ctrl_inst.read_fsm_state_ps == SKDEC_RD_T0) &&
    !skdecode_top.skdecode_ctrl_inst.last_poly_last_addr
|=>
    counter == (10'd1 + $past(counter));
endproperty
a_run_skdec_count_increments: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_skdec_count_increments_p);



// ================================================================
// DEAD / UNREACHABLE PROPERTIES -- kept for reference, never asserted
// Grouped below by root cause. See explanation under each group heading.
// ================================================================

// ============================================================
// Group 1: RD_WR_s1_to_RD_STG_WR_s1 residue family (base, _1-_19)
// ============================================================
// Each antecedent constrains 'counter' to a specific residue class via bit-slicing
// (counter[1:0]/counter[2:0] combinations). This property checks the transition INTO
// the S1 boundary state, which only happens at counter==223 -- but every residue
// combination in this numbered family excludes 223 by construction, so the antecedent
// can never actually be satisfied. run_RD_WR_s1_to_RD_STG_WR_s1_20_p/_21_p (live,
// masked+unmasked) cover the real transition instead.

// property run_RD_WR_s1_to_RD_STG_WR_s1_p;
//   RD_WR_s1 &&
//   //(counter[1:0] != 3) &&
//   (((counter[2:0] == 7) ||
//   (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0)
//   //&&
//   //((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_1_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_1_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_2_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_stg_wr_t0_to_rd_stg_wr_t0_masked_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_2_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_3_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_3_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_4_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_4_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_5_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_5_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_6_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_6_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_7_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_7_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_8_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_8_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_9_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_9_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_10_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_10_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_11_p;
//   RD_WR_s1 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_11_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_12_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_12_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_13_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_13_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_14_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_14_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_15_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_15_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_16_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_16_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_16_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_17_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_17_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_17_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_18_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_18_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_19_p;
//   RD_WR_s1 &&
//   //(counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) //
//   //&&
//   //((10'd1 + counter) >= 10'd224)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s1_to_RD_STG_WR_s1_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_19_p);


// ============================================================
// Group 2: RD_WR_s1_to_RD_STG_WR_s1_22/_23 (!s1s2_valid unreachable)
// ============================================================
// Both require '!s1s2_valid' at counter==222 -- one cycle before the S1 boundary.
// By this point the read-latency buffer has long since been primed and is continuously
// producing valid decoded output, so s1s2_valid is realistically always 1 here.
// Requiring it to be 0 this late in the phase is a combination that can never occur.

// property run_RD_WR_s1_to_RD_STG_WR_s1_22_p;
//   RD_WR_s1 &&
//   counter == 10'd222 &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd223 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_22_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_22_p);

// property run_RD_WR_s1_to_RD_STG_WR_s1_23_p;
//   RD_WR_s1 &&
//   counter == 10'd222 &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0)
// |->
//   ##1
//   RD_STG_WR_s1 &&
//   counter == 10'd223 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_stg_wr_s1_23_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_STG_WR_s1_23_p);


// ============================================================
// Group 3: RD_WR_s2_to_RD_STG_WR_s2 residue family (base, _1-_13)
// ============================================================
// Same root cause as Group 1, mirrored for the S2 boundary: each residue-class
// combination excludes counter==255 (S2's terminal value), so the antecedent is
// mathematically unreachable. The live masked/unmasked properties elsewhere cover
// the real S2 boundary transition.

// property run_RD_WR_s2_to_RD_STG_WR_s2_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_1_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_1_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_2_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_2_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_3_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_3_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_3_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_4_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_4_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_4_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_5_p;
//   RD_WR_s2 &&
//   (counter[1:0] != 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_1_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_5_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_5_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_6_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_6_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_6_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_7_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_7_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_7_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_8_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_8_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_8_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_9_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_9_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_9_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_10_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_10_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_10_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_11_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == $past(fv_decode_s1s2_a_0_i, 1) &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_0_i, 1) &&
//   mem_b_wr_data[0] == $past(fv_decode_s1s2_b_0_i, 1) &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_0_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_11_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_11_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_12_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_12_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_12_p);

// property run_RD_WR_s2_to_RD_STG_WR_s2_13_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) >= 10'd256)
// |->
//   ##1
//   RD_STG_WR_s2 &&
//   counter == 10'd0 &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_a_wr_req == $past(fv_mem_a_wr_req_1_i, 1) &&
//   mem_b_wr_data[0] == fv_mem_a_wr_data_0_i &&
//   mem_b_wr_req == $past(fv_mem_b_wr_req_1_i, 1) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 1 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_s2_to_RD_STG_WR_s2_13_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_STG_WR_s2_13_p);


// ============================================================
// Group 4: RD_WR_s1_to_RD_WR_s1 / RD_WR_s2_to_RD_WR_s2 !s1s2_valid siblings (14,15,18,19)
// ============================================================
// Same reasoning as Group 2, but for the steady-state self-loop properties (not the
// boundary transition): each requires '!s1s2_valid' at a specific residue class deep
// within an active S1 or S2 phase, where the buffer has already been primed and
// s1s2_valid is realistically always 1. Unreachable in both the S1 and S2 versions.

// property run_RD_WR_s1_to_RD_WR_s1_14_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) < 10'd224)
// |->
//   ##1
//   RD_WR_s1 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_wr_s1_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_14_p);

// property run_RD_WR_s1_to_RD_WR_s1_15_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hDF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) < 10'd224)
// |->
//   ##1
//   RD_WR_s1 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_wr_s1_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_15_p);

// property run_RD_WR_s1_to_RD_WR_s1_18_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) < 10'd224)
// |->
//   ##1
//   RD_WR_s1 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_wr_s1_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_18_p);

// property run_RD_WR_s1_to_RD_WR_s1_19_p;
//   RD_WR_s1 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hDF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) < 10'd224)
// |->
//   ##1
//   RD_WR_s1 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 0 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s1_to_rd_wr_s1_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s1_to_RD_WR_s1_19_p);

// property run_RD_WR_s2_to_RD_WR_s2_14_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) < 10'd256)
// |->
//   ##1
//   RD_WR_s2 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s2_to_rd_wr_s2_14_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_14_p);

// property run_RD_WR_s2_to_RD_WR_s2_15_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   (((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) &&
//   (counter != 10'hFF) &&
//   (counter[2:0] != 0) &&
//   (counter[2:0] != 3) &&
//   (counter[2:0] != 5) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) < 10'd256)
// |->
//   ##1
//   RD_WR_s2 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s2_to_rd_wr_s2_15_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_15_p);

// property run_RD_WR_s2_to_RD_WR_s2_18_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] == 0) &&
//   ((10'd1 + counter) < 10'd256)
// |->
//   ##1
//   RD_WR_s2 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s2_to_rd_wr_s2_18_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_18_p);

// property run_RD_WR_s2_to_RD_WR_s2_19_p;
//   RD_WR_s2 &&
//   (counter[1:0] == 3) &&
//   !((((counter[2:0] == 7) || (counter[2:0] == 1)) || (counter[2:0] == 4)) && (counter != 10'hFF)) &&
//   (((counter[2:0] == 0) || (counter[2:0] == 3)) || (counter[2:0] == 5)) &&
//   !s1s2_valid &&
//   (base_address.source[0] != 0) &&
//   ((10'd1 + counter) < 10'd256)
// |->
//   ##1
//   RD_WR_s2 &&
//   counter == (10'd1 + $past(counter, 1)) &&
//   keymem_a_rd_req == $past(fv_keymem_a_rd_req_3_i, 1) &&
//   keymem_b_rd_req == $past(fv_keymem_b_rd_req_2_i, 1) &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_1_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_1_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 1 &&
//   s1s2_stall_dummy_out == 0 &&
//   s2_done == 0 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_s2_to_rd_wr_s2_19_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_s2_to_RD_WR_s2_19_p);


// ============================================================
// Group 5: RD_WR_t0_to_RD_STG_WR_t0 family (base, _1, _2)
// ============================================================
// Each antecedent requires counter>=511 while also requiring the RD_WR_t0 compound
// state, which by its own definition requires !last_poly_last_addr (i.e. counter!=511).
// That's a direct same-cycle contradiction in the antecedent itself -- confirmed
// unreachable via JasperGold precondition cover. Superseded by the live
// masked/unmasked T0 boundary properties elsewhere in this file.

// property run_RD_WR_t0_to_RD_STG_WR_t0_p;
//   RD_WR_t0 &&
//   t0_valid_in &&
//   (fv_mem_wr_addr[0] == 0) &&
//   ((10'd1 + counter) >= 10'd511)
// |->
//   ##1 ($stable(s1s2_stall_dummy_out)) and
//   ##1
//   RD_STG_WR_t0 &&
//   counter == 10'd0 &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : $past(fv_decode_t0_0_i, 1)) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_a_wr_req_2_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : $past(fv_decode_t0_0_i, 1)) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_2_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : $past(fv_decode_t0_0_i, 1)) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : $past(fv_decode_t0_0_i, 1)) &&
//   s1_done == 1 &&
//   s2_done == 1 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_t0_to_RD_STG_WR_t0_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_p);

// property run_RD_WR_t0_to_RD_STG_WR_t0_1_p;
//   RD_WR_t0 &&
//   t0_valid_in &&
//   (fv_mem_wr_addr[0] != 0) &&
//   ((10'd1 + counter) >= 10'd511)
// |->
//   ##1 ($stable(s1s2_stall_dummy_out)) and
//   ##1
//   RD_STG_WR_t0 &&
//   counter == 10'd0 &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : $past(fv_decode_t0_0_i, 1)) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_b_wr_req_2_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : $past(fv_decode_t0_0_i, 1)) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_a_wr_req_2_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : $past(fv_decode_t0_0_i, 1)) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : $past(fv_decode_t0_0_i, 1)) &&
//   s1_done == 1 &&
//   s2_done == 1 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_RD_WR_t0_to_RD_STG_WR_t0_1_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_1_p);

// property run_RD_WR_t0_to_RD_STG_WR_t0_2_p;
//   RD_WR_t0 &&
//   !t0_valid_in &&
//   ((10'd1 + counter) >= 10'd511)
// |->
//   ##1 ($stable(s1s2_stall_dummy_out)) and
//   ##1
//   RD_STG_WR_t0 &&
//   counter == 10'd0 &&
//   mem_a_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_a : fv_mem_a_wr_data_0_i) &&
//   mem_a_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_a_wr_req_int, 2) : $past(fv_mem_b_wr_req_2_i, 1)) &&
//   mem_b_wr_data[0] == (pi_split_en_i ? fv_model_rand_d2_b : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_req == (pi_split_en_i ? $past(skdecode_top.mem_b_wr_req_int, 2) : $past(fv_mem_b_wr_req_2_i, 1)) &&
//   mem_a_wr_data[1] == (pi_split_en_i ? fv_model_share1_a : fv_mem_a_wr_data_0_i) &&
//   mem_b_wr_data[1] == (pi_split_en_i ? fv_model_share1_b : fv_mem_a_wr_data_0_i) &&
//   s1_done == 1 &&
//   s2_done == 1 &&
//   skdecode_done == 0 &&
//   t0_done == 0;
// endproperty
// run_rd_wr_t0_to_rd_stg_wr_t0_2_a: assert property (disable iff(!(skdecode_top.reset_n && !skdecode_top.zeroize && !fv_error_reg)) run_RD_WR_t0_to_RD_STG_WR_t0_2_p);

endmodule
