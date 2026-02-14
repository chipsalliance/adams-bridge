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


module fv_constraints_ct_mode_wip
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
    import ntt_ctrl_ct_mlkem_pkg::*;
   
#(
    parameter REG_SIZE         = 23,
    parameter RADIX            = 23,
    parameter MLDSA_Q          = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
    parameter MLDSA_N          = 256,
    parameter MLDSA_LOGN       = 8,
    parameter MEM_ADDR_WIDTH   = 15
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input mode_t                     pi_ntt_mode,
    input                            pi_ntt_enable,
    input                            pi_butterfly_ready,
    input                            pi_buf0_valid,
    input                            pi_sampler_valid,
    input                            pi_accumulate,
    input ntt_mem_addr_t             pi_ntt_mem_base_addr,
    input pwo_mem_addr_t             pi_pwo_mem_base_addr,
    input                            pi_shuffle_en,
    input [5:0]                      pi_random,
    input                            pi_masking_en,
    input                            pi_mlkem,
    input logic                      po_bf_enable,
    input logic [2:0]                po_opcode,
    input logic                      po_masking_en_ctrl,
    input logic                      po_buf_wren,
    input logic                      po_buf_rden,
    input logic [1:0]                po_buf_wrptr,
    input logic [1:0]                po_buf_rdptr,
    input logic [6:0]                po_twiddle_addr,
    input logic [MEM_ADDR_WIDTH-1:0] po_mem_rd_addr,
    input logic [MEM_ADDR_WIDTH-1:0] po_mem_wr_addr,
    input logic                      po_mem_rd_en,
    input logic                      po_mem_wr_en,
    input logic                      po_buf_wr_rst_count,
    input logic                      po_buf_rd_rst_count,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_a,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_b,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_rd_addr_c,
    input logic [MEM_ADDR_WIDTH-1:0] po_pw_mem_wr_addr_c,
    input logic                      po_pw_rden,
    input logic                      po_pw_wren,
    input logic                      po_busy,
    input logic                      po_done
    //$#//
);

    //#$localparams
    localparam NTT_NUM_ROUNDS = 4;
    localparam PWO_NUM_ROUNDS = 1;
    localparam NTT_READ_ADDR_STEP = 16;
    localparam NTT_WRITE_ADDR_STEP = 1;
    localparam INTT_READ_ADDR_STEP = 1;
    localparam INTT_WRITE_ADDR_STEP = 16;
    localparam PWO_READ_ADDR_STEP = 1;
    localparam PWO_WRITE_ADDR_STEP = 1;
    localparam MEM_LAST_ADDR = 63;
    //$#//
    /////////////////////////////////////////////
    default clocking default_clk @(posedge pi_clk); endclocking

// Constraint to only allow ct mode
  property wip_ntt_mode;
      (pi_ntt_mode == ct) ;
  endproperty
  assume_ntt_mode: assume property (wip_ntt_mode);

 //aux logic for butterfly latency
  logic [9:0] fv_butterflylatancy; 
  always_ff@(posedge pi_clk, negedge pi_reset_n)
  begin
     if(!pi_reset_n || pi_zeroize)
        fv_butterflylatancy <= '0;
     else 
  
     begin
      fv_butterflylatancy <= {po_bf_enable,fv_butterflylatancy[9:1]};
     end
  end

  property wip_butterfly_ready;
      pi_butterfly_ready == fv_butterflylatancy[0];
  endproperty
  assume_wip_butterfly_ready: assume property(wip_butterfly_ready);

//Constraint to have stable base address during aux_mode
  property stable_base_address;
      ##0 $stable(pi_ntt_mem_base_addr);
  endproperty
  assume_stable_base_address:assume property (stable_base_address);

//aux logic for stable mode enable and done signal
  logic aux_mode;
  always_ff@(posedge pi_clk or negedge pi_reset_n)
  begin
        if(!pi_reset_n || pi_zeroize)
                  aux_mode <= 1'b0;
        else if(pi_ntt_enable)
                  aux_mode <= 1'b1;
        else if(po_done)
                  aux_mode <= 1'b0;
  end

  //Constraint to have stable mode during aux_mode
  property stable_mode;
     ##1 aux_mode |-> ##0 $stable(pi_ntt_mode);
  endproperty
  assume_stable_mode : assume property(stable_mode);


  // Aux logic for count & count_reg
  logic [1:0]count;
  logic [1:0] count_reg;

  always_ff@(posedge pi_clk or negedge pi_reset_n)
    begin
          if(!pi_reset_n || pi_zeroize || po_buf_wr_rst_count)
      begin
          count <= '0;
          count_reg <= '0;
      end
           else if (po_buf_wren )
      begin
           count <= count + 1;
           count_reg <= count;
      end    
    end


 // Constraint for buf_valid assertion
  property buf0_valid_constraint;
    ##0 (count_reg == 3) |-> ##0 pi_buf0_valid;
  endproperty
  assume_buf0_valid_constraint: assume property (buf0_valid_constraint);

 // Constraint for no buf_valid assertion
  property No_buf0_valid_constraint;
     ##0(count_reg != 3) |-> ##0 !pi_buf0_valid;
  endproperty
  assume_No_buf0_valid_constraint: assume property (No_buf0_valid_constraint);

// Constraint to have stable shuffle_en during aux_mode
  stable_shuffle_en: assume property (
    ##1
    aux_mode
  |->
    $stable(pi_shuffle_en)
  );

  //Constraint to always de-assert masking_en
    property assume_masking_en_p;
    pi_masking_en == 0;
  endproperty
  assume_masking_en: assume property (assume_masking_en_p);

// Constraint to have stable mlkem
property wip_mlkem;
    $stable(pi_mlkem);
  endproperty
  assume_mlkem: assume property (wip_mlkem);

// Constraint for liveness assertions
  assume_ntt_enable: assume property (
    s_eventually(pi_ntt_enable)
  );

  
  logic signed [MEM_ADDR_WIDTH:0] src_addr;
  assign src_addr = pi_ntt_mem_base_addr.src_base_addr;
  logic signed [MEM_ADDR_WIDTH:0] interim_addr;
  assign interim_addr = pi_ntt_mem_base_addr.interim_base_addr;
  logic signed [MEM_ADDR_WIDTH:0] dest_addr;
  assign dest_addr = pi_ntt_mem_base_addr.dest_base_addr;

// Constraint for base addresses alignment and relative distance
  property valid_base_address;
     aux_mode
      |->
     (dest_addr == src_addr || dest_addr >= src_addr + 64 || dest_addr <= src_addr - 64) &&
     (interim_addr <= src_addr - 64 || interim_addr >= src_addr + 64) &&
     (interim_addr <= dest_addr - 64 || interim_addr >= dest_addr + 64);
  endproperty
  assume_valid_base_address: assume property (valid_base_address);
     
endmodule
bind ntt_ctrl fv_constraints_ct_mode_wip constraints_ct_mode_inst(
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_ntt_mode (ntt_mode),
    .pi_ntt_enable (ntt_enable),
    .pi_butterfly_ready (butterfly_ready),
    .pi_buf0_valid (buf0_valid),
    .pi_sampler_valid (sampler_valid),
    .pi_accumulate (accumulate),
    .pi_ntt_mem_base_addr (ntt_mem_base_addr),
    .pi_pwo_mem_base_addr (pwo_mem_base_addr),
    .pi_shuffle_en (shuffle_en),
    .pi_random (random),
    .pi_masking_en (masking_en),
    .pi_mlkem (mlkem),
    .po_bf_enable (bf_enable),
    .po_opcode (opcode),
    .po_masking_en_ctrl (masking_en_ctrl),
    .po_buf_wren (buf_wren),
    .po_buf_rden (buf_rden),
    .po_buf_wrptr (buf_wrptr),
    .po_buf_rdptr (buf_rdptr),
    .po_twiddle_addr (twiddle_addr),
    .po_mem_rd_addr (mem_rd_addr),
    .po_mem_wr_addr (mem_wr_addr),
    .po_mem_rd_en (mem_rd_en),
    .po_mem_wr_en (mem_wr_en),
    .po_buf_wr_rst_count (buf_wr_rst_count),
    .po_buf_rd_rst_count (buf_rd_rst_count),
    .po_pw_mem_rd_addr_a (pw_mem_rd_addr_a),
    .po_pw_mem_rd_addr_b (pw_mem_rd_addr_b),
    .po_pw_mem_rd_addr_c (pw_mem_rd_addr_c),
    .po_pw_mem_wr_addr_c (pw_mem_wr_addr_c),
    .po_pw_rden (pw_rden),
    .po_pw_wren (pw_wren),
    .po_busy (busy),
    .po_done (done)
);
