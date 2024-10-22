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

//Sequencer for MLDSA
//MLDSA functions
//  Signing initial steps
//  Signing validity checks
//  Signing signature generation

`include "mldsa_config_defines.svh"

module ntt_arbiter 
    import mldsa_params_pkg::*;
    import mldsa_ctrl_pkg::*;
    import ntt_defines_pkg::*;
  (
    input logic clk,
    input logic reset_n,

    // Inputs from controller
    input logic [1:0] ntt_enable,           // ntt_enable[0] for NTT_0, ntt_enable[1] for NTT_1
    input mldsa_ntt_mode_e [1:0] ntt_mode,
    input ntt_mem_addr_t [1:0] ntt_mem_base_addr,
    input pwo_mem_addr_t [1:0] pwo_mem_base_addr,

    // Inputs from sampler
    input logic [1:0] sampler_ntt_dv, 

    // Inputs from NTT
    input logic ntt_busy,
    input logic ntt_done,

    input mem_if_t ntt_mem_wr_req_i,
    input mem_if_t ntt_mem_rd_req_i,
    input logic [MLDSA_MEM_DATA_WIDTH-1:0] ntt_mem_wr_data_i,

    input mem_if_t pwm_a_rd_req_i,
    input mem_if_t pwm_b_rd_req_i,


    // Outputs to memory MUX
    output mem_if_t [1:0] ntt_mem_wr_req_o,
    output mem_if_t [1:0] ntt_mem_rd_req_o,
    output logic [1:0][MLDSA_MEM_DATA_WIDTH-1:0] ntt_mem_wr_data_o,

    output mem_if_t [1:0] pwm_a_rd_req_o,
    output mem_if_t [1:0] pwm_b_rd_req_o,

    // Outputs to controller
    output logic [1:0] ntt_busy_o,
    output logic [1:0] ntt_done_o,

    // Outputs to NTT
    output logic ntt_enable_o,
    output mode_t ntt_mode_o,
    output logic accumulate_o,
    output logic sampler_valid_o,
    output logic sampler_ntt_mode_o,
    output ntt_mem_addr_t ntt_mem_base_addr_o,
    output pwo_mem_addr_t pwo_mem_base_addr_o
  );
  
  // Internal registers
  logic [1:0] using_ntt;
  
  logic ntt_enable_r;
  mldsa_ntt_mode_e ntt_mode_r;
  logic accumulate_r;
  logic sampler_valid_r;
  ntt_mem_addr_t ntt_mem_base_addr_r;
  pwo_mem_addr_t pwo_mem_base_addr_r;
  
  // Latch inputs and select NTT based on ntt_enable signals
  always_ff @(posedge clk or negedge reset_n) begin
      if (!reset_n) begin
          using_ntt <= 0;
          ntt_enable_r <= 0;
          ntt_mode_r <= MLDSA_NTT_NONE;
          ntt_mem_base_addr_r <= '0;
          pwo_mem_base_addr_r <= '0;
      end else begin
            ntt_enable_o <= ntt_enable[0] | ntt_enable[1];
            if (ntt_enable[0]) begin
                using_ntt <= 1;
                ntt_mode_r <= ntt_mode[0];
                ntt_mem_base_addr_r <= ntt_mem_base_addr[0];
                pwo_mem_base_addr_r <= pwo_mem_base_addr[0];
            end else if (ntt_enable[1]) begin
                using_ntt <= 2;
                ntt_mode_r <= ntt_mode[1];
                ntt_mem_base_addr_r <= ntt_mem_base_addr[1];
                pwo_mem_base_addr_r <= pwo_mem_base_addr[1];
            end
      end
  end
  
  // Output logic to NTT engine
  always_comb begin
      if (using_ntt[0]) begin
          //ntt_enable_o = ntt_enable_r;
          ntt_mem_base_addr_o = ntt_mem_base_addr_r;
          pwo_mem_base_addr_o = pwo_mem_base_addr_r;
      end else begin
        //   ntt_enable_o = ntt_enable[1];
          ntt_mem_base_addr_o = ntt_mem_base_addr[1];
          pwo_mem_base_addr_o = pwo_mem_base_addr[1];
      end
  end
  
  // Output logic to controller
  always_comb begin
      ntt_busy_o = 2'b00;
      ntt_done_o = 2'b00;
      if (using_ntt[0]) begin
          ntt_busy_o[0] = ntt_busy | (using_ntt[0] & ntt_enable_o);
          ntt_done_o[0] = ntt_done;
      end else begin
          ntt_busy_o[1] = ntt_busy | (using_ntt[1] & ntt_enable_o);
          ntt_done_o[1] = ntt_done;
      end
  end

  always_comb begin

    ntt_mem_wr_req_o[0] = ntt_mem_wr_req_i;
    ntt_mem_rd_req_o[0] = ntt_mem_rd_req_i;
    ntt_mem_wr_data_o[0] = ntt_mem_wr_data_i;
    pwm_a_rd_req_o[0] = pwm_a_rd_req_i;
    pwm_b_rd_req_o[0] = pwm_b_rd_req_i;

    ntt_mem_wr_req_o[1] = '{rd_wr_en: RW_IDLE, addr: '0};
    ntt_mem_rd_req_o[1] = '{rd_wr_en: RW_IDLE, addr: '0};
    ntt_mem_wr_data_o[1] = '0;
    pwm_a_rd_req_o[1]    = '{rd_wr_en: RW_IDLE, addr: '0};
    pwm_b_rd_req_o[1]    = '{rd_wr_en: RW_IDLE, addr: '0};

  end


    always_comb begin
        ntt_mode_o = '0;
        accumulate_o = '0;
        sampler_valid_o = 0;
        sampler_ntt_mode_o = 0;

      unique case (ntt_mode_r) inside
        MLDSA_NTT_NONE: begin
        end
        MLDSA_NTT: begin
            ntt_mode_o = ct;
        end
        MLDSA_INTT: begin
            ntt_mode_o = gs;
        end
        MLDSA_PWM_SMPL: begin
            ntt_mode_o = pwm;
            sampler_valid_o = using_ntt[0] ? sampler_ntt_dv[0]: '0;
            sampler_ntt_mode_o = 1;
        end
        MLDSA_PWM_ACCUM_SMPL: begin
            ntt_mode_o = pwm;
            accumulate_o = 1;
            sampler_valid_o = using_ntt[0]? sampler_ntt_dv[0]: '0;
            sampler_ntt_mode_o = 1;
        end
        MLDSA_PWM: begin
            ntt_mode_o = pwm;
            sampler_valid_o = 1;
        end
        MLDSA_PWM_ACCUM: begin
            ntt_mode_o = pwm;
            accumulate_o = 1;
            sampler_valid_o = 1;
        end
        MLDSA_PWA: begin
            ntt_mode_o = pwa;
            sampler_valid_o = 1;
        end
        MLDSA_PWS: begin
            ntt_mode_o = pws;
            sampler_valid_o = 1;
        end
        default: begin
        end
      endcase 
    end
  
  endmodule
  