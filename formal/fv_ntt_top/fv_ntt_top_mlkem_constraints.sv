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


    module fv_ntt_top_mlkem_constraints
        import abr_params_pkg::*;
        import ntt_defines_pkg::*;
    #(
        parameter REG_SIZE         = 24,
        parameter NTT_REG_SIZE     = REG_SIZE-1,
        parameter MLDSA_Q          = 23'd8380417,
        parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q+1)/2,
        parameter MLDSA_N          = 256,
        parameter MLDSA_LOGN       = $clog2(MLDSA_N),
        parameter MEM_ADDR_WIDTH   = 15,
        parameter MEM_DATA_WIDTH   = 4*REG_SIZE,
        parameter WIDTH            = 46,
        parameter SRAM_LATENCY     = 1
        // matches ntt_top.sv SRAM_LATENCY default; used to model pi_mem_rd_data_valid timing
        //#$localparams
        //$#//
    ) (
        //#$ports
        input                            pi_clk,
        input                            pi_reset_n,
        input                            pi_zeroize,
        input mode_t                     pi_mode,
        input                            pi_ntt_enable,
        input ntt_mem_addr_t             pi_ntt_mem_base_addr,
        input pwo_mem_addr_t             pi_pwo_mem_base_addr,
        input                            pi_accumulate,
        input                            pi_mlkem,
        input                            pi_sampler_valid,
        input                            pi_shuffle_en,
        input [5:0]                      pi_random,
        input mem_if_t                   po_mem_wr_req,
        input mem_if_t                   po_mem_rd_req,
        input logic [ABR_MEM_DATA_WIDTH-1:0] po_mem_wr_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_mem_rd_data,
        input                            pi_mem_rd_data_valid,
        input mem_if_t                   po_pwm_a_rd_req,
        input mem_if_t                   po_pwm_b_rd_req,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_a_rd_data,
        input [ABR_MEM_DATA_WIDTH-1:0]       pi_pwm_b_rd_data,
        input logic                      po_ntt_busy,
        input logic                      po_ntt_done
        //$#//
    );

        default clocking default_clk @(posedge pi_clk); endclocking


    // Constraints to make base address stable
    property stable_base_address;
    //disable iff(pi_reset_n)
        ##0 pi_ntt_enable
    |=>
        ##0 $stable(pi_ntt_mem_base_addr)
    ;endproperty
    //assume_stable_base_address:assume property (stable_base_address);

    //aux logic for stable mode enable and done signal
    logic fv_ongoing;

    always_ff@(posedge pi_clk or negedge pi_reset_n)
    begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_ongoing <= 1'b0;
        end else if(pi_ntt_enable) begin
            fv_ongoing <= 1'b1;
        end else if(po_ntt_done) begin
            fv_ongoing <= 1'b0;
        end
    end

    //Constraints to make control signals and base addresses stable during operation
        property stable_mode;
            ##0 fv_ongoing
        |->
            ##0 $stable(pi_mode)
            ##0 $stable(pi_shuffle_en)
            ##0 $stable(pi_mlkem)
            ##0 $stable(pi_accumulate)
            ##0 $stable(pi_ntt_mem_base_addr)
            ##0 $stable(pi_pwo_mem_base_addr)
        ;endproperty
        assume_stable_mode : assume property(stable_mode);

    // Aux logic for SRAM read latency: response `pi_mem_rd_data_valid` is the requested
    // read-enable delayed by SRAM_LATENCY cycles
    logic [SRAM_LATENCY-1:0] fv_mem_rd_data_valid_latency;
    always_ff@(posedge pi_clk, negedge pi_reset_n)
    begin
        if (!pi_reset_n || pi_zeroize)
        begin
            fv_mem_rd_data_valid_latency <= '0;
        end
        else
        begin
            fv_mem_rd_data_valid_latency <= {(po_mem_rd_req.rd_wr_en == RW_READ),
              fv_mem_rd_data_valid_latency} >> 1;
        end
    end

    property mem_rd_data_valid_latency;
        ##0 pi_mem_rd_data_valid == fv_mem_rd_data_valid_latency[0]
    ;endproperty
    assume_mem_rd_data_valid_latency : assume property(mem_rd_data_valid_latency);

    // Constraint to not enable ntt while ongoing unless done is asserted
    property ntt_enable_not_while_ongoing;
            ##0 pi_ntt_enable
    |->
            ##0 !fv_ongoing || po_ntt_done
    ;endproperty
    assume_ntt_enable_not_while_ongoing : assume property(ntt_enable_not_while_ongoing);

    // Constraint for base addresses alignment and relative distance
    // adding this because assert_num_rd_always_64 fails without this assumption. (constraint for
    // mem_rd_base_addr is needed)
    logic signed [ABR_MEM_ADDR_WIDTH:0] fv_src_addr;
    assign fv_src_addr = pi_ntt_mem_base_addr.src_base_addr;
    logic signed [ABR_MEM_ADDR_WIDTH:0] fv_interim_addr;
    assign fv_interim_addr = pi_ntt_mem_base_addr.interim_base_addr;
    logic signed [ABR_MEM_ADDR_WIDTH:0] fv_dest_addr;
    assign fv_dest_addr = pi_ntt_mem_base_addr.dest_base_addr;

    property valid_base_address;
        fv_ongoing
    |->
        (fv_dest_addr == fv_src_addr || fv_dest_addr >= fv_src_addr + 64 || fv_dest_addr <=
          fv_src_addr - 64) &&
        (fv_interim_addr <= fv_src_addr - 64 || fv_interim_addr >= fv_src_addr + 64) &&
        (fv_interim_addr <= fv_dest_addr - 64 || fv_interim_addr >= fv_dest_addr + 64)&&
        fv_src_addr[5:0] == '0 &&
        fv_dest_addr[5:0] == '0 &&
        fv_interim_addr[5:0] == '0 ;
    endproperty
    assume_valid_base_address: assume property (valid_base_address);

    //Constraint to have sampler_valid eventually asserted when ongoing
    property sampler_valid;
        fv_ongoing
    |->
        s_eventually(pi_sampler_valid)
    ;endproperty
    assume_sampler_valid : assume property(sampler_valid);

    //Constraint to have sampler_valid eventually asserted for 64 cycles
    property sampler_valid_duration;
        fv_ongoing &&
        !pi_sampler_valid
        ##1
        fv_ongoing &&
        pi_sampler_valid
    |=>
        pi_sampler_valid[*63]
    ;endproperty
    assume_sampler_valid_duration : assume property(sampler_valid_duration);


    // Sampler Valid: Only applies to PWM/PWA/PWS modes. Can randomly be deasserted in each round
    // to model sampler behavior
    property sampler_valid_only_in_pwo;
        !(pi_mode == pwa|| pi_mode == pwm || pi_mode == pws || (pi_mlkem && pi_mode == pairwm))
    |->
        pi_sampler_valid
    ;endproperty
    //assume_sampler_valid_only_in_pwo: assume property(sampler_valid_only_in_pwo);

    // Constraint for only legal modes, disabled because assertion check_mem_rd_req_other becomes
    // unreachable with this
    property only_legal_modes;
        ##0 pi_mode != 3'b111 && pi_mode != 3'b110
    ;endproperty
   // assume_only_legal_modes : assume property(only_legal_modes);

    // Constriant to eventually have busy signal deasserted when ongoing
    property busy_not_busy;
        fv_ongoing
    |->
        s_eventually(!ntt_ctrl_inst0.pwo_busy && !ntt_ctrl_inst0.ntt_busy)
    ;endproperty
    assume_busy_not_busy : assume property(busy_not_busy);


    endmodule

