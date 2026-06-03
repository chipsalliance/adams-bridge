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


module fv_skencode_constraints
    import abr_params_pkg::*;
    import skdecode_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = 15,
    parameter MLDSA_Q        = 23'd8380417,
    parameter MLDSA_L        = 'h7,
    parameter MLDSA_K        = 'h8,
    parameter MLDSA_N        = 'd256,
    parameter REG_SIZE       = 24,
    parameter AHB_DATA_WIDTH = 32
) (
    //#$ports
    input                            pi_clk,
    input                            pi_reset_n,
    input                            pi_zeroize,
    input                            pi_skencode_enable,
    input [MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr,
    input [MEM_ADDR_WIDTH-1:0]       pi_src_base_addr,
    input [3:0][REG_SIZE-1:0]        pi_mem_a_rd_data,
    input [3:0][REG_SIZE-1:0]        pi_mem_b_rd_data,
    input mem_if_t                   po_keymem_a_wr_req,
    input mem_if_t                   po_mem_a_rd_req,
    input mem_if_t                   po_mem_b_rd_req,
    input logic [AHB_DATA_WIDTH-1:0] po_keymem_a_wr_data,
    input logic                      po_skencode_error,
    input logic                      po_skencode_done
    //$#//
);

    //#$localparams
    localparam THE_LAST_ADDR = ((MLDSA_K*MLDSA_N)/4)+((MLDSA_L*MLDSA_N)/4)-1;
    localparam THE_LAST_API = ((MLDSA_K+MLDSA_L)*MLDSA_N*3)/32;
    localparam IDLE = 3'b000;
    localparam READ = 3'b001;
    localparam READ_and_ENC = 3'b010;
    localparam READ_ENC_and_CONSUME = 3'b011;
    localparam ENC_and_CONSUME = 3'b100;
    localparam CONSUME = 3'b101;
    localparam CONSUME_LAST = 3'b110;
    localparam DONE = 3'b111;
    localparam WAIT_BUFFER = 3'b001;
    localparam WRITE = 3'b010;
    localparam STALL = 3'b011;
    localparam GET_LAST = 3'b100;
    //$#//


default clocking default_clk @(posedge pi_clk); endclocking

logic fv_ongoing_computation;
always_ff @(posedge pi_clk) begin
    if(!pi_reset_n) begin
        fv_ongoing_computation <= 1'b0;
    end else if(!fv_ongoing_computation || po_skencode_done) begin
        fv_ongoing_computation <= pi_skencode_enable;
    end
end

// Set enable only when it is not busy
assume_only_enable_when_idle : assume property (
    pi_skencode_enable
|->
    !fv_ongoing_computation || po_skencode_done
);

property enable_signal_set;
    pi_reset_n
|->
    s_eventually(pi_skencode_enable);
endproperty

assume_enable_signal_set: assume property (disable iff(!pi_reset_n) enable_signal_set);


endmodule

