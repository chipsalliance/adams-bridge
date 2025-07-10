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

//======================================================================
// ntt_mem_adapter.sv
// Adapter between Memory and NTT interface
// This module handles data conversion between memory and NTT interface
// Write case:
// AHB sends 256 txns of 32-bit each. Memory has 256 slots for these coeffs per poly //TODO: masking shares!
// NTT mem rd req expects 64 addresses of 96-bits each. This interface concatenates 4 coeffs into 1 data and sends to NTT
// Read case:
// NTT mem wr req sends 64 addresses of 96-bits each. This interface splits them and writes to 4 addresses in the same cycle
// AHB sends 256 txns of 32-bit each for reads

// Ctrl data:
// Mem has 2 extra slots for ntt_en and mode. 
// Enforce CPU to program polys first, then mode and then ntt_en. Better if CPU can emulate ntt_en pulse

// Masking:
// In masking, mem is 384 bits wide (4 * 48 * 2). 
//======================================================================

module ntt_ahb_mem_adapter
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter MEM_ADDR_WIDTH = 14, // Memory address width
    parameter MEM_DATA_WIDTH = 96, // Memory data width
    parameter MASKED_MEM_DATA_WIDTH = 384, // Memory data width for masking
    parameter AHB_ADDR_WIDTH = 14, // AHB address width
    parameter AHB_DATA_WIDTH = 64 // AHB data width
)
(
    input wire clk,
    input wire rst,

    //AHB slv interface
    input wire dv,
    input wire write,
    input wire [AHB_DATA_WIDTH-1:0] wdata,
    input wire [AHB_ADDR_WIDTH-1:0] addr,
    output logic [AHB_DATA_WIDTH-1:0] rdata,
    output logic hold,
    output logic err,

    //NTT trig interface
    input logic [AHB_DATA_WIDTH-1:0] mem_ctrl_data_i, //ctrl reg
    input logic [AHB_DATA_WIDTH-1:0] mem_enable_data_i, //enable reg

    output logic ntt_en_o,
    output mode_t ntt_mode_o,
    output logic ntt_accumulate_o,
    output logic ntt_sampler_valid_o,
    output logic ntt_masking_en_o,
    output logic ntt_shuffle_en_o,
    //TODO: random bits inputs

    //Memory interface
    output logic ahb_ena,
    output logic ahb_wea,
    output logic [AHB_ADDR_WIDTH-1:0] ahb_addr,
    output logic [AHB_DATA_WIDTH-1:0] ahb_wdata,
    input logic [AHB_DATA_WIDTH-1:0] ahb_rdata
);

logic rd_ack, wr_ack;

//Assign hold
always_comb begin
    rd_ack = dv & ~write;
    wr_ack = dv & write;
    hold = dv & ~(rd_ack | wr_ack);
end

//Assign err
assign err = 1'b0; // No error handling in this adapter

//AHB-mem interface
always_comb begin
    ahb_ena = dv & !write; //read enable
    ahb_wea = dv & write; //write enable
    ahb_addr = addr;

    ahb_wdata = wdata;
    rdata = ahb_rdata;
end

//Ctrl and enable data processing
always_comb begin
    ntt_en_o = mem_enable_data_i[0]; // Enable NTT
    ntt_mode_o = mem_ctrl_data_i[2:0]; // Mode of operation
    ntt_accumulate_o = mem_ctrl_data_i[3]; // Accumulate results
    ntt_sampler_valid_o = mem_ctrl_data_i[4]; // Sampler valid
    ntt_masking_en_o = mem_ctrl_data_i[5]; // Masking enabled
    ntt_shuffle_en_o = mem_ctrl_data_i[6]; // Shuffle enabled
end

endmodule