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
//
//======================================================================
// ntt_special_mem.sv
// 1. 64-bit with 256 slots per poly + 1 ctrl + 1 enable reg + 1 status
// 2. AHB side --> one wr, one rd interface with 64-bit data ports
// 3. NTT side --> one wr, one rd interface with 384-bit data ports
// Special adapter to convert between AHB and NTT interfaces:
// 1. AHB sends 256 txns of 64-bit each. Memory has 256 slots for these coeffs per poly
// 2. NTT mem rd req expects 64 addresses of 384-bits each. This interface concatenates 4 coeffs into 1 data and sends to NTT
// 3. NTT mem wr req sends 64 addresses of 384-bits each. This interface splits them and writes to 4 addresses in the same cycle
//======================================================================

module ntt_special_mem 
#(
    parameter ADDR_WIDTH = 12, //1024 + 3 regs
    parameter AHB_DATA_WIDTH = 64,
    // parameter NTT_ADDR_WIDTH = 15,
    parameter REG_SIZE = 24, // 24 bits per coeff
    parameter MASKED_REG_SIZE = 24*2,
    parameter NTT_DATA_WIDTH = MASKED_REG_SIZE*8,
    parameter RND_W = 236, //5*46 + 6
    parameter LFSR_W = RND_W / 2
)
(
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    // AHB interface
    input wire ahb_ena,
    input wire ahb_wea,
    input wire [ADDR_WIDTH-1:0] ahb_addr,
    input wire [AHB_DATA_WIDTH-1:0] ahb_data_in,
    output logic [AHB_DATA_WIDTH-1:0] ahb_data_out,

    // NTT interface
    input wire ntt_enb,
    input wire ntt_web,
    input wire [ADDR_WIDTH-4:0] ntt_rd_addr,
    input wire [ADDR_WIDTH-4:0] ntt_wr_addr,
    input wire [NTT_DATA_WIDTH-1:0] ntt_data_in,
    output logic [NTT_DATA_WIDTH-1:0] ntt_data_out,
    input logic masking_en_ctrl,

    // reg interface
    input logic ntt_done,
    output logic [AHB_DATA_WIDTH-1:0] ctrl_data,
    output logic [AHB_DATA_WIDTH-1:0] enable_data,
    output logic [AHB_DATA_WIDTH-1:0] base_addr_data,
    output logic [NTT_DATA_WIDTH-1:0] sampler_data,
    output logic lfsr_enable,
    output logic [1:0][LFSR_W-1:0] lfsr_seed
    // output logic [5:0] random_data,
    // output logic [4:0][45:0] rnd_i_data
);

localparam DEPTH = 2**ADDR_WIDTH;
reg [AHB_DATA_WIDTH-1:0] mem[DEPTH-1:0]; //mem[DEPTH-1] = status, mem[DEPTH-2] = enable, mem[DEPTH-3] = ctrl
logic masking_en;
logic pwm_mode;

always_comb begin
    base_addr_data = mem[DEPTH-4];
    ctrl_data = mem[DEPTH-3];
    enable_data = mem[DEPTH-2];
    masking_en = ctrl_data[5];
    pwm_mode = (ctrl_data[2:0] == 3'h2);

    sampler_data = {288'h0, mem[DEPTH-8][REG_SIZE-1:0], mem[DEPTH-7][REG_SIZE-1:0], mem[DEPTH-6][REG_SIZE-1:0], mem[DEPTH-5][REG_SIZE-1:0]};

    // random_data = mem[DEPTH-9][5:0];
    // rnd_i_data = {mem[DEPTH-14][45:0], mem[DEPTH-13][45:0], mem[DEPTH-12][45:0], mem[DEPTH-11][45:0], mem[DEPTH-10][45:0]};
    lfsr_enable = mem[DEPTH-9][0];
    lfsr_seed[0] = LFSR_W'({mem[DEPTH-11], mem[DEPTH-10]});
    lfsr_seed[1] = LFSR_W'({mem[DEPTH-13], mem[DEPTH-12]});
end

always_ff @(posedge clk or negedge reset_n) begin: reading_memory
    if (!reset_n) begin
        ahb_data_out <= '0;
        ntt_data_out <= '0;
    end
    else if (zeroize) begin
        ahb_data_out <= '0;
        ntt_data_out <= '0;
    end
    else begin
        if (ahb_ena) begin
            ahb_data_out <= mem[ahb_addr];
        end
        else begin
            ahb_data_out <= '0;
        end

        if (ntt_enb) begin
            ntt_data_out <= (masking_en & masking_en_ctrl & !pwm_mode) ? {mem[(ntt_rd_addr*8) + 7][MASKED_REG_SIZE-1:0], mem[(ntt_rd_addr*8) + 6][MASKED_REG_SIZE-1:0], mem[(ntt_rd_addr*8) + 5][MASKED_REG_SIZE-1:0], mem[(ntt_rd_addr*8) + 4][MASKED_REG_SIZE-1:0],
                             mem[(ntt_rd_addr*8) + 3][MASKED_REG_SIZE-1:0], mem[(ntt_rd_addr*8) + 2][MASKED_REG_SIZE-1:0], mem[(ntt_rd_addr*8) + 1][MASKED_REG_SIZE-1:0], mem[ntt_rd_addr*8][MASKED_REG_SIZE-1:0]}
                                                                        : NTT_DATA_WIDTH'({mem[(ntt_rd_addr*4) + 3][REG_SIZE-1:0], mem[(ntt_rd_addr*4) + 2][REG_SIZE-1:0], mem[(ntt_rd_addr*4) + 1][REG_SIZE-1:0], mem[ntt_rd_addr*4][REG_SIZE-1:0]});
        end
    end
end

always_ff @(posedge clk or negedge reset_n) begin: writing_memory
    if (!reset_n) begin
        for (int i = 0; i < DEPTH; i++) begin
            mem[i] <= '0;
        end
    end
    else if (zeroize) begin
        for (int i = 0; i < DEPTH; i++) begin
            mem[i] <= '0;
        end
    end
    else begin
        if (/*ahb_ena &&*/ ahb_wea) begin
            mem[ahb_addr] <= ahb_data_in;
        end

        if (/*ntt_enb &*/ ntt_web) begin
            if (masking_en & pwm_mode) begin
                mem[ntt_wr_addr *8]       <= {8'h0, ntt_data_in[  MASKED_REG_SIZE-1:0]};
                mem[(ntt_wr_addr*8) + 1] <= {8'h0, ntt_data_in[2*MASKED_REG_SIZE-1:  MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 2] <= {8'h0, ntt_data_in[3*MASKED_REG_SIZE-1:2*MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 3] <= {8'h0, ntt_data_in[4*MASKED_REG_SIZE-1:3*MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 4] <= {8'h0, ntt_data_in[5*MASKED_REG_SIZE-1:4*MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 5] <= {8'h0, ntt_data_in[6*MASKED_REG_SIZE-1:5*MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 6] <= {8'h0, ntt_data_in[7*MASKED_REG_SIZE-1:6*MASKED_REG_SIZE]};
                mem[(ntt_wr_addr*8) + 7] <= {8'h0, ntt_data_in[8*MASKED_REG_SIZE-1:7*MASKED_REG_SIZE]};
            end
            else begin
                mem[ntt_wr_addr*4]       <= {24'h0, ntt_data_in[  REG_SIZE-1:0]};
                mem[(ntt_wr_addr*4) + 1] <= {24'h0, ntt_data_in[2*REG_SIZE-1:  REG_SIZE]};
                mem[(ntt_wr_addr*4) + 2] <= {24'h0, ntt_data_in[3*REG_SIZE-1:2*REG_SIZE]};
                mem[(ntt_wr_addr*4) + 3] <= {24'h0, ntt_data_in[4*REG_SIZE-1:3*REG_SIZE]};
            end
        end

        mem[DEPTH-1] <= {{(AHB_DATA_WIDTH-1){1'b0}},ntt_done};
    end
end

endmodule
