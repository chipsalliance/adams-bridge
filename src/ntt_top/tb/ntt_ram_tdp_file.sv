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
//
// ntt_ram_tdp_file.sv
// --------
// Temp NTT Data Memory to store intermediate results from point multiplication.
//
//
//======================================================================

module ntt_ram_tdp_file 
    import abr_params_pkg::*;
    #(
    parameter ADDR_WIDTH = 10,
    parameter DATA_WIDTH = ABR_MEM_MASKED_DATA_WIDTH
    )
    (      
    input  wire                      clk,
    input  wire                      reset_n,
    input  wire                      zeroize,
    
    input  wire                      ena,
    input  wire                      wea,
    input  wire  [ADDR_WIDTH-1 : 0]  addra,
    input  wire  [DATA_WIDTH-1 : 0]  dina,
    output logic [DATA_WIDTH-1 : 0]  douta,

    input  wire                      enb,
    input  wire                      web,
    input  wire  [ADDR_WIDTH-1 : 0]  addrb,
    input  wire  [DATA_WIDTH-1 : 0]  dinb,
    output logic [DATA_WIDTH-1 : 0]  doutb,

    //TODO: temporary inputs. Remove after high-level memory is ready
    input wire load_tb_values,
    input wire load_random_values,
    input wire mlkem
    // input wire [ADDR_WIDTH-1:0] load_tb_addr
    );
 
    // Declare the RAM variable
    localparam ADDR_LENGTH = 2**ADDR_WIDTH;
    reg [DATA_WIDTH-1:0]    mem[ADDR_LENGTH-1:0], mem_tb[ADDR_LENGTH-1:0];
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] data_tb;

    //for tb purpose - TODO: temp, remove after high-level memory is ready
    initial begin
        $display("In ram, initing mem_tb\n");
        $readmemh("ntt_unmasked_input.hex", mem_tb);
    end
    

    always_ff @ (posedge clk or negedge reset_n) 
    begin : reading_memory
        if (!reset_n) begin
            douta <= '0;
            doutb <= '0;
        end
        else if (zeroize) begin
            douta <= '0;
            doutb <= '0;
        end
        else begin
            if (ena)
                douta <= mem[addra];

            if (enb)
                doutb <= mem[addrb];
        end
    end // reading_memory

    always_ff @ (posedge clk or negedge reset_n) 
    begin : writing_memory
        if (!reset_n) begin
            for (int i0 = 0; i0 < ADDR_LENGTH; i0++)
                mem[i0] <= '0;
        end
        else if (zeroize) begin
            for (int i0 = 0; i0 < ADDR_LENGTH; i0++)
                mem[i0] <= '0;
        end
        else if (load_random_values) begin
            for (int i0 = 0; i0 < MLDSA_N/COEFF_PER_CLK; i0++) begin
                if (mlkem) begin
                    for (int k = 0; k < ABR_MEM_MASKED_DATA_WIDTH/24; k++) begin
                        data_tb[24*k +: 24] = 24'($urandom() % MLKEM_Q);
                    end
                end
                else begin
                    for (int k = 0; k < ABR_MEM_MASKED_DATA_WIDTH/24; k++) begin
                        data_tb[24*k +: 24] = {1'b0,23'($urandom() % MLDSA_Q)};
                    end
                end
                mem[i0] <= data_tb; //mem_tb[i0];
            end
        end
        else if (load_tb_values) begin
            for (int i0 = 0; i0 < MLDSA_N/COEFF_PER_CLK; i0++) begin
                mem[i0] <= mem_tb[i0];
            end
        end
        else begin
            if (ena & wea)
                mem[addra] <= dina;

            if (enb & web)
                mem[addrb] <= dinb;
        end
    end // writing_memory

endmodule
