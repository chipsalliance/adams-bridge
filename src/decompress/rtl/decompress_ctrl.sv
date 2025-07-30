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
//
// decompress_ctrl.sv
// ---------
// Controls memory accesses and iterates over MLKEM_K = 4 polynomials before generating done

module decompress_ctrl
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire decompress_enable,
        input wire [2:0] num_poly,
        input wire mem_wr_valid,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        output logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr,
        output logic done
    );

    //Internals
    logic last_poly_last_addr_wr;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_wr_addr <= '0;
        end
        else if (zeroize) begin
            mem_wr_addr <= '0;
        end
        else if (last_poly_last_addr_wr) begin
            mem_wr_addr <= '0;
        end
        else if (decompress_enable) begin
            mem_wr_addr <= dest_base_addr;
        end
        else if (mem_wr_valid) begin
            mem_wr_addr <= mem_wr_addr + 'h1;
        end
    end

    always_comb last_poly_last_addr_wr = (mem_wr_addr == (dest_base_addr + ((num_poly * (MLKEM_N/4))-1)));

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            done <= '0;
        else if (zeroize)
            done <= '0;
        else
            done <= last_poly_last_addr_wr;
    end

endmodule
