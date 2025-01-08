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

module sib_mem #(
     parameter DEPTH      = 64
    ,parameter NUM_PORTS  = 1
    ,parameter DATA_WIDTH = 32
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    )
    (
    input  logic                                 clk_i,
    input  logic                                 rst_b,
    input  logic                                 zeroize,

    input  logic [NUM_PORTS-1:0]                 cs_i,
    input  logic [NUM_PORTS-1:0]                 we_i,
    input  logic [NUM_PORTS-1:0][ADDR_WIDTH-1:0] addr_i,
    input  logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] wdata_i,
    output logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] rdata_o
    );

    //storage element
    logic [DEPTH-1:0][DATA_WIDTH-1:0] mem;

    always @(posedge clk_i or negedge rst_b) begin
        if (!rst_b) begin
            mem <= '0;
        end
        else if (zeroize) begin
            mem <= '0;
        end else begin
            for (int port = 0; port < NUM_PORTS; port++) begin
                if (cs_i[port] & we_i[port]) begin
                        mem[addr_i[port]] <= wdata_i[port];
                end
            end
        end
    end

    always @(posedge clk_i or negedge rst_b) begin
        if (!rst_b) begin
            rdata_o <= '0;
        end
        else if (zeroize) begin
            rdata_o <= '0;
        end else begin
            for (int port = 0; port < NUM_PORTS; port++) begin
                if (cs_i[port] & ~we_i[port]) begin
                    rdata_o[port] <= mem[addr_i[port]];
                end
            end 
        end
    end

endmodule
