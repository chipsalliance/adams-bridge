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

module abr_ram_regout #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter NUM_RD_PORTS = 1
    ,parameter NUM_WR_PORTS = 1
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    )
    (
    input  logic                                    clk_i,
    input  logic                                    zeroize_i,
    input  logic [NUM_WR_PORTS-1:0]                 we_i,
    input  logic [NUM_WR_PORTS-1:0][ADDR_WIDTH-1:0] waddr_i,
    input  logic [NUM_WR_PORTS-1:0][DATA_WIDTH-1:0] wdata_i,
    input  logic [NUM_RD_PORTS-1:0]                 re_i,
    input  logic [NUM_RD_PORTS-1:0][ADDR_WIDTH-1:0] raddr_i,
    output logic [NUM_RD_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    output logic [DEPTH-1:0][DATA_WIDTH-1:0]        reg_o
    );

    //storage element
    logic [DEPTH-1:0][DATA_WIDTH-1:0] ram;

    always @(posedge clk_i) begin
        if (zeroize_i) begin
            ram <= '0;
        end
        else begin
            for (int port = 0; port < NUM_WR_PORTS; port++) begin
                if (we_i[port]) begin
                    ram[waddr_i[port]] <= wdata_i[port];
                end
            end
        end
    end

    always @(posedge clk_i) begin
        for (int port = 0; port < NUM_RD_PORTS; port++) begin
            if (re_i[port]) begin
                rdata_o[port] <= ram[raddr_i[port]];
            end
        end
    end

    assign reg_o = ram;

endmodule
