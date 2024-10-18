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

module abr_1r1w_be_ram #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter STROBE_WIDTH = 8
    ,localparam ADDR_WIDTH = $clog2(DEPTH)
    )
    (
    input  logic                           clk_i,

    input  logic                           we_i,
    input  logic [(DATA_WIDTH/STROBE_WIDTH)-1:0]      wstrobe_i,
    input  logic [ADDR_WIDTH-1:0]          waddr_i,
    input  logic [(DATA_WIDTH/STROBE_WIDTH)-1:0][STROBE_WIDTH-1:0] wdata_i,
    input  logic                           re_i,
    input  logic [ADDR_WIDTH-1:0]          raddr_i,
    output logic [DATA_WIDTH-1:0]          rdata_o
    );

    //storage element
    logic [(DATA_WIDTH/STROBE_WIDTH)-1:0][STROBE_WIDTH-1:0] ram [DEPTH-1:0];

    always @(posedge clk_i) begin
        if (we_i) begin
            for (int i = 0; i < (DATA_WIDTH/STROBE_WIDTH); i++) begin
                if (wstrobe_i[i])
                    ram[waddr_i][i] <= wdata_i[i];
            end
        end
    end

    always @(posedge clk_i) begin
        if (re_i) begin
            rdata_o <= ram[raddr_i];
        end
    end

endmodule
