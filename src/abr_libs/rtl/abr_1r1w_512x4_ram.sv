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

module abr_1r1w_512x4_ram #(
     parameter DEPTH      = 512
    ,parameter DATA_WIDTH = 4
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    )
    (
    input  logic                       clk_i,

    input  logic                       we_i,
    input  logic [ADDR_WIDTH-1:0]      waddr_i,
    input  logic [DATA_WIDTH-1:0]      wdata_i,
    input  logic                       re_i,
    input  logic [ADDR_WIDTH-1:0]      raddr_i,
    output logic [DATA_WIDTH-1:0]      rdata_o
    );

    //storage element
`ifndef RV_FPGA_OPTIMIZE
    logic [DEPTH-1:0][DATA_WIDTH-1:0] ram;
`else
    (* ram_style = "block" *) logic [DATA_WIDTH-1:0] ram [DEPTH-1:0];
`endif

    always @(posedge clk_i) begin
        if (we_i) begin
            ram[waddr_i] <= wdata_i;
        end
    end

    always @(posedge clk_i) begin
        if (re_i) begin
            rdata_o <= ram[raddr_i];
        end
    end

endmodule
