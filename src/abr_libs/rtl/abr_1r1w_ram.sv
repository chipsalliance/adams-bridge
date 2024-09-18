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

module abr_1r1w_ram #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
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
    
    simple_dual_one_clock
    #(
      .DEPTH(DEPTH),
      .DATA_WIDTH(DATA_WIDTH)
    )   
    BRAM
    (
        .clk(clk_i),
        .ena(we_i),
        .enb(re_i),
        .wea(we_i),
        .addra(waddr_i),
        .addrb(raddr_i),
        .dia(wdata_i),
        .dob(rdata_o)
     );

//    //storage element
//    (* ram_style = "block" *) logic [DEPTH-1:0][DATA_WIDTH-1:0] ram;

//    always @(posedge clk_i) begin
//        if (we_i) begin
//            ram[waddr_i] <= wdata_i;
//        end
//    end

//    always @(posedge clk_i) begin
//        if (re_i) begin
//            rdata_o <= ram[raddr_i];
//        end
//    end

endmodule


module simple_dual_one_clock #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    ) (clk,ena,enb,wea,addra,addrb,dia,dob);

    input clk,ena,enb,wea;
    input [ADDR_WIDTH-1:0] addra,addrb;
    input [DATA_WIDTH-1:0] dia;
    output [DATA_WIDTH-1:0] dob;
    (* ram_style = "block" *) reg [DATA_WIDTH-1:0] ram [DEPTH-1:0];
    reg [DATA_WIDTH-1:0] doa,dob;
    
    always @(posedge clk) begin
        if (ena) begin
            if (wea)
                ram[addra] <= dia;
        end
    end
    
    always @(posedge clk) begin
        if (enb)
            dob <= ram[addrb];
    end

endmodule
