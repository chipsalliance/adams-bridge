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

// Description:
// This module is just a counter which increases whenever
// the input signal is one for a clock event.
//
module fv_abr_sha3pad_incr_counter_m
#(
    parameter COUNTER_WIDTH = 4
)
(
    input  logic                     clk       ,
    input  logic                     rst       ,
    input  logic                     soft_rst  ,
    input  logic                     incr_en   , 
    input  logic [COUNTER_WIDTH-1:0] incr_val  , 

    output logic [COUNTER_WIDTH-1:0] count_next,
    output logic [COUNTER_WIDTH-1:0] count
);

    logic [COUNTER_WIDTH-1:0] count_reg, count_next;

    assign count_next = incr_en ? COUNTER_WIDTH'(count_reg + incr_val) : count_reg;
    assign count = count_reg;

    always_ff @(posedge clk) begin
        if (rst) begin
            count_reg <= '0;
        end
        else if (soft_rst) begin
            count_reg <= '0;
        end
        else begin
            count_reg <= count_next;
        end
    end
    
endmodule

