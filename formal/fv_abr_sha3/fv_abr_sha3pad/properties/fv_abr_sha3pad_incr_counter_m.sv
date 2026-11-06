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
// the input signal is one for a clock event. It also supports
// a direct reload (`set_en`/`set_val`), mirroring the `set_i`/
// `set_cnt_i` reload path of the design's `abr_prim_count`, so
// the FV counter can be seeded to a non-zero value in the same
// cycle it would otherwise be soft-reset (e.g. the pipelined
// "new_block" case where a beat of the next block is absorbed
// in the same cycle the current block's run is issued).
//
// Priority (highest to lowest): rst > soft_rst > set_en > incr_en
//
module fv_abr_sha3pad_incr_counter_m
#(
    parameter COUNTER_WIDTH = 4
)
(
    input  logic                     clk       ,
    input  logic                     rst       ,
    input  logic                     soft_rst  ,
    input  logic                     set_en    ,
    input  logic [COUNTER_WIDTH-1:0] set_val   ,
    input  logic                     incr_en   ,
    input  logic [COUNTER_WIDTH-1:0] incr_val  ,

    output logic [COUNTER_WIDTH-1:0] count_next,
    output logic [COUNTER_WIDTH-1:0] count
);

    logic [COUNTER_WIDTH-1:0] fv_count_reg;

    assign count_next = set_en  ? set_val :
                        incr_en ? COUNTER_WIDTH'(fv_count_reg + incr_val) :
                                  fv_count_reg;
    assign count = fv_count_reg;

    always_ff @(posedge clk) begin
        if (rst) begin
            fv_count_reg <= '0;
        end
        else if (soft_rst) begin
            fv_count_reg <= '0;
        end
        else begin
            fv_count_reg <= count_next;
        end
    end

endmodule
