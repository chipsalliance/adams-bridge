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

module fv_abr_sha3pad_scoreboard_tracking
#(
    parameter  DATA_WIDTH         = 20                       ,
    parameter  type INPUT_TYPE    = bit [DATA_WIDTH-1:0]     ,
    parameter  DEPTH              = 128                      ,
    // Set to 1 if push and pop can happen at the same clock cycle, when the system is empty
    parameter  BYPASS             = 0                        ,
    parameter  ASSUME_INVARIANTS  = 0                        ,
    localparam DEPTH_WIDTH        = (DEPTH == 1 ? 1 : $clog2(DEPTH))
)
(
    input logic                   clk                 ,
    input logic                   rst                 ,
    input logic                   soft_rst            ,
    input logic                   push                ,
    input logic                   pop                 ,
    input logic                   full                ,
    input logic                   empty               ,
    input INPUT_TYPE              data_in             ,
    input logic [DEPTH_WIDTH-1:0] incr_val            ,

    output logic                  sampled_in          ,
    output logic                  sampled_in_reg      ,
    output logic                  sampled_out         ,
    output logic                  sampled_out_reg     ,
    output INPUT_TYPE             chosen_symbolic_data,
    output logic [DEPTH_WIDTH:0]  tracking_counter_out
);

    default clocking default_clk @(posedge clk); endclocking

    INPUT_TYPE symbolic_data;
    sym_symbolic_data: assume property (##1 $stable(symbolic_data));

    logic                   wr_hsk;
    logic                   rd_hsk;
    logic                   tracking_counter_incr;
    logic                   tracking_counter_decr;
    logic                   arbit_window;
    logic [DEPTH_WIDTH:0  ] tracking_counter;
    logic [DEPTH_WIDTH-1:0] tracking_counter_incr_val;

    assign wr_hsk = push && !full;

    if (BYPASS) begin: gen_bypass
        assign rd_hsk      = pop && !(empty && !push);
        assign sampled_out = (tracking_counter == 1 && sampled_in_reg && tracking_counter_decr) ||
                             (push && pop && tracking_counter == 0 && sampled_in && !sampled_in_reg);
    end
    else begin: gen_no_bypass
        assign rd_hsk      = pop && !empty;
        assign sampled_out = (tracking_counter == 1 && sampled_in_reg && tracking_counter_decr && !sampled_out_reg);
    end

    assign sampled_in = ((data_in == symbolic_data) && tracking_counter_incr && arbit_window && !sampled_in_reg);

    assign tracking_counter_incr     = wr_hsk && !sampled_in_reg;
    assign tracking_counter_decr     = rd_hsk && !sampled_out_reg;
    assign tracking_counter_incr_val = (tracking_counter_incr ? incr_val : '0);

    always @(posedge clk) begin
        if (rst) begin
            sampled_in_reg <= 1'b0;
        end
        else if(soft_rst && sampled_in_reg && !(sampled_out || sampled_out_reg)) begin
            sampled_in_reg <= 1'b0;
        end
        else begin
            if (sampled_in) begin
                sampled_in_reg <= 1'b1;
            end
        end
    end

    always @(posedge clk) begin
        if (rst) begin
            sampled_out_reg <= 1'b0;
        end
        else begin
            if (sampled_out) begin
                sampled_out_reg <= 1'b1;
            end
        end
    end

    always @(posedge clk) begin
        if (rst) begin
            tracking_counter <= {DEPTH{1'b0}};
        end
        else if (soft_rst) begin
            tracking_counter <= wr_hsk ? DEPTH_WIDTH'(1'b1) : DEPTH_WIDTH'(1'b0);
        end
        else begin
            tracking_counter <= tracking_counter + tracking_counter_incr_val - tracking_counter_decr;
        end
    end

    assign tracking_counter_out = tracking_counter;
    assign chosen_symbolic_data = symbolic_data;

    // Covers
    cover_sampled_in: cover property (disable iff (rst)
        sampled_in
    );

    cover_sampled_out: cover property (disable iff (rst)
        sampled_out
    );

    // Invariants
    property L0_only_pop_after_push;
        tracking_counter_decr
    |->
        tracking_counter != 0 || tracking_counter_incr
    ;endproperty

    property L1_depth_is_sufficient;
        tracking_counter_incr
    |->
        tracking_counter < DEPTH || tracking_counter_decr
    ;endproperty

    property L2_data_not_in_then_never_at_output;
        !sampled_in_reg
    |->
        !sampled_out_reg
    ;endproperty

    property L3_tracking_counter_not_zero_if_data_in;
        sampled_in_reg && !sampled_out_reg
    |->
        tracking_counter > 0
    ;endproperty

    if(ASSUME_INVARIANTS) begin: gen_assume_invariants
        assume_L0_only_pop_after_push                 : assume property (disable iff (rst) L0_only_pop_after_push              );
        assume_L1_depth_is_sufficient                 : assume property (disable iff (rst) L1_depth_is_sufficient              );
        assume_L2_data_not_in_then_never_at_output    : assume property (disable iff (rst) L2_data_not_in_then_never_at_output );
        assume_L0_tracking_counter_not_zero_if_data_in: assume property (disable iff (rst) L3_tracking_counter_not_zero_if_data_in);
    end else begin: gen_prove_invariants
        assert_L0_only_pop_after_push                 : assert property (disable iff (rst) L0_only_pop_after_push              );
        assert_L1_depth_is_sufficient                 : assert property (disable iff (rst) L1_depth_is_sufficient              );
        assert_L2_data_not_in_then_never_at_output    : assert property (disable iff (rst) L2_data_not_in_then_never_at_output );
        assert_L0_tracking_counter_not_zero_if_data_in: assert property (disable iff (rst) L3_tracking_counter_not_zero_if_data_in);
    end

    data_ordering_and_integrity_liveness: assert property (disable iff (rst)
        sampled_in && tracking_counter == 1
    |->
        s_eventually(sampled_out || soft_rst)
    );

endmodule


