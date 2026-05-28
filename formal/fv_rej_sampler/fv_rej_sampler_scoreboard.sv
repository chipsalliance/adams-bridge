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

module fv_rej_sampler_scoreboard
#( 	
    parameter  INPUT_DATA_WIDTH         = 20,
    parameter  OUTPUT_DATA_WIDTH        = 20,
    parameter  INPUT_PACKET_WIDTH       = 10,
    parameter  OUTPUT_PACKET_WIDTH      = 10,
    parameter  type INPUT_TYPE          = bit [INPUT_DATA_WIDTH-1:0],
    parameter  type OUTPUT_TYPE         = bit [OUTPUT_DATA_WIDTH-1:0],
    parameter  type INPUT_PACKET_TYPE   = bit [INPUT_PACKET_WIDTH-1:0],
    parameter  type OUTPUT_PACKET_TYPE  = bit [OUTPUT_PACKET_WIDTH-1:0],
    parameter  type EXP_DATA_TYPE       = bit [OUTPUT_DATA_WIDTH-1:0],
    parameter  DEPTH                    = 128,
    parameter  BYPASS                   = 0,
    parameter  ASSUME_INVARIANTS        = 0,

    localparam DEPTH_WIDTH              = (DEPTH == 1 ? 1 : $clog2(DEPTH+1)),
    localparam INPUT_PACKET_NUM         = INPUT_DATA_WIDTH / INPUT_PACKET_WIDTH,
    localparam OUTPUT_PACKET_NUM        = OUTPUT_DATA_WIDTH / OUTPUT_PACKET_WIDTH,
    localparam INPUT_PACKET_NUM_W       = $clog2(INPUT_PACKET_NUM+1),
    localparam OUTPUT_PACKET_NUM_W      = $clog2(OUTPUT_PACKET_NUM+1)
)
(
    input logic                        clk,
    input logic                        rst,
    input logic                        soft_rst,
    input logic                        push,
    input logic                        pop,
    input logic                        full,
    input logic                        empty,

    input INPUT_TYPE                   data_in,
    input logic [INPUT_PACKET_NUM_W-1:0] num_packets_in,
    input OUTPUT_TYPE                  data_out,
    input logic [OUTPUT_PACKET_NUM_W-1:0] num_packets_out,
    input EXP_DATA_TYPE expected_data,

    output logic                       sampled_in,
    output logic                       sampled_in_reg,
    output logic                       sampled_out,
    output logic                       sampled_out_reg,
    output INPUT_TYPE                  chosen_symbolic_data,
    output logic [DEPTH_WIDTH:0]       tracking_counter_out
);

default clocking default_clk @(posedge clk); endclocking



// -------------------------
// Symbolic Tracking
// -------------------------

logic [INPUT_PACKET_NUM_W-1:0] symbolic_packet_index;
assume property (##1 $stable(symbolic_packet_index));
assume property (sampled_in |-> symbolic_packet_index < num_packets_in);
logic [OUTPUT_PACKET_NUM_W-1:0] output_index_symbolic;
logic [INPUT_PACKET_WIDTH-1:0] symbolic_data; // symbolic data to track
assume property (##1 $stable(symbolic_data)); // symbolic value must not change

number_of_packets_less_than: assert property (num_packets_in <= INPUT_PACKET_NUM);
number_of_out_packet_less_than: assert property (num_packets_out <= OUTPUT_PACKET_NUM);
logic arbit_window; // non-deterministic start of the window 

// find the index of the symbolic data in the fifo
logic [DEPTH_WIDTH:0] index_in_fifo;

always_ff @(posedge clk or posedge rst) begin
    if (rst || soft_rst) begin
        index_in_fifo <= '0;
    end else begin
        if (sampled_in == 1'b1) begin
            if (!sampled_out_reg && pop)
            index_in_fifo <= (symbolic_packet_index + tracking_counter_out - num_packets_out);
            else
            index_in_fifo <= (symbolic_packet_index + tracking_counter_out);
        end
        else if (!sampled_out_reg && pop) begin
            index_in_fifo <= index_in_fifo - num_packets_out;
        end
    end
end
// find the output index of the symbolic data in the output
always_ff @(posedge clk or posedge rst) begin
    if (rst  ||  soft_rst) begin
        output_index_symbolic <= 1'b0;
    end else begin
        if (sampled_in == 1'b1) begin
            output_index_symbolic <= (symbolic_packet_index + tracking_counter_out) % OUTPUT_PACKET_NUM;
        end
    end
end
//logic output_contains_symbolic;
logic input_contains_symbolic;
// this comb block, just checks if the symbolic data is present in the input
// and also counts the number of packets before the symbolic data
always_comb begin 
    input_contains_symbolic = 1'b0;
            if (data_in[symbolic_packet_index*INPUT_PACKET_WIDTH +: INPUT_PACKET_WIDTH] == symbolic_data) begin
                input_contains_symbolic = 1'b1;
        end 
end


assign sampled_in = push && !full && input_contains_symbolic &&
                    !sampled_in_reg && arbit_window;

assign sampled_out = pop && sampled_in_reg &&
                     !sampled_out_reg && index_in_fifo < num_packets_out;

// -------------------------
// State Registers
// -------------------------

always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
        sampled_in_reg  <= 1'b0;
        sampled_out_reg <= 1'b0;
    end else if (soft_rst) begin
        sampled_in_reg  <= 1'b0;
        sampled_out_reg <= 1'b0;
    end else begin
        if (sampled_in)
            sampled_in_reg <= 1'b1;

        if (sampled_out)
            sampled_out_reg <= 1'b1;
    end
end

// -------------------------
// Tracking Counter Logic
// -------------------------
logic tracking_counter_incr,tracking_counter_decr;
assign tracking_counter_incr = push && !sampled_in_reg && !full;
assign tracking_counter_decr = pop && !sampled_out_reg;
lubis_incr_decr_counter_m #(
.COUNTER_WIDTH      (DEPTH_WIDTH+1),                    // the counter width should be enough to hold the depth
.NUM_INC_SRCS       (1 ), 
.NUM_DEC_SRCS       (1 ), 
.MAX_VALUE          (DEPTH), 
.MIN_VALUE          (    ), 
.INCR_VAL_WIDTH (DEPTH_WIDTH+1), 
.DECR_VAL_WIDTH (DEPTH_WIDTH+1)
) lubis_incr_decr_counter_scoerboard
(
    .clk     (clk),
    .rst     (rst),                   // the counter uses active high reset
    .soft_rst(soft_rst),
    .incr_en (tracking_counter_incr), // when there is atleast one valid and not hold
    .decr_en (tracking_counter_decr), // when the number of elements is greater than fifo_pop_max
    .incr_val(num_packets_in),        // the increment should be the number of valid samples
    .decr_val(num_packets_out),       // the decrement should be the number of element you are popping one time    
    .count   (tracking_counter_out),  //current counter value
    .count_next(              )       // next counter value
);

   

assign chosen_symbolic_data = symbolic_data;

// -------------------------
// Properties
// -------------------------
property L0_only_pop_after_push;
    tracking_counter_decr
|->
    tracking_counter_out != 0 || tracking_counter_incr
;endproperty
property L1_depth_is_sufficient;
    tracking_counter_incr
|->
    tracking_counter_out < DEPTH || tracking_counter_decr
;endproperty
property L2_data_not_in_then_never_at_output;
    !sampled_in_reg
|->
    !sampled_out_reg
;endproperty
property L3_tracking_counter_not_zero_if_data_in;
    sampled_in_reg && !sampled_out_reg
|->
    tracking_counter_out > 0
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
logic must_read;
assign must_read = (index_in_fifo < num_packets_out) && sampled_in_reg && pop;
property check_must_read;
    disable iff (rst || soft_rst)
    must_read
;endproperty

check_if_must_read_reachable : cover property(check_must_read);
property check_sampled_out;
    disable iff (rst || soft_rst)
    sampled_out_reg
;endproperty 
checking_sampled_out : cover property (check_sampled_out);
property check_pop;
    disable iff (rst || soft_rst)
    pop
;endproperty 
checking_pop : cover property (pop);
property data_integrity;
    disable iff (rst || soft_rst)
    must_read
|->
    data_out[output_index_symbolic*OUTPUT_PACKET_WIDTH +: OUTPUT_PACKET_WIDTH] == symbolic_data
;endproperty
checking_data_integrity : assert property (data_integrity);

property liveness;
    disable iff (rst || soft_rst)
    sampled_in_reg 
|->
    s_eventually sampled_out_reg
;endproperty
checking_liveness : assert property (liveness);

property ordering;
    disable iff (rst || soft_rst)
    sampled_in_reg && !sampled_out_reg 
|-> 
    !full || pop
;endproperty
check_ordering: assert property (ordering);


endmodule
