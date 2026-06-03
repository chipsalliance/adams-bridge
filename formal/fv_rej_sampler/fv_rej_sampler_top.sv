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
//#$includes

//$#//

module fv_rej_sampler_top
    //#$imports
    import abr_params_pkg::*;
    //$#//
#(
    parameter REJ_NUM_SAMPLERS     = 5,                             // 10
    parameter REJ_SAMPLE_W         = 24,                            // 12
    parameter REJ_VLD_SAMPLES      = 4,                             // 4
    parameter REJ_VLD_SAMPLES_W    = 24,                            // 12
    parameter REJ_VALUE            = 8380417,                       // 3329
    parameter OPT_REJ_BUFFER_DEPTH = 0,
    parameter REJ_BUFFER_W         = $clog2(REJ_VALUE)
    //#$localparams
    //$#//
) (
    //#$ports
    input logic                                              pi_clk,
    input logic                                              pi_rst_b,
    input logic                                              pi_zeroize,
    input logic                                              pi_data_valid_i,
    input logic                                              po_data_hold_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0]     pi_data_i,
    input logic                                              po_data_valid_o,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0] po_data_o
    //$#//
);
/// LOCAL PARAMS ///
localparam REJ_NUM_SAMPLERS_INDEX = $clog2(REJ_NUM_SAMPLERS);
localparam FIFO_MAX = REJ_NUM_SAMPLERS+REJ_VLD_SAMPLES ;               // how many elements can the fifo hold
localparam FIFO_POP_MAX = REJ_VLD_SAMPLES;                             // how many elements can be popped from the fifo at once
//// VARIABLES /////


logic [REJ_NUM_SAMPLERS_INDEX-1:0] fv_rej_sample_index;
logic [REJ_SAMPLE_W-1:0] fv_rej_sample_data;
logic fv_rej_sample_data_valid;
logic [REJ_BUFFER_W-1:0] fv_rej_valid_sample_data;

logic fv_hold_o;
logic fv_data_valid_o;

// SCORE BOARD VARIABLES ////
logic [$clog2(FIFO_MAX)-1:0] fv_valid_counter,fv_valid_counter_nxt;     // this is the current count of elements inthe fifo
logic [REJ_NUM_SAMPLERS-1:0] fv_sample_valid;                           // to check how many of them are valid
logic [REJ_NUM_SAMPLERS-1:0][REJ_BUFFER_W-1:0] fv_sample_data;          // store the data if they are valid
logic [REJ_NUM_SAMPLERS-1:0][REJ_VLD_SAMPLES_W-1:0] fv_fifo_data;
//// FUNCTIONS /////


function automatic logic [REJ_BUFFER_W:0] get_rej_valid_sample_w( logic [REJ_SAMPLE_W-1:0] data_i);
    if (data_i[REJ_BUFFER_W-1:0] < REJ_VALUE) begin 
        return {1'b1, data_i[REJ_BUFFER_W-1:0]};
    end else begin
        return {1'b0, data_i[REJ_BUFFER_W-1:0]}; 
    end
endfunction

//// INSTANCES ////

property eventually_valid_in_if_buffer_not_empty;
    disable iff (reset)
    (fv_valid_counter > 0)
|->
    s_eventually(|fv_sample_valid)
;endproperty
assume_eventually_valid_in_if_buffer_not_empty: assume property (eventually_valid_in_if_buffer_not_empty);
//#$instances
fv_rej_sampler_constraints #(
    .REJ_NUM_SAMPLERS(REJ_NUM_SAMPLERS),
    .REJ_SAMPLE_W(REJ_SAMPLE_W),
    .REJ_VLD_SAMPLES(REJ_VLD_SAMPLES),
    .REJ_VLD_SAMPLES_W(REJ_VLD_SAMPLES_W),
    .REJ_VALUE(REJ_VALUE),
    .OPT_REJ_BUFFER_DEPTH(OPT_REJ_BUFFER_DEPTH),
    .REJ_BUFFER_W(REJ_BUFFER_W)
) fv_rej_sampler_constraints_i (.*);

//$#/
lubis_incr_decr_counter_m #(
.COUNTER_WIDTH      ($clog2(FIFO_MAX)),
.NUM_INC_SRCS       (1 ),
.NUM_DEC_SRCS       (1 ),
.MAX_VALUE          (FIFO_MAX),
.MIN_VALUE          (  0  ),
.INCR_VAL_WIDTH ($clog2(FIFO_MAX)),
.DECR_VAL_WIDTH ($clog2(FIFO_MAX))/*
.ASSERT_CLAMP_MAX   (0            ),
.ASSERT_CLAMP_MIN   (0            ),
.ASSERT_NO_UNDERFLOW(1            ),
.ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_verif
(
    .clk     (pi_clk),
    .rst     (!pi_rst_b), // the counter uses active high reset
    .soft_rst(pi_zeroize),
    .incr_en (pi_data_valid_i && !po_data_hold_o && |fv_sample_valid ),         // when the valid_i is up 
    .decr_en (fv_valid_counter >= FIFO_POP_MAX               ),                 // when the number of elements is greater than fifo_pop_max
    .incr_val($countones(fv_sample_valid)            ),                         // the increment should be the number of valid samples
    .decr_val(FIFO_POP_MAX     ),                                               // the decrement should be the number of element you are popping one time    
    .count   (fv_valid_counter                    ),                            //current counter value
    .count_next(fv_valid_counter_nxt              )                             // next counter value
);
property tracking_counter_invariant(counter_val,max_val,min_val);
    disable iff (reset)
    (counter_val<= max_val) && (counter_val >= min_val)
;endproperty
check_counter_invariant: assert property (tracking_counter_invariant(fv_valid_counter,FIFO_MAX,0));

// scoreboard instance 
fv_rej_sampler_scoreboard #(
    .INPUT_DATA_WIDTH       (REJ_NUM_SAMPLERS*REJ_VLD_SAMPLES_W),
    .OUTPUT_DATA_WIDTH     (REJ_VLD_SAMPLES*REJ_VLD_SAMPLES_W),
    .INPUT_PACKET_WIDTH   (REJ_VLD_SAMPLES_W),
    .OUTPUT_PACKET_WIDTH  (REJ_VLD_SAMPLES_W),
    
    .DEPTH             (FIFO_MAX),
    .BYPASS            (0),
    .ASSUME_INVARIANTS (0)
) lubis_scoreboard_i (
    .clk                 (pi_clk                 ),
    .rst                 (!pi_rst_b               ),
    .soft_rst            (pi_zeroize             ),
    .push                (pi_data_valid_i   && !po_data_hold_o    && |fv_sample_valid  ),   // when the input is valid, and not hold
    .pop                 (fv_valid_counter >= FIFO_POP_MAX        ),                        // when the number of elements in the fifo is greater than fifo_pop_max
    .full                (po_data_hold_o),                                                  // hold_o is the full signal
    .empty               (),
    .data_in             (fv_fifo_data),
    .num_packets_in      ($countones(fv_sample_valid)),
    .data_out            (po_data_o),
    .num_packets_out     (FIFO_POP_MAX),
    .expected_data       (),

    .sampled_in          (),
    .sampled_in_reg      (),
    .sampled_out         (),
    .sampled_out_reg     (),
    .chosen_symbolic_data(),
    .tracking_counter_out()
);

//// DEFAULT CLOCK/////
default clocking default_clk @(posedge pi_clk); endclocking
/// DEFAULT RESET ////
logic reset;
assign reset =  !pi_rst_b || pi_zeroize;

//// AUX LOGIC ////

always_comb begin
    {fv_rej_sample_data_valid, fv_rej_valid_sample_data} = 
    get_rej_valid_sample_w(pi_data_i[fv_rej_sample_index]);
end

always_comb begin
    fv_sample_valid = '0;
    fv_sample_data = '0;
    for (int j = 0; j < REJ_NUM_SAMPLERS ; j++) begin 
        if (pi_data_valid_i) begin
            {fv_sample_valid[j],fv_sample_data[j]} = get_rej_valid_sample_w(pi_data_i[j]);
        end
        else begin
            fv_sample_valid[j] = 1'b0;
            fv_sample_data[j] = {REJ_BUFFER_W{1'b0}};
        end
    end
end

always_comb begin
    for (int j = 0,int a = 0; j < REJ_NUM_SAMPLERS ; j++) begin 
        if (fv_sample_valid[j]) begin
            fv_fifo_data[a] = { {(REJ_VLD_SAMPLES_W-REJ_BUFFER_W){1'b0}},fv_sample_data[j] };
            a++;
        end
    end
end
//// ASSUMPTIONS /////
// make symbolic variables
property make_symbolic (variable);
    disable iff (reset)
    ##1 $stable(variable)
;endproperty
// limit the value of the index to the number of samplers
property limit_index (index,limit);
    disable iff (reset)
    index < limit
;endproperty

make_index_symbolic: assume property (make_symbolic(fv_rej_sample_index));
make_data_symbolic: assume property (make_symbolic(fv_rej_sample_data));
limit_fv_rej_sample_index: assume property(limit_index(fv_rej_sample_index,REJ_NUM_SAMPLERS));

///// ASSERTIONS /////
// check the data validity is correctly generated by the rejection block
property check_rej_valid_and_data;
    disable iff (reset)
    pi_data_valid_i &&  pi_data_i[fv_rej_sample_index] == fv_rej_sample_data 
|-> 
    rej_sampler_ctrl.sample_valid[fv_rej_sample_index]== fv_rej_sample_data_valid && 
    fv_rej_valid_sample_data == rej_sampler_ctrl.buffer_data[fv_rej_sample_index]
;endproperty
check_validity_output: assert property (check_rej_valid_and_data);

// check the hold_o is correctly generated 
property check_hold_o;
   disable iff (reset)
   po_data_hold_o == (fv_valid_counter > (FIFO_MAX - (REJ_NUM_SAMPLERS - REJ_VLD_SAMPLES)) )
;endproperty
check_hold_o_output: assert property (check_hold_o);
/// RESET property ///
property reset_property;
    $past(~pi_rst_b || pi_zeroize )  
|-> 
    !po_data_hold_o  && !po_data_valid_o 
;endproperty
reset_assert: assert property (reset_property);
// check the data out is valid when data poppd
property data_out_valid;
    disable iff (reset)
    po_data_valid_o == (fv_valid_counter >= FIFO_POP_MAX) 
;endproperty
check_data_out_valid_a : assert property (data_out_valid);
endmodule




bind rej_sampler_ctrl fv_rej_sampler_top #(
    //#$bind
    .REJ_NUM_SAMPLERS (REJ_NUM_SAMPLERS),
    .REJ_SAMPLE_W (REJ_SAMPLE_W),
    .REJ_VLD_SAMPLES (REJ_VLD_SAMPLES),
    .REJ_VLD_SAMPLES_W (REJ_VLD_SAMPLES_W),
    .REJ_VALUE (REJ_VALUE),
    .OPT_REJ_BUFFER_DEPTH (OPT_REJ_BUFFER_DEPTH),
    .REJ_BUFFER_W (REJ_BUFFER_W)
) fv_rej_sampler_top_i (
    .pi_clk (clk),
    .pi_rst_b (rst_b),
    .pi_zeroize (zeroize),
    .pi_data_valid_i (data_valid_i),
    .po_data_hold_o (data_hold_o),
    .pi_data_i (data_i),
    .po_data_valid_o (data_valid_o),
    .po_data_o (data_o)
    //$#//
);
