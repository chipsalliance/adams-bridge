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

module fv_rej_bounded_ctrl_scoreboard 
    import abr_params_pkg::*;
#(
   parameter REJ_NUM_SAMPLERS = 8
  ,parameter REJ_SAMPLE_W     = 4
  ,parameter REJ_VLD_SAMPLES  = 4
  ,parameter REJ_VLD_SAMPLES_W = 24
  ,parameter REJ_VALUE = 15
  ,parameter REJ_BUFFER_W = 3
  ,parameter COUNTER_WIDTH = 4
) (
     ////////////////////////////
    // Input / Output signals //
    ////////////////////////////
    input logic                                                     pi_clock,
    input logic                                                     pi_reset_n,
    input logic                                                     pi_data_valid_i,
    input                                                           po_data_hold_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_SAMPLE_W-1:0]            pi_data_i,
    input                                                           po_data_valid_o,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_VLD_SAMPLES_W-1:0]        po_data_o,

    input logic [REJ_NUM_SAMPLERS-1:0]                              fifo_valid_i,
    input logic [REJ_VLD_SAMPLES-1:0][REJ_BUFFER_W-1:0]             fifo_data_o,
    input logic [REJ_NUM_SAMPLERS-1:0][REJ_BUFFER_W-1:0]            fifo_data_i,
    input                                                           fifo_valid_o

);


lubis_scoreboard #(
.INPUT_TYPE        (logic[11:0]),
.DEPTH             (3),
.EXP_DATA_TYPE     (logic[11:0]),
.ASSUME_INVARIANTS(0)
)fv_rej_bounded_fifo_scoreboard (
.clk            (pi_clock),
.rst            (pi_reset_n),
.soft_rst       ('0),
.full           ('0),
.empty          ('0),
.data_in        (fv_valid_counter_nxt >= 8 && fv_sample_packet ? data_in[23:12] : data_in[11:0]),
.data_out       (fifo_data_o),
.expected_data  (symb_data),
.incr_val       ((fv_valid_counter_nxt >= 8 && fv_sample_packet && sampled_in_loc) || (fv_valid_counter_nxt >= 8 && !sampled_in_loc)  ? 2 : 1),
.push           (fv_scoreboard_push ),
.pop            (fifo_valid_o),
.sampled_in     (sampled_in_loc),
.chosen_symbolic_data(symb_data)
);



logic        fv_scoreboard_push;
logic        fv_soft_reset;
logic [35:0] fv_scoreboard_data_in_reg;
logic [ 3:0] fv_valid_counter_nxt;
logic [ 3:0] fv_valid_counter;
logic [ 3:0] fv_valid_counter_1;
logic [ 3:0] valid_cnt;
logic [35:0] data_in;
logic        fv_sample_packet;
logic        sampled_in_loc;
logic [11:0] symb_data;

lubis_incr_decr_counter_m #(
    .COUNTER_WIDTH      (COUNTER_WIDTH),
    .NUM_INC_SRCS       (1 ),
    .NUM_DEC_SRCS       (1 ),
    .MAX_VALUE          (12    ),
    .MIN_VALUE          (    ),
    .INCR_VAL_WIDTH (4),
    .DECR_VAL_WIDTH (4)/*
    .ASSERT_CLAMP_MAX   (0            ),
    .ASSERT_CLAMP_MIN   (0            ),
    .ASSERT_NO_UNDERFLOW(1            ),
    .ASSERT_NO_OVERFLOW (1            )*/
) lubis_incr_decr_counter_verif
(
    .clk     (pi_clock                            ),
    .rst     (pi_reset_n                          ),
    .soft_rst(1'b0 ),
    .incr_en ((|fifo_valid_i ) && !po_data_hold_o                     ),
    .decr_en (fv_valid_counter >= 4               ),
    .incr_val($countones(fifo_valid_i)            ),
    .decr_val(fv_valid_counter >= 8 ? 8 : 4            ),
    .count   (fv_valid_counter                    ),
    .count_next(fv_valid_counter_nxt              )
);

always_comb begin
  data_in = fv_scoreboard_data_in_reg;
  fv_scoreboard_push = (fv_valid_counter_nxt >= 4) ? 1'b1 : 1'b0;
  
  valid_cnt = 0;
  for(int i = 0; i < 8; i++) begin
    if(fifo_valid_i[i]) begin
      data_in[((fv_valid_counter_1 + valid_cnt)*3 + 2)-:3] = fifo_data_i[i];
      valid_cnt += 1;
    end
  end
end


always_ff@ (posedge pi_clock, posedge pi_reset_n) begin
  if(pi_reset_n) begin
    fv_scoreboard_data_in_reg <= '0;
    fv_valid_counter_1 <= '0;
  end
  else begin
    if (fv_scoreboard_push)
      fv_scoreboard_data_in_reg <= data_in >> (fv_valid_counter_nxt >= 8 ? 24 : 12);
    else
      fv_scoreboard_data_in_reg <= data_in;

    if (fv_valid_counter_nxt >= 8)
      fv_valid_counter_1 <= fv_valid_counter_nxt - 8;
    else if (fv_valid_counter_nxt >= 4 && fv_valid_counter_nxt < 8)
      fv_valid_counter_1 <= fv_valid_counter_nxt - 4;
    else
      fv_valid_counter_1 <= fv_valid_counter_nxt;
  end
end

assume property (
  $stable(fv_sample_packet)
  );

endmodule


