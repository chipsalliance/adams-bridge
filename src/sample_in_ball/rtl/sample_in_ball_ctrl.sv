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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either sibress or implied.
// See the License for the specific language governing permissions and
// limitations under the License.


module sample_in_ball_ctrl
  import sib_pkg::*;
  import abr_params_pkg::*;
  #(
   parameter SIB_NUM_SAMPLERS = 4
  ,parameter SIB_SAMPLE_W     = 8
  ,parameter SIB_TAU          = 60
  ,parameter SIB_NUM_COEFF    = 256
  ,localparam MLDSA_Q_WIDTH   = $clog2(8380417)
  )
  (
  input logic clk,
  input logic rst_b,
  input logic zeroize,

  //input data
  input  logic                                          data_valid_i,
  output logic                                          data_hold_o,
  input  logic [SIB_NUM_SAMPLERS-1:0][SIB_SAMPLE_W-1:0] data_i,
  output logic                                          sib_done_o,

  //memory if 
  output logic [1:0]                         cs_o,
  output logic [1:0]                         we_o,
  output logic [1:0][7:2]                    addr_o,
  output logic [1:0][3:0][MLDSA_Q_WIDTH-1:0] wrdata_o,
  input  logic [1:0][3:0][MLDSA_Q_WIDTH-1:0] rddata_i

  );
  localparam SIB_NUM_DATA_BITS = $bits(data_i);

  sib_fsm_state_e sib_fsm_ns;
  sib_fsm_state_e sib_fsm_ps;

  logic last_sample;

  logic [SIB_TAU-1:0] sign_buffer, sign_buffer_d;
  logic [(SIB_NUM_DATA_BITS*2)-1:0] sign_buffer_nxt;
  logic sign_buffer_en;
  logic sign_buffer_ph;

  logic [SIB_SAMPLE_W-1:0] rej_value;
  logic rej_value_en;

  logic [SIB_NUM_SAMPLERS-1:0] sampler_valid;
  logic sampler_hold;

  logic index_found;
  logic [$clog2(SIB_NUM_SAMPLERS)-1:0] valid_index;
  logic [SIB_SAMPLE_W-1:0] valid_sample;
  logic [SIB_NUM_SAMPLERS-1:0] sampler_mask, sampler_mask_d;
  logic sampler_mask_en;
  logic sampler_mask_clear;
  logic shuffler_valid;

  logic shuffler_hold;

  //FSM Controller
  always_comb begin : sib_fsm_state_combo
    //default loopback assignment
    sib_fsm_ns = sib_fsm_ps;
    unique case (sib_fsm_ps)
        SIB_IDLE: begin
          if (data_valid_i) sib_fsm_ns = SIB_SIGN_BUFFER;
        end
        SIB_SIGN_BUFFER: begin
          if (data_valid_i) sib_fsm_ns = SIB_ACTIVE;
        end
        SIB_ACTIVE: begin
          if (last_sample)  sib_fsm_ns = SIB_DONE;
        end
        SIB_DONE: begin
                            sib_fsm_ns = SIB_IDLE;
        end
        //ERROR
        default: begin
                            sib_fsm_ns = SIB_IDLE;
        end
    endcase
  end

  always_comb begin : sib_fsm_output_combo
    data_hold_o = 0;
    sign_buffer_en = 0;
    sign_buffer_ph = 0;
    rej_value_en = 0;
    sampler_mask_en = 0;
    sampler_mask_clear = 0;
    shuffler_valid = 0;
    sib_done_o = 0;
    unique case (sib_fsm_ps)
        SIB_IDLE: begin
          sign_buffer_en = data_valid_i;
          sign_buffer_ph = 0;
        end
        SIB_SIGN_BUFFER: begin
          sign_buffer_en = data_valid_i;
          sign_buffer_ph = 1;
        end
        SIB_ACTIVE: begin
          data_hold_o = sampler_hold | shuffler_hold;
          shuffler_valid = index_found;
          rej_value_en = index_found & ~shuffler_hold;
          sampler_mask_en = index_found & sampler_hold & ~shuffler_hold;
          sampler_mask_clear = ~index_found | ~data_hold_o;
        end
        SIB_DONE: begin
          sib_done_o = 1;
        end
        //ERROR
        default: begin
          data_hold_o = 1;
        end
    endcase
  end

  always_ff @(posedge clk or negedge rst_b) begin : sib_fsm_state_reg
    if (!rst_b)       sib_fsm_ps <= SIB_IDLE;
    else if (zeroize) sib_fsm_ps <= SIB_IDLE;
    else              sib_fsm_ps <= sib_fsm_ns;
  end

  //Sign buffer
  //Gather TAU bits of sign data over TAU/(SIB_NUM_SAMPLERS*SIB_SAMPLE_W) clocks
  always_comb sign_buffer_nxt = sign_buffer_ph ? {data_i, {SIB_NUM_DATA_BITS{1'b0}}} : {{SIB_NUM_DATA_BITS{1'b0}}, data_i};
  always_comb sign_buffer_d = sign_buffer | sign_buffer_nxt[SIB_TAU-1:0];
                              

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)begin
      sign_buffer <= '0;
    end else if (zeroize) begin
      sign_buffer <= '0;
    end else if (sib_done_o) begin
      sign_buffer <= '0;
    end else if (sign_buffer_en) begin
      sign_buffer <= sign_buffer_d;
    end else if (rej_value_en) begin
      sign_buffer <= SIB_TAU'(sign_buffer >> 1);
    end else begin
      sign_buffer <= sign_buffer;
    end
  end

  //Initialize rejection value to 256 - TAU
  //Increment the rejection value whenever a valid sample is found
  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b) begin
      rej_value <= SIB_NUM_COEFF - SIB_TAU;
    end else if (zeroize) begin
      rej_value <= SIB_NUM_COEFF - SIB_TAU;
    end else if (sib_done_o) begin
      rej_value <= SIB_NUM_COEFF - SIB_TAU;
    end else if (rej_value_en) begin
      rej_value <= rej_value + 1'b1;
    end else begin
      rej_value <= rej_value;
    end
  end

  //Find first valid sample
  always_comb begin
    index_found = 0;
    valid_index = 0;
    sampler_mask_d = sampler_mask;
    for (int i = 0; i < SIB_NUM_SAMPLERS; i++) begin
      if (data_valid_i & ~index_found) begin
        sampler_mask_d[i] = 0;
        if (sampler_valid[i]) begin
          index_found = 1;
          valid_index = i[$clog2(SIB_NUM_SAMPLERS)-1:0];
        end
      end
    end
  end

  always_ff @(posedge clk or negedge rst_b) begin
    if (!rst_b)begin
      sampler_mask <= '1;
    end else if (zeroize | sampler_mask_clear) begin
      sampler_mask <= '1;
    end else if (sampler_mask_en) begin
      sampler_mask <= sampler_mask_d;
    end else begin
      sampler_mask <= sampler_mask;
    end
  end

  //sample in ball is done when we collect TAU samples (rej value is 255)
  always_comb last_sample = (&rej_value) & shuffler_valid & ~shuffler_hold;
  always_comb valid_sample = data_i[valid_index];

  generate
    for (genvar inst_g = 0; inst_g < SIB_NUM_SAMPLERS; inst_g++) begin : sample_in_ball_inst
      sample_in_ball #(
        .SIB_SAMPLE_W(SIB_SAMPLE_W)
      ) sample_in_ball_i (
        .valid_i(sampler_mask[inst_g]),
        .data_i(data_i[inst_g]),
        .rej_value_i(rej_value),
        .valid_o(sampler_valid[inst_g])
      );
    end
  endgenerate

  always_comb sampler_hold = index_found & (valid_index != (SIB_NUM_SAMPLERS-1));

  //Shuffler
  sample_in_ball_shuffler #(
    .SIB_SAMPLE_W(SIB_SAMPLE_W)
  ) sib_shuffler_i (
    .clk(clk),
    .rst_b(rst_b),
    .zeroize(zeroize),
    
    .valid_i(shuffler_valid),
    .hold_o(shuffler_hold),
    .indexi_i(rej_value),
    .indexj_i(valid_sample),
    .sign_i(sign_buffer[0]),

    //memory if 
    .cs_o(cs_o),
    .we_o(we_o),
    .addr_o(addr_o),
    .wrdata_o(wrdata_o),
    .rddata_i(rddata_i)
  );

endmodule
