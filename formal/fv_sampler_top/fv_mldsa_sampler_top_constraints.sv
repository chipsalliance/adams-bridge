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


module fv_mldsa_sampler_top_constraints
    import mldsa_sampler_pkg::*;
    import abr_sha3_pkg::*;
    import mldsa_params_pkg::*;
    import abr_prim_alert_pkg::*;
    import abr_prim_mubi_pkg::*;
#(
   parameter REJ_VLD_SAMPLES  = 4
  ,parameter REJ_BUFFER_W = 3
) (
    input    logic                  pi_clk,
    input    logic                  pi_reset_n,
    input    logic                  pi_zeroize,
    input    mldsa_sampler_mode_e   pi_sampler_mode_i,
    input    logic                  pi_sha3_start_i,
    input    logic                  pi_msg_start_i,
    input    logic                  pi_msg_valid_i,
    input    logic                  po_msg_rdy_o,
    input    logic [MsgStrbW-1:0]   pi_msg_strobe_i,
    input    logic [MsgWidth-1:0]   pi_msg_data_i[Sha3Share],
    input    logic                  pi_sampler_start_i,
    input    logic [MLDSA_MEM_ADDR_WIDTH-1:0]       pi_dest_base_addr_i,
    input    mem_if_t                          pi_sib_mem_rd_req_i,
    input    logic [MLDSA_MEM_DATA_WIDTH-1:0]       po_sib_mem_rd_data_o,
    input    logic                                  po_sampler_busy_o,
    input    logic                                  po_sampler_ntt_dv_o,
    input    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0]   po_sampler_ntt_data_o,
    input    logic                                          po_sampler_mem_dv_o,
    input    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0]   po_sampler_mem_data_o,
    input    logic [MLDSA_MEM_ADDR_WIDTH-1:0]       po_sampler_mem_addr_o,
    input    logic                                  po_sampler_state_dv_o,
    input    logic [abr_sha3_pkg::StateW-1:0]       po_sampler_state_data_o[Sha3Share]
);

default clocking default_clk @(posedge pi_clk); endclocking


//--- sampler_mode_i ---//

// sampler_mode_i stays stable after sha3_start_i has been asserted, until there is a sampler_start_i
assume_stable_sampler_mode_sha3_start : assume property(
    pi_sha3_start_i
|->
    $stable(pi_sampler_mode_i) until pi_sampler_start_i
);

// sampler_mode_i stays within the defined value range
assume_sampler_mode_in_range : assume property(
    pi_sampler_mode_i inside {MLDSA_SAMPLER_NONE,MLDSA_SHAKE256,MLDSA_SHAKE128,MLDSA_REJ_SAMPLER,MLDSA_EXP_MASK,MLDSA_REJ_BOUNDED,MLDSA_SAMPLE_IN_BALL}
);

// sampler_mode_i stays stable after sampler_start_i until the sampler is not busy anymore
assume_stable_sampler_mode_sampler_start : assume property(
    pi_sampler_start_i
|->
    ##1 $stable(pi_sampler_mode_i) until !po_sampler_busy_o
);


//--- sha3_start_i ---//

// sha3_start_i is a pulse
assume_pulse_sha3_start: assume property(
    pi_sha3_start_i
|->
    ##1 !pi_sha3_start_i
);

// sha3_start_i can only occur during on of the SHAKE modes and if the sampler is not busy
assume_sha3_start_only_during_SHAKE: assume property(
   pi_sha3_start_i
|->
 $past(!po_sampler_busy_o && 
    ((pi_sampler_mode_i == MLDSA_SHAKE128) || (pi_sampler_mode_i == MLDSA_SHAKE256)))
    
);
// sha3_start |-> $past(!(busy)).

// sha3_start_i should not toggle until sampler_busy_o will be asserted
assume_no_several_sha3_start: assume property(
    pi_sha3_start_i
|->
    ##1 (!pi_sha3_start_i) until_with (po_sampler_busy_o)
);


//--- msg_start_i ---//

// msg_start_i shouldn't be asserted, whenever either sha3_start_i, sampler_start_i or msg_valid_i is asserted
assume_no_msg_start: assume property(
    pi_sha3_start_i || pi_sampler_start_i || pi_msg_valid_i
|->
    !pi_msg_start_i
);

// msg_start_i should appear one CC after sha3_start_i
assume_msg_start_after_sha3_start: assume property(
    pi_sha3_start_i
|->
    ##1 pi_msg_start_i
);

// msg_start_i is a pulse
assume_pulse_msg_start: assume property(
    pi_msg_start_i
|->
    ##1 !pi_msg_start_i
);

// there are no several msg_start_i, until sha3_absorbed is set to True
assume_no_several_msg_starts: assume property(
    pi_msg_start_i
|->
    ##1 (!pi_msg_start_i) until_with (mldsa_sampler_top.sha3_absorbed == abr_prim_mubi_pkg::MuBi4True)
);


//--- msg_valid_i ---//

// msg_valid_i stays stable until there is a sampler_start_i
assume_msg_valid_until_sampler_start_i: assume property(
    pi_msg_valid_i
|->
    pi_msg_valid_i until pi_sampler_start_i
);

// when sha3_process is asserted, msg_valid_i is deasserted until msg_start_i
assume_msg_valid_after_process: assume property(
    mldsa_sampler_top.sha3_process
|->
    !pi_msg_valid_i until_with pi_msg_start_i
);

// msg_valid_i shouldn't be asserted, whenever either sha3_start_i, sampler_start_i or msg_start_i is asserted
assume_no_msg_valid: assume property(
    pi_sha3_start_i || pi_sampler_start_i || pi_msg_start_i
|->
    !pi_msg_valid_i
);


//--- msg_strobe_i ---//

// msg_strobe_i has to be in its defined range
assume_no_bubbles_msg_strobe: assume property(
    pi_msg_strobe_i inside {8'b00000000, 8'b00000001, 8'b00000011, 8'b00000111, 8'b00001111,
                            8'b00011111, 8'b00111111, 8'b01111111, 8'b11111111}
);


//--- msg_data_i ---//

// msg_data_i stays stable after a msg_valid_i and no msg_rdy_o
assume_stable_msg_data: assume property(
    pi_msg_valid_i &&
    !po_msg_rdy_o
|->
    ##1 $stable(pi_msg_data_i)
);


//--- sampler_start_i ---//

// sampler_start_i is asserted, after there is a msg_valid_i and the msg_strobe_i is not all 1's
assume_partial_sampler_start: assume property(
   pi_sampler_start_i
    |->
    $past( pi_msg_valid_i &&
    pi_msg_strobe_i != '1)
);
// sampler_start |-> $past(msg_valid_i) && $past(msg_strobe_i) != '1.

// sampler_start_i shouldn't be asserted, whenever either sha3_start_i, msg_start_i or msg_valid_i is asserted
assume_no_sampler_start: assume property(
    pi_sha3_start_i || pi_msg_valid_i || pi_msg_start_i
|->
   !pi_sampler_start_i
);

// sampler_start_i is a pulse
assume_pulse_sampler_start: assume property(
    pi_sampler_start_i
|->
   ##1 !pi_sampler_start_i
);

// sampler_start_i stays deasserted for the time, there is the start_i_flag asserted
assume_stable_sampler_start: assume property(
    start_i_flag
|->
   !pi_sampler_start_i
);


//--- sib_mem_rd_req_i ---//

// sib_mem_rd_req_i.rd_wr_en stays in its defined range
assume_no_bubbles_sib_mem_rd_req: assume property(
    pi_sib_mem_rd_req_i.rd_wr_en inside {2'b00, 2'b01, 2'b10}
);

// when sib_mem_rd_req_i is asserted the sampler_mode_i has to be MLDSA_SAMPLER_IN_BALL
assume_sib_mem_rd_req_only_during_sib_mode: assume property(
    pi_sib_mem_rd_req_i 
|-> 
    pi_sampler_mode_i == MLDSA_SAMPLE_IN_BALL
);


//--- dest_base_addr_i ---//

// dest_base_addr_i stays stable
assume_stable_dest_base_addr_i: assume property(
    $stable(pi_dest_base_addr_i)
);


//--- auxilliary logic ---//

// logic that sets flags for the individual start signals in order to make sure the start sequence is correct
logic sha3_start_flag;
logic msg_start_flag;
logic msg_valid_flag;
logic start_i_flag;

always_ff @(posedge pi_clk, negedge pi_reset_n) begin : sampler_start_i_logic
    if (!pi_reset_n || pi_zeroize) begin
        sha3_start_flag <= 1'b0;
        msg_start_flag  <= 1'b0;
        msg_valid_flag  <= 1'b0;
        start_i_flag    <= 1'b0;
    end else  if (pi_sha3_start_i) begin
        sha3_start_flag <= 1'b1;
    end else if (pi_msg_start_i && sha3_start_flag) begin
        msg_start_flag <= 1'b1;
    end else if (pi_msg_valid_i && msg_start_flag && sha3_start_flag) begin
        msg_valid_flag <= 1'b1;
    end else if (sha3_start_flag && msg_start_flag && msg_valid_flag && pi_sampler_start_i) begin
        start_i_flag <= 1'b1;
    end else if (sha3_start_flag && msg_start_flag && msg_valid_flag && start_i_flag && !po_sampler_busy_o) begin
        sha3_start_flag <= 1'b0;
        msg_start_flag  <= 1'b0;
        msg_valid_flag  <= 1'b0;
        start_i_flag    <= 1'b0;
    end
end

// msg_valid_i can only occur, if msg_start_flag and sha3_start_flag are asserted
assume_start_msg_valid: assume property(
    pi_msg_valid_i |-> msg_start_flag && sha3_start_flag
);

// sampler_start_i can only be asserted, if msg_start_flag, sha3_start_flag and msg_valid_flag are asserted
assume_start_sampler_start: assume property(
    pi_sampler_start_i |-> sha3_start_flag && msg_start_flag && msg_valid_flag
);

// sampler_start_i has to happen eventually
assume_eventually_sampler_start: assume property(
    s_eventually(pi_sampler_start_i)
);

endmodule