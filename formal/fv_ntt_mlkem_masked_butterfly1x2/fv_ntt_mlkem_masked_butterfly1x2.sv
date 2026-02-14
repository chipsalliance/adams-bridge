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


module fv_ntt_mlkem_masked_butterfly1x2
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
#(
    parameter MLKEM_SHARE_WIDTH = 24,
    parameter MLKEM_Q_WIDTH     = MLKEM_SHARE_WIDTH/2
    //#$localparams
    //$#//
) (
    //#$ports
    input                        pi_clk,
    input                        pi_reset_n,
    input                        pi_zeroize,
    input mlkem_masked_bf_uvwi_t pi_uvw_i,
    input [4:0][13:0]            pi_rnd_i,
    input bf_uvo_t               po_uv_o
    //$#//
);

default clocking default_clk @(posedge pi_clk); endclocking

sequence reset_sequence;
  !pi_reset_n ##1 pi_reset_n;
endsequence

//Reset property
property run_reset_p;
  reset_sequence |->
  po_uv_o.u20_o == 0 &&
  po_uv_o.u21_o == 0 &&
  po_uv_o.v20_o == 0 &&
  po_uv_o.v21_o == 0;
endproperty
run_reset_a: assert property (run_reset_p);


function logic unsigned [MLKEM_Q_WIDTH-1:0] div2(logic unsigned [MLKEM_Q_WIDTH-1:0] data);
  logic unsigned [MLKEM_Q_WIDTH-1:0] result;
  result = MLKEM_Q_WIDTH'(0);

  if (data[0] != 'd0) begin
    result = ((data >> 'd1) + ((MLKEM_Q + 'd1) / 'd2));
  end else begin
    result = data >> 'd1;
  end

  return result;
endfunction

//Property to check the primary output after cutting the output signals (v11_int,u11_int,u10_int,v10_int) of ntt_mlkem_masked_gs_butterfly.
property run_bfu_1x2_cut_p;
  ##1
  po_uv_o.v21_o == $past(div2(MLKEM_Q_WIDTH'(ntt_mlkem_masked_butterfly1x2.v11_int[0] + ntt_mlkem_masked_butterfly1x2.v11_int[1])), 1) &&
  po_uv_o.v20_o == $past(div2(MLKEM_Q_WIDTH'(ntt_mlkem_masked_butterfly1x2.u11_int[0] + ntt_mlkem_masked_butterfly1x2.u11_int[1])), 1) &&
  po_uv_o.u21_o == $past(div2(MLKEM_Q_WIDTH'(ntt_mlkem_masked_butterfly1x2.v10_int[0] + ntt_mlkem_masked_butterfly1x2.v10_int[1])), 1) &&
  po_uv_o.u20_o == $past(div2(MLKEM_Q_WIDTH'(ntt_mlkem_masked_butterfly1x2.u10_int[0] + ntt_mlkem_masked_butterfly1x2.u10_int[1])), 1);
endproperty
run_bfu_1x2_cut_a: assert property (disable iff(!pi_reset_n | pi_zeroize) run_bfu_1x2_cut_p);

endmodule

