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

// +---------------------------------------------------+
// | Copyright (c) LUBIS EDA GmbH, all rights reserved |
// | Created on 30.10.2025 at 09:24                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import abr_sha3_pkg::*;
import fv_abr_sha3_pkg::*;


module fv_fv_abr_sha3_ref_wrapper_m;


function e_state fv_sha3_fsm_o();
if(abr_sha3.sha3_fsm_o == StIdle) begin
    return IDLE_ST;
end else if (abr_sha3.sha3_fsm_o == StAbsorb) begin
    return ABSORB_ST;
end else if (abr_sha3.sha3_fsm_o == StSqueeze) begin
    return SQUEEZE_ST;
end else if (abr_sha3.sha3_fsm_o == StManualRun) begin
    return RUN_ST;
end
endfunction


fv_fv_abr_sha3_m fv_fv_abr_sha3(
  .rst(!abr_sha3.rst_b || abr_sha3.zeroize),
  .clk(abr_sha3.clk_i),

  // Ports
  .fv_absorbed_i(abr_sha3.u_pad.absorbed_o == abr_prim_mubi_pkg::MuBi4True),

  .fv_keccak_complete_i_vld(abr_sha3.keccak_complete),
  .fv_keccak_complete_i_rdy(),
  .fv_keccak_complete_i(abr_sha3.keccak_complete),

  .fv_run_i(abr_sha3.run_i),

  .fv_start_i(abr_sha3.start_i),

  .fv_state_valid_hold_i(abr_sha3.state_valid_hold_i),

  .fv_absorbed_o(abr_sha3.absorbed_o == abr_prim_mubi_pkg::MuBi4True),

  .fv_sha3_fsm_o(fv_sha3_fsm_o()),

  .fv_squeezing_o(abr_sha3.squeezing_o),

  .fv_state_valid_o(abr_sha3.state_valid_o),

  // States
  .ABSORB(abr_sha3.st == StAbsorb_sparse),
  .IDLE(abr_sha3.st == StIdle_sparse),
  .RUN(abr_sha3.st == StManualRun_sparse),
  .SQUEEZE(abr_sha3.st == StSqueeze_sparse)
);


endmodule


bind abr_sha3 fv_fv_abr_sha3_ref_wrapper_m fv_fv_abr_sha3_ref_wrapper();
