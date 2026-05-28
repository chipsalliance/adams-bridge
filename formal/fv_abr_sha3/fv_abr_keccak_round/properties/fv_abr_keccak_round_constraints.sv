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

module fv_abr_keccak_round_constraints
  import abr_prim_mubi_pkg::*;
(
  input clk_i,
  input ready_o,
  input run_i,
  input abr_prim_mubi_pkg::mubi4_t clear_i
);

default clocking default_clk @(posedge clk_i); endclocking


assume_run_i: assume property(
  ready_o
|->
  s_eventually(clear_i == 4'h9 && run_i)
);


endmodule


bind abr_keccak_round fv_abr_keccak_round_constraints constraints_inst (
  .clk_i(clk_i),
  .ready_o(ready_o),
  .run_i(run_i),
  .clear_i(clear_i)
);