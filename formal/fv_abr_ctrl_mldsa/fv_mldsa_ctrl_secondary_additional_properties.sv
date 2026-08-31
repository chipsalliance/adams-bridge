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

module fv_mldsa_ctrl_secondary_additional_properties (
  input logic rst_n,
  input logic clk,

  input logic [1:0] normcheck_enable,
  input logic normcheck_enable_o
);


default clocking default_clk @(posedge clk); endclocking


property verify_normcheck_enable_o_p;
  normcheck_enable_o == normcheck_enable[0] || normcheck_enable[1]
endproperty
verify_normcheck_enable_o_a: assert property (disable iff(!(rst_n && !mldsa_ctrl.zeroize)) verify_normcheck_enable_o_p);


property verify_normcheck_enable_onehot_p;
  $onehot0(normcheck_enable);
endproperty
verify_normcheck_enable_onehot_a: assert property (disable iff(!(rst_n && !mldsa_ctrl.zeroize)) verify_normcheck_enable_onehot_p);

  
endmodule


bind mldsa_ctrl fv_mldsa_ctrl_secondary_additional_properties additional_inst(
  .rst_n(mldsa_ctrl.rst_b),
  .clk(mldsa_ctrl.clk),
  .normcheck_enable(mldsa_ctrl.normcheck_enable),
  .normcheck_enable_o(mldsa_ctrl.normcheck_enable_o)
);
