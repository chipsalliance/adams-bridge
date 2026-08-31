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
// | Created on 12.05.2025 at 19:55                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import fv_ntt_masked_gs_butterfly_pkg::*;
import fv_ntt_masked_gs_butterfly_functions::*;


bind ntt_masked_gs_butterfly fv_ntt_masked_gs_butterfly_m fv_ntt_masked_gs_butterfly(
  .rst_n(ntt_masked_gs_butterfly.reset_n && !ntt_masked_gs_butterfly.zeroize),
  .clk(ntt_masked_gs_butterfly.clk),

  // Ports
  .accumulate(ntt_masked_gs_butterfly.accumulate),

  .mode(ntt_masked_gs_butterfly.mode),

  .u(ntt_masked_gs_butterfly.opu_i),

  .v(ntt_masked_gs_butterfly.opv_i),

  .w(ntt_masked_gs_butterfly.opw_i),

  .u_0((ntt_masked_gs_butterfly.u_o_0 + ntt_masked_gs_butterfly.u_o_1) % 'h400000000000),

  .v_0((ntt_masked_gs_butterfly.v_o_0 + ntt_masked_gs_butterfly.v_o_1) % 'h400000000000),

  // States
  .INIT(1'b1),
  .NON_PWM(ntt_masked_gs_butterfly.mode != 'd2),
  .PWM((ntt_masked_gs_butterfly.mode == 'd2) && !ntt_masked_gs_butterfly.accumulate),
  .PWMA((ntt_masked_gs_butterfly.mode == 'd2) && ntt_masked_gs_butterfly.accumulate)
);
