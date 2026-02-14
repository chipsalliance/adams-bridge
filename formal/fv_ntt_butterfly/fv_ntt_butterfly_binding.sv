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
// | Created on 19.03.2025 at 18:24                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import ntt_butterfly_functions::*;


bind ntt_butterfly fv_ntt_butterfly_m fv_ntt_butterfly(
  .rst_n(ntt_butterfly.reset_n && !ntt_butterfly.zeroize),
  .clk(ntt_butterfly.clk),

  // Ports
  .accumulate(ntt_butterfly.accumulate),

  .add_res(ntt_butterfly.add_res),

  .mode(ntt_butterfly.mode),

  .opu_i(ntt_butterfly.opu_i),

  .opv_i(ntt_butterfly.opv_i),

  .opw_i(ntt_butterfly.opw_i),

  .add_res_d1(ntt_butterfly.add_res_d1),

  .add_res_d2(ntt_butterfly.add_res_d2),

  .mul_opa(ntt_butterfly.mul_opa),

  .mul_opb(ntt_butterfly.mul_opb),

  .pwm_res_o(ntt_butterfly.pwm_res_o),

  .u_o(ntt_butterfly.u_o),

  .u_reg(ntt_butterfly.u_reg),

  .u_reg_d2(ntt_butterfly.u_reg_d2),

  .u_reg_d3(ntt_butterfly.u_reg_d3),

  .u_reg_d4(ntt_butterfly.u_reg_d4),

  .v_o(ntt_butterfly.v_o),

  .w_reg(ntt_butterfly.w_reg),

  .w_reg_d2(ntt_butterfly.w_reg_d2),

  .w_reg_d3(ntt_butterfly.w_reg_d3),

  .w_reg_d4(ntt_butterfly.w_reg_d4),

  // States
  .CT(ntt_butterfly.mode  == 'd0),
  .GS(ntt_butterfly.mode  == 'd1),
  .INIT(1'b1),
  .PWA_PWS(ntt_butterfly.mode > 'd2),
  .PWM_ACC((ntt_butterfly.mode  == 'd2) && (ntt_butterfly.accumulate)),
  .PWM_NOT_ACC((ntt_butterfly.mode  == 'd2) && (!ntt_butterfly.accumulate))
);
