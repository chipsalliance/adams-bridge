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
// | Created on 06.02.2025 at 15:25                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import fv_ntt_masked_pwm_pkg::*;
import ntt_defines_pkg::*;
import fv_ntt_masked_pwm_functions::*;


bind ntt_masked_pwm fv_ntt_masked_pwm_m fv_ntt_masked_pwm(
  .rst_n(ntt_masked_pwm.reset_n && !ntt_masked_pwm.zeroize),
  .clk(ntt_masked_pwm.clk),

  // Ports
  .accumulate(ntt_masked_pwm.accumulate),

  .u(ntt_masked_pwm.u),

  .v(ntt_masked_pwm.v),

  .w(ntt_masked_pwm.w),

  .res_sum(ntt_masked_pwm.res[0] + ntt_masked_pwm.res[1]),

  // States
  .INIT(1'b1),
  .PWM(!ntt_masked_pwm.accumulate),
  .PWMA(ntt_masked_pwm.accumulate)
);
