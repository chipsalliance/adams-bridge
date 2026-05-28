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
// | Created on 04.02.2025 at 22:03                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import fv_ntt_masked_BFU_mult_functions::*;


bind ntt_masked_BFU_mult fv_ntt_masked_BFU_mult_m fv_ntt_masked_BFU_mult(
  .rst_n(ntt_masked_BFU_mult.reset_n && !ntt_masked_BFU_mult.zeroize),
  .clk(ntt_masked_BFU_mult.clk),

  // Ports
  .u(ntt_masked_BFU_mult.u),

  .v(ntt_masked_BFU_mult.v),

  //.res(ntt_masked_BFU_mult.res),

  // States
  .COMPUTE(1'b1)
);
