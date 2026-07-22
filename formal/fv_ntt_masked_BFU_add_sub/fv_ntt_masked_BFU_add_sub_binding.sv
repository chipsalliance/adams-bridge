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
// | Created on 03.02.2025 at 18:02                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import fv_ntt_masked_BFU_add_sub_functions::*;


bind ntt_masked_BFU_add_sub fv_ntt_masked_BFU_add_sub_m fv_ntt_masked_BFU_add_sub(
  .rst_n(ntt_masked_BFU_add_sub.reset_n && !ntt_masked_BFU_add_sub.zeroize),
  .clk(ntt_masked_BFU_add_sub.clk),

  // Ports
  .sub(ntt_masked_BFU_add_sub.sub),

  .u(ntt_masked_BFU_add_sub.u),

  .v(ntt_masked_BFU_add_sub.v),

  //.res(ntt_masked_BFU_add_sub.res),

  // States
  .COMPUTE(1'b1)
);
