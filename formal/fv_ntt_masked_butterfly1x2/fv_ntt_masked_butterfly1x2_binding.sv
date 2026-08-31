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
// | Created on 06.02.2025 at 13:56                    |
// | Contact: contact@lubis-eda.com                    |
// | Author: Tobias Ludwig, Michael Schwarz            |
// +---------------------------------------------------+


import ntt_defines_pkg::*;
import fv_ntt_masked_butterfly1x2_pkg::*;
import fv_ntt_masked_butterfly1x2_functions::*;


bind ntt_masked_butterfly1x2 fv_ntt_masked_butterfly1x2_m fv_ntt_masked_butterfly1x2(
  .rst_n(ntt_masked_butterfly1x2.reset_n && !ntt_masked_butterfly1x2.zeroize),
  .clk(ntt_masked_butterfly1x2.clk),

  // Ports
  .u00(ntt_masked_butterfly1x2.uvw_i.u00_i),

  .u01(ntt_masked_butterfly1x2.uvw_i.u01_i),

  .v00(ntt_masked_butterfly1x2.uvw_i.v00_i),

  .v01(ntt_masked_butterfly1x2.uvw_i.v01_i),

  .w00(ntt_masked_butterfly1x2.uvw_i.w00_i),

  .w01(ntt_masked_butterfly1x2.uvw_i.w01_i),

  .uv_0_u20(ntt_masked_butterfly1x2.uv_o.u20_o),

  .uv_0_u21(ntt_masked_butterfly1x2.uv_o.u21_o),

  .uv_0_v20(ntt_masked_butterfly1x2.uv_o.v20_o),

  .uv_0_v21(ntt_masked_butterfly1x2.uv_o.v21_o),

  // States
  .COMPUTE(1'b1)
);
