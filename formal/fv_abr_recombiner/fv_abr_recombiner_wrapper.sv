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
// | Contact: contact@lubis-eda.com                    |
// +---------------------------------------------------+

// Wrapper around the combinational abr_recombiner. It adds the clock and reset pins
// needed by the formal tool; the DUT itself has neither.

module fv_abr_recombiner_wrapper
    import abr_params_pkg::*;
(
    input  logic                                 clk,
    input  logic                                 rst_b,
    input  logic                                 pi_mode,
    input  logic [REG_SIZE*COEFF_PER_CLK-1:0]    pi_share0_i,
    input  logic [REG_SIZE*COEFF_PER_CLK-1:0]    pi_share1_i,
    output logic [REG_SIZE*COEFF_PER_CLK-1:0]    po_data_o
);

    abr_recombiner abr_recombiner_i (
        .mode     (pi_mode),
        .share0_i (pi_share0_i),
        .share1_i (pi_share1_i),
        .data_o   (po_data_o)
    );

endmodule
