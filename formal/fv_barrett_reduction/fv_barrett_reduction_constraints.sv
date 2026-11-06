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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_barrett_reduction_constraints
#(
    parameter prime    = 3329,
    parameter REG_SIZE = $clog2(prime),
    //#$localparams
    localparam K = 2*REG_SIZE,
    localparam m = (1<<K)/prime
    //$#//
) (
    //#$ports
    input logic [2*REG_SIZE-1:0] pi_x,
    input logic [REG_SIZE-1:0]   po_inv,
    input logic [REG_SIZE-1:0]   po_r
    //$#//
);

endmodule

