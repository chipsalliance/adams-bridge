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
//======================================================================
//
// ntt_masked_gs_butterfly.sv
// --------
// Only performs gs (INTT) mode of operation. All blocks are masked

module ntt_masked_gs_butterfly
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
    #(
        parameter WIDTH = 46
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire [1:0][WIDTH-1:0] opu_i,
        input wire [1:0][WIDTH-1:0] opv_i,
        input wire [1:0][WIDTH-1:0] opw_i,
        input wire [4:0][WIDTH-1:0] rnd_i,

        output logic [1:0] u_o [WIDTH-1:0], //TODO: make packed?
        output logic [1:0] v_o [WIDTH-1:0]
    );


    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) add_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(opu_i),
        .v(opv_i),
        .rnd0(rnd_i[0]),
        .rnd1(rnd_i[1]),
        .rnd2(rnd_i[2]),
        .rnd3(rnd_i[3]),
        .res()
    );

    ntt_masked_BFU_add_sub #(
        .WIDTH(WIDTH)
    ) sub_inst_0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .u(opu_i),
        .v(opv_i),
        .rnd0(rnd_i[0]),
        .rnd1(rnd_i[1]),
        .rnd2(rnd_i[2]),
        .rnd3(rnd_i[3]),
        .res()
    );

endmodule
