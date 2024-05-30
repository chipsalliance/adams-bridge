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
//
//======================================================================

`ifndef SHA3_TB_PKG
`define SHA3_TB_PKG

package sha3_tb_pkg;

    import sha3_pkg::*;

    //input vector size in bytes
    parameter INPUT_VECTOR_W = 2592;
    parameter MAX_MSG_WR = INPUT_VECTOR_W/(MsgWidth/8);

    parameter MAX_SQUEEZE = 5;
    parameter SHAKE256_W = 1088;
    parameter SHAKE128_W = 1344;
    parameter SHAKE128_SIZE = SHAKE128_W + SHAKE128_W*MAX_SQUEEZE;
    parameter SHAKE256_SIZE = SHAKE256_W + SHAKE256_W*MAX_SQUEEZE;
    //Expected results structs
    typedef struct packed {
        logic [MAX_SQUEEZE-1:0][SHAKE128_W-1:0] squeeze;
        logic [SHAKE128_W-1:0] absorb;
    } shake128_res_t;
    typedef struct packed {
        logic [SHAKE128_SIZE-SHAKE256_SIZE-1:0]  rsvd;
        logic [MAX_SQUEEZE-1:0][SHAKE256_W-1:0] squeeze;
        logic [SHAKE256_W-1:0] absorb;
    } shake256_res_t;
    typedef struct packed {
        logic [SHAKE128_SIZE-512-1:0] rsvd;
        logic [512-1:0]  digest;
    } sha3_512_res_t;
    typedef struct packed {
        logic [SHAKE128_SIZE-256-1:0] rsvd;
        logic [256-1:0]  digest;
    } sha3_256_res_t;

    typedef union packed {
        shake256_res_t shake256;
        shake128_res_t shake128;
        sha3_512_res_t sha3_512;
        sha3_256_res_t sha3_256;
    } exp_results_u;

    //test vector struct
    typedef struct {
        rand sha3_pkg::sha3_mode_e mode;
        rand sha3_pkg::keccak_strength_e strength;
        rand logic [MAX_MSG_WR-1:0][MsgWidth-1:0] input_vector;
        logic [MAX_MSG_WR-1:0][MsgStrbW-1:0] input_valid;
    } keccak_test_vector_t;

    class test;
        rand keccak_test_vector_t vector;
        rand int vector_length;

        constraint length_c { vector_length inside {[1:MAX_MSG_WR*(MsgWidth/8)]}; }

        constraint mode_c { vector.mode inside {sha3_pkg::Shake, sha3_pkg::Sha3}; }

        constraint strength_c { 
        (vector.mode == sha3_pkg::Sha3) -> vector.strength inside {sha3_pkg::L256, sha3_pkg::L512};
        (vector.mode == sha3_pkg::Shake) -> vector.strength inside {sha3_pkg::L256, sha3_pkg::L128}; 
        solve vector.mode before vector.strength;
        }

    endclass

endpackage
`endif