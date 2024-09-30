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
// import ntt_utb_defines::*;
// import ntt_defines_pkg::*;
// import uvm_pkg::*;


class mem_txn extends uvm_sequence_item;

    rand bit reset_n;
    rand bit reset_indicator;
    rand  mem_if_t mem_port0_req;
    rand  mem_if_t mem_port1_req;
    rand  bit [MEM_DATA_WIDTH-1:0] p0_read_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p0_write_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p1_read_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p1_write_data;
    rand bit update_mem;
    rand bit [MEM_DATA_WIDTH-1:0]    artificialMemory [];

    // Define constants
    localparam int MLDSA_Q = 23'd8380417;


    function new(string name = "");
       super.new(name);
       artificialMemory = new[MLDSA_MEM_MAX_DEPTH];
    endfunction: new

    //Constraint for artificialMemory
    constraint artificialMemory_c {
        foreach (artificialMemory[i]) {
            (artificialMemory[i][23:0] < MLDSA_Q) &&
            (artificialMemory[i][47:24] < MLDSA_Q) &&
            (artificialMemory[i][71:48] < MLDSA_Q) &&
            (artificialMemory[i][95:72] < MLDSA_Q);
        }
    }


    `uvm_object_utils_begin(mem_txn)
        `uvm_field_int(reset_n, UVM_ALL_ON)
        `uvm_field_int(mem_port0_req.addr, UVM_ALL_ON)
        `uvm_field_enum(mem_rw_mode_e, mem_port0_req.rd_wr_en, UVM_ALL_ON)
        `uvm_field_int(mem_port1_req.addr, UVM_ALL_ON)
        `uvm_field_enum(mem_rw_mode_e, mem_port1_req.rd_wr_en, UVM_ALL_ON)
        `uvm_field_int(p0_read_data, UVM_ALL_ON)
        `uvm_field_int(p0_write_data, UVM_ALL_ON)
        `uvm_field_int(p1_read_data, UVM_ALL_ON)
        `uvm_field_int(p1_write_data, UVM_ALL_ON)
        `uvm_field_int(update_mem, UVM_ALL_ON)
        `uvm_field_array_int(artificialMemory, UVM_ALL_ON)
    `uvm_object_utils_end



endclass: mem_txn
