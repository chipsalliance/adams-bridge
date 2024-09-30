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
class mem_base_seq extends uvm_sequence#(mem_txn);

    `uvm_object_utils(mem_base_seq)

    function new (string name = "");
        super.new(name);
    endfunction: new

endclass

class mem_init_seq extends mem_base_seq;

    `uvm_object_utils(mem_init_seq)
    mem_txn mem_txn_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        mem_txn_i = mem_txn::type_id::create(.name("mem_txn_i"));
        start_item(mem_txn_i);
        assert(mem_txn_i.randomize() with {
            update_mem == 1;
        });
        finish_item(mem_txn_i);
    endtask: body

endclass