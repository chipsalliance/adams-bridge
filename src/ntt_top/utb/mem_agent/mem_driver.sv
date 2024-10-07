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
class mem_driver extends uvm_driver#(mem_txn);
    `uvm_component_utils(mem_driver)

    virtual mem_if mem_vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction: build_phase

    task run_phase(uvm_phase phase);

        mem_txn mem_txn_i;
        logic [MLDSA_MEM_ADDR_WIDTH-1:0] addr;
        forever begin
            @(negedge mem_vif.clk);
            seq_item_port.try_next_item(mem_txn_i);
            if (mem_txn_i != null) begin
                if(mem_txn_i.update_mem  == 1 ) begin
                    mem_vif.update_mem      <= mem_txn_i.update_mem;
                    for (int i = 0; i<(2**MLDSA_MEM_ADDR_WIDTH); i++ ) begin
                        addr = i;
                        mem_vif.update_mem_task(addr, mem_txn_i.artificialMemory[addr]);
                    end
                    seq_item_port.item_done();
                end
                else begin
                    mem_vif.update_mem      <= 0;               
                end
            end
            else begin
                mem_vif.update_mem      <= 0;               
            end
        end

    endtask

endclass
