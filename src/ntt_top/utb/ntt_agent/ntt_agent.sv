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
class ntt_agent extends uvm_agent;

    `uvm_component_utils(ntt_agent)

    uvm_analysis_port#(ntt_txn) ntt_ap;

    ntt_sequencer           ntt_sqcr_i;
    ntt_driver              ntt_driver_i;
    ntt_mon                 ntt_input_mon_i;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ntt_ap = new("ntt_ap", this);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ntt_sqcr_i = ntt_sequencer::type_id::create(.name("ntt_sqcr_i"), .parent(this));
        ntt_driver_i = ntt_driver::type_id::create(.name("ntt_driver_i"), .parent(this));
        ntt_input_mon_i = ntt_mon::type_id::create(.name("ntt_input_mon_i"), .parent(this));
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        ntt_driver_i.seq_item_port.connect(ntt_sqcr_i.seq_item_export);
        ntt_input_mon_i.ntt_input_ap.connect(ntt_ap);
    endfunction: connect_phase

endclass: ntt_agent