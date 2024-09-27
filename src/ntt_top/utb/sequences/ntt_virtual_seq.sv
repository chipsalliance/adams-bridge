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
class ntt_virtual_seq extends uvm_sequence#(uvm_sequence_item);

    `uvm_object_utils(ntt_virtual_seq)

    // Declare handles for the sequencers
    mem_sequencer mem_seqr;
    ntt_sequencer ntt_seqr;
    mem_base_seq mem_seq_i;
    ntt_base_seq ntt_seq_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        fork
            begin
                mem_seq_i.start(mem_seqr);
            end
            begin
                #10ns;
                ntt_seq_i.start(ntt_seqr);
            end
        join

        // Optionally, you can add more sequences or additional coordination logic here
    endtask: body

endclass

