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
class ntt_fwd_seq extends ntt_base_seq;

    `uvm_object_utils(ntt_fwd_seq)
    ntt_txn ntt_txn_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        ntt_txn_i = ntt_txn::type_id::create(.name("ntt_txn_i"));
        start_item(ntt_txn_i);
        assert(ntt_txn_i.randomize() with {
            ntt_enable == 1;
            mode == mode_t'(ct);       // Set mode to 'ct'
            zeroize == 0;              // Set zeroize to 0
            accumulate == 0;
            sampler_valid == 0;
            sampler_mode == 0;
            sampler_data == 0;
        }) else begin
            `uvm_error("RANDOMIZE_FAIL", "Randomization failed for ntt_txn_i")
        end
        finish_item(ntt_txn_i);
    endtask: body

endclass