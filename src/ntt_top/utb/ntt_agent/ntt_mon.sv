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
class ntt_mon extends uvm_monitor;

    `uvm_component_utils(ntt_mon)

    // Analysis port for sending transactions to the scoreboard
    uvm_analysis_port#(ntt_txn) ntt_input_ap;
    // Virtual interface for connecting to the DUT signals
    virtual ntt_if ntt_vif;

    // Constructor to initialize the monitor
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ntt_input_ap = new("ntt_input_ap", this);
    endfunction: new

    // Build phase to get the virtual interface
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction: build_phase

    // Run phase to monitor the DUT signals and send transactions to the scoreboard
    task run_phase(uvm_phase phase);
        int stage_idx = 0; // Variable to track the current stage index

        forever begin
            @ntt_vif.ntt_s_cb; // Wait for a change on the ntt_s_cb signal

            if (ntt_vif.ntt_s_cb.ntt_enable) begin
                ntt_txn ntt_txn_i;
                ntt_txn_i = ntt_txn::type_id::create("ntt_txn_i");

                // Capture relevant signals from the DUT
                ntt_txn_i.zeroize                = ntt_vif.ntt_s_cb.zeroize;
                ntt_txn_i.mode                   = ntt_vif.ntt_s_cb.mode;
                ntt_txn_i.ntt_enable             = ntt_vif.ntt_s_cb.ntt_enable;
                ntt_txn_i.ntt_mem_base_addr      = ntt_vif.ntt_s_cb.ntt_mem_base_addr;
                ntt_txn_i.pwo_mem_base_addr      = ntt_vif.ntt_s_cb.pwo_mem_base_addr;
                ntt_txn_i.accumulate             = ntt_vif.ntt_s_cb.accumulate;
                ntt_txn_i.sampler_valid          = ntt_vif.ntt_s_cb.sampler_valid;
                ntt_txn_i.sampler_mode           = ntt_vif.ntt_s_cb.sampler_mode;
                ntt_txn_i.sampler_data           = ntt_vif.ntt_s_cb.sampler_data;
                ntt_txn_i.ntt_done               = ntt_vif.ntt_s_cb.ntt_done;
                ntt_txn_i.stage_done             = 0; // Set stage_done to 0 initially
                ntt_txn_i.stage_idx              = 0; // Set stage_idx to 0 initially

                // Initialize stage index when ntt_enable is asserted
                stage_idx = 0;

                // Send the transaction to the scoreboard
                ntt_input_ap.write(ntt_txn_i);
            end
            else if (ntt_vif.ntt_s_cb.stage_done) begin
                ntt_txn ntt_txn_i;
                ntt_txn_i = ntt_txn::type_id::create("ntt_txn_i");

                // Capture relevant signals from the DUT
                ntt_txn_i.zeroize                = ntt_vif.ntt_s_cb.zeroize;
                ntt_txn_i.mode                   = ntt_vif.ntt_s_cb.mode;
                ntt_txn_i.ntt_enable             = ntt_vif.ntt_s_cb.ntt_enable;
                ntt_txn_i.ntt_mem_base_addr      = ntt_vif.ntt_s_cb.ntt_mem_base_addr;
                ntt_txn_i.pwo_mem_base_addr      = ntt_vif.ntt_s_cb.pwo_mem_base_addr;
                ntt_txn_i.accumulate             = ntt_vif.ntt_s_cb.accumulate;
                ntt_txn_i.sampler_valid          = ntt_vif.ntt_s_cb.sampler_valid;
                ntt_txn_i.sampler_mode           = ntt_vif.ntt_s_cb.sampler_mode;
                ntt_txn_i.sampler_data           = ntt_vif.ntt_s_cb.sampler_data;
                ntt_txn_i.ntt_done               = ntt_vif.ntt_s_cb.ntt_done;
                ntt_txn_i.stage_done             = ntt_vif.ntt_s_cb.stage_done;
                ntt_txn_i.stage_idx              = stage_idx; // Set stage_idx to 0 initially
                stage_idx++;

                // Send the transaction to the scoreboard
                ntt_input_ap.write(ntt_txn_i);
            end
            else if (ntt_vif.ntt_s_cb.ntt_done) begin
                ntt_txn ntt_txn_i;
                ntt_txn_i = ntt_txn::type_id::create("ntt_txn_i");

                // Capture relevant signals from the DUT
                ntt_txn_i.zeroize                = ntt_vif.ntt_s_cb.zeroize;
                ntt_txn_i.mode                   = ntt_vif.ntt_s_cb.mode;
                ntt_txn_i.ntt_enable             = ntt_vif.ntt_s_cb.ntt_enable;
                ntt_txn_i.ntt_mem_base_addr      = ntt_vif.ntt_s_cb.ntt_mem_base_addr;
                ntt_txn_i.pwo_mem_base_addr      = ntt_vif.ntt_s_cb.pwo_mem_base_addr;
                ntt_txn_i.accumulate             = ntt_vif.ntt_s_cb.accumulate;
                ntt_txn_i.sampler_valid          = ntt_vif.ntt_s_cb.sampler_valid;
                ntt_txn_i.sampler_mode           = ntt_vif.ntt_s_cb.sampler_mode;
                ntt_txn_i.sampler_data           = ntt_vif.ntt_s_cb.sampler_data;
                ntt_txn_i.ntt_done               = ntt_vif.ntt_s_cb.ntt_done;
                ntt_txn_i.stage_done             = ntt_vif.ntt_s_cb.stage_done;
                ntt_txn_i.stage_idx              = stage_idx; // Set stage_idx to 0 initially

                // Send the transaction to the scoreboard
                ntt_input_ap.write(ntt_txn_i);
            end
        end
    endtask

endclass




// class ntt_mon extends uvm_monitor;

//     `uvm_component_utils(ntt_mon)

//     uvm_analysis_port#(ntt_txn) ntt_input_ap;
//     virtual ntt_if ntt_vif;

//     function new(string name, uvm_component parent);
//         super.new(name, parent);
//         ntt_input_ap = new("ntt_input_ap", this);
//     endfunction: new

//     function void build_phase(uvm_phase phase);
//         super.build_phase(phase);
//         // assert( uvm_config_db#( virtual ntt_if )::get( this, "", "ntt_vif", ntt_vif));
//     endfunction: build_phase

//     task run_phase(uvm_phase phase);

//         forever begin
//             @ntt_vif.ntt_s_cb;
//             if(ntt_vif.ntt_s_cb.ntt_enable) begin
//                 ntt_txn ntt_txn_i;
//                 ntt_txn_i = ntt_txn::type_id::create("ntt_txn_i");
                
//                 ntt_txn_i.zeroize                = ntt_vif.ntt_s_cb.zeroize;
//                 ntt_txn_i.mode                   = ntt_vif.ntt_s_cb.mode;
//                 ntt_txn_i.ntt_enable             = ntt_vif.ntt_s_cb.ntt_enable;

//                 ntt_txn_i.ntt_mem_base_addr      = ntt_vif.ntt_s_cb.ntt_mem_base_addr;
//                 ntt_txn_i.pwo_mem_base_addr      = ntt_vif.ntt_s_cb.pwo_mem_base_addr;

//                 ntt_txn_i.accumulate             = ntt_vif.ntt_s_cb.accumulate;
//                 ntt_txn_i.sampler_valid          = ntt_vif.ntt_s_cb.sampler_valid;
//                 ntt_txn_i.sampler_mode           = ntt_vif.ntt_s_cb.sampler_mode;
//                 ntt_txn_i.sampler_data           = ntt_vif.ntt_s_cb.sampler_data;

//                 ntt_txn_i.ntt_done               = ntt_vif.ntt_s_cb.ntt_done;
                
//                 ntt_input_ap.write(ntt_txn_i);
//             end
//         end

//     endtask

// endclass