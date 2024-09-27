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
class mem_mon extends uvm_monitor;
    `uvm_component_utils(mem_mon)

    uvm_analysis_port#(mem_txn) mem_ap;
    virtual mem_if mem_vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        mem_ap = new("mem_ap", this);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
    endfunction: build_phase

    task run_phase(uvm_phase phase);
        logic port0_readFollowUp;
        logic port1_readFollowUp;
        mem_txn port0_mem_txn_i_pending;
        mem_txn port1_mem_txn_i_pending;
        port0_readFollowUp = 'h0;
        port1_readFollowUp = 'h0;
        port0_mem_txn_i_pending = mem_txn::type_id::create("port0_mem_txn_i_pending");
        port1_mem_txn_i_pending = mem_txn::type_id::create("port1_mem_txn_i_pending");
        port0_mem_txn_i_pending.reset_indicator = 0;
        port1_mem_txn_i_pending.reset_indicator = 0;
        @(negedge mem_vif.reset_n);
        forever begin
            @(posedge mem_vif.clk);
            // check if memory is updated by the TB
            mem_TB_update_check();
            mem_port0_read_write_decoder (port0_readFollowUp, port0_mem_txn_i_pending);
            mem_port1_read_write_decoder (port1_readFollowUp, port1_mem_txn_i_pending);

        end

    endtask

    task mem_TB_update_check();
        mem_txn mem_txn_i;
        if (mem_vif.update_mem) begin
            mem_txn_i = mem_txn::type_id::create("mem_txn_i");
            mem_txn_i.update_mem = mem_vif.update_mem;
            for (int i = 0; i<(2**MLDSA_MEM_ADDR_WIDTH); i++ ) begin
                mem_vif.read_mem(i, mem_txn_i.artificialMemory[i]);
            end
            mem_ap.write(mem_txn_i);
        end
    endtask: mem_TB_update_check

    
    task mem_port0_read_write_decoder (inout logic readFollowUp, inout mem_txn mem_txn_i_pending);
        mem_txn mem_txn_i;
        logic [3:0] mem_states;
        mem_states = {mem_vif.mem_s_cb.reset_n, mem_vif.mem_s_cb.mem_port0_req.rd_wr_en, readFollowUp};
        casez (mem_states)
            4'b0???: begin
                // Reset is active and others are ignored

                // This if condition avoids sending multiple items to scoreboard
                // This if has a lock mechanism and the lock is released in
                // non-reset states.
                if (mem_txn_i_pending.reset_indicator == 0) begin
                    mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                    // the indicator flag is high, meaning is DUT is in reset state
                    mem_txn_i.reset_indicator = 1;
                    // mem_txn_i.mem_port0_req = '{default: '0};
                    mem_txn_i.mem_port0_req.rd_wr_en = mem_rw_mode_e'(RW_IDLE);
                    mem_txn_i.mem_port0_req.addr = 'h0;
                    mem_txn_i.p0_read_data = 'h0;
                    mem_txn_i.p0_write_data = 'h0;
                    readFollowUp = 0;
                    mem_txn_i_pending.reset_indicator = 1;
                    mem_ap.write(mem_txn_i);
                end
            end
            {1'b1, mem_rw_mode_e'(RW_WRITE), 1'b0}: begin
                // Write observed but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port0_req = mem_vif.mem_s_cb.mem_port0_req;
                mem_txn_i.p0_read_data = 'h0;
                mem_txn_i.p0_write_data = mem_vif.mem_s_cb.p0_write_data;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_WRITE), 1'b1}: begin
                // Write comes but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port0_req = mem_txn_i_pending.mem_port0_req;
                mem_txn_i.p0_read_data = mem_vif.mem_s_cb.p0_read_data;
                mem_txn_i.p0_write_data = 'h0;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                // Pending read request is being sent
                mem_ap.write(mem_txn_i);
                // Now write request is being sent.
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port0_req = mem_vif.mem_s_cb.mem_port0_req;
                mem_txn_i.p0_read_data = 'h0;
                mem_txn_i.p0_write_data = mem_vif.mem_s_cb.p0_write_data;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_READ), 1'b0}: begin
                // Read is requested but the RAM needs one cycle to respond
                mem_txn_i_pending.mem_port0_req = mem_vif.mem_s_cb.mem_port0_req;
                readFollowUp = 1;
                mem_txn_i_pending.reset_indicator = 0;
            end
            {1'b1, mem_rw_mode_e'(RW_READ), 1'b1}: begin
                // Another read is requested while the pending read
                // is going to be sent
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port0_req = mem_txn_i_pending.mem_port0_req;
                mem_txn_i.p0_read_data = mem_vif.mem_s_cb.p0_read_data;
                mem_txn_i.p0_write_data = 'h0;
                // Read is requested but the RAM needs one cycle to respond                 
                mem_txn_i_pending.mem_port0_req = mem_vif.mem_s_cb.mem_port0_req;
                readFollowUp = 1;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_IDLE), 1'b0}: begin
                // Memory is Idle                    
            end
            {1'b1, mem_rw_mode_e'(RW_IDLE), 1'b1}: begin
                // Mem is in the idle state but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port0_req = mem_txn_i_pending.mem_port0_req;
                mem_txn_i.p0_read_data = mem_vif.mem_s_cb.p0_read_data;
                mem_txn_i.p0_write_data = 'h0;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                // Pending read request is being sent
                mem_ap.write(mem_txn_i);                  
            end
            default: begin
                // Handle unexpected states
                `uvm_error("MEM_MON", "Unexpected state in mem_states for port 0")
            end
        endcase
    endtask: mem_port0_read_write_decoder

    task mem_port1_read_write_decoder (inout logic readFollowUp, inout mem_txn mem_txn_i_pending);
        mem_txn mem_txn_i;
        logic [3:0] mem_states;
        mem_states = {mem_vif.mem_s_cb.reset_n, mem_vif.mem_s_cb.mem_port1_req.rd_wr_en, readFollowUp};
        casez (mem_states)
            4'b0???: begin
                // Reset is active and others are ignored

                // This if condition avoids sending multiple items to scoreboard
                // This if has a lock mechanism and the lock is released in
                // non-reset states.
                if (mem_txn_i_pending.reset_indicator == 0) begin
                    mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                    // the indicator flag is high, meaning is DUT is in reset state
                    mem_txn_i.reset_indicator = 1;
                    mem_txn_i.mem_port1_req.rd_wr_en = mem_rw_mode_e'(RW_IDLE);
                    mem_txn_i.mem_port1_req.addr = 'h0;
                    mem_txn_i.p1_read_data = 'h0;
                    mem_txn_i.p1_write_data = 'h0;
                    readFollowUp = 0;
                    mem_txn_i_pending.reset_indicator = 1;
                    mem_ap.write(mem_txn_i);
                end
            end
            {1'b1, mem_rw_mode_e'(RW_WRITE), 1'b0}: begin
                // Write observed but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port1_req = mem_vif.mem_s_cb.mem_port1_req;
                mem_txn_i.p1_read_data = 'h0;
                mem_txn_i.p1_write_data = mem_vif.mem_s_cb.p1_write_data;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_WRITE), 1'b1}: begin
                // Write comes but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port1_req = mem_txn_i_pending.mem_port1_req;
                mem_txn_i.p1_read_data = mem_vif.mem_s_cb.p1_read_data;
                mem_txn_i.p1_write_data = 'h0;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                // Pending read request is being sent
                mem_ap.write(mem_txn_i);
                // Now write request is being sent.
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port1_req = mem_vif.mem_s_cb.mem_port1_req;
                mem_txn_i.p1_read_data = 'h0;
                mem_txn_i.p1_write_data = mem_vif.mem_s_cb.p1_write_data;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_READ), 1'b0}: begin
                // Read is requested but the RAM needs one cycle to respond
                mem_txn_i_pending.mem_port1_req = mem_vif.mem_s_cb.mem_port1_req;
                readFollowUp = 1;
                mem_txn_i_pending.reset_indicator = 0;
            end
            {1'b1, mem_rw_mode_e'(RW_READ), 1'b1}: begin
                // Another read is requested while the pending read
                // is going to be sent
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port1_req = mem_txn_i_pending.mem_port1_req;
                mem_txn_i.p1_read_data = mem_vif.mem_s_cb.p1_read_data;
                mem_txn_i.p1_write_data = 'h0;
                // Read is requested but the RAM needs one cycle to respond                 
                mem_txn_i_pending.mem_port1_req = mem_vif.mem_s_cb.mem_port1_req;
                readFollowUp = 1;
                mem_txn_i_pending.reset_indicator = 0;
                mem_ap.write(mem_txn_i);
            end
            {1'b1, mem_rw_mode_e'(RW_IDLE), 1'b0}: begin
                // Memory is Idle                    
            end
            {1'b1, mem_rw_mode_e'(RW_IDLE), 1'b1}: begin
                // Mem is in the idle state but there is also a pending read
                mem_txn_i = mem_txn::type_id::create("mem_txn_i");
                mem_txn_i.mem_port1_req = mem_txn_i_pending.mem_port1_req;
                mem_txn_i.p1_read_data = mem_vif.mem_s_cb.p1_read_data;
                mem_txn_i.p1_write_data = 'h0;
                readFollowUp = 0;
                mem_txn_i_pending.reset_indicator = 0;
                // Pending read request is being sent
                mem_ap.write(mem_txn_i);                  
            end
            default: begin
                // Handle unexpected states
                `uvm_error("MEM_MON", "Unexpected state in mem_states for port 1")
            end
        endcase
    endtask: mem_port1_read_write_decoder

endclass