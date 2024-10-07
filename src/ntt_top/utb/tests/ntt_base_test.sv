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
class ntt_base_test extends uvm_test;

    `uvm_component_utils(ntt_base_test)

    ntt_env             ntt_env_i;
    mem_init_seq        mem_init_seq_i;
    ntt_fwd_seq         ntt_fwd_seq_i;
    ntt_inv_seq         ntt_inv_seq_i;
    ntt_virtual_seq     ntt_virtual_seq_i;

    virtual ntt_if ntt_vif;
    virtual mem_if ntt_mem_vif;
    virtual mem_if pwm_a_mem_vif;
    virtual mem_if pwm_b_mem_vif;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ntt_env_i = ntt_env::type_id::create(.name("ntt_env_i"), .parent(this));

        // Get the virtual interfaces from the UVM configuration database        
        if (!uvm_config_db#(virtual ntt_if)::get(this, "", "ntt_vif", ntt_vif)) begin
            `uvm_fatal("NOVIF", "NTT virtual interface is not gotten by the test");
        end
        if (!uvm_config_db#(virtual mem_if)::get(this, "", "ntt_mem_vif", ntt_mem_vif)) begin
            `uvm_fatal("NOVIF", "NTT Memory virtual interface is not gotten by the test");
        end
        if (!uvm_config_db#(virtual mem_if)::get(this, "", "pwm_a_mem_vif", pwm_a_mem_vif)) begin
            `uvm_fatal("NOVIF", "PWM A Memory virtual interface is not gotten by the test");
        end
        if (!uvm_config_db#(virtual mem_if)::get(this, "", "pwm_b_mem_vif", pwm_b_mem_vif)) begin
            `uvm_fatal("NOVIF", "PWM B Memory virtual interface is not gotten by the test");
        end

    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);

        ntt_env_i.ntt_agent_i.ntt_driver_i.ntt_vif = ntt_vif;
        ntt_env_i.ntt_agent_i.ntt_input_mon_i.ntt_vif = ntt_vif;

        ntt_env_i.ntt_mem_i.mem_driver_i.mem_vif = ntt_mem_vif;
        ntt_env_i.ntt_mem_i.mem_mon_i.mem_vif = ntt_mem_vif;

        ntt_env_i.pwm_a_mem_i.mem_driver_i.mem_vif = pwm_a_mem_vif;
        ntt_env_i.pwm_a_mem_i.mem_mon_i.mem_vif = pwm_a_mem_vif;

        ntt_env_i.pwm_b_mem_i.mem_driver_i.mem_vif = pwm_b_mem_vif;
        ntt_env_i.pwm_b_mem_i.mem_mon_i.mem_vif = pwm_b_mem_vif;
    endfunction: connect_phase

    task run_phase(uvm_phase phase);

        mem_init_seq_i = mem_init_seq::type_id::create(.name("mem_init_seq_i"));
        ntt_inv_seq_i = ntt_inv_seq::type_id::create(.name("ntt_inv_seq_i"));
        ntt_virtual_seq_i = ntt_virtual_seq::type_id::create(.name("ntt_virtual_seq_i"));

        phase.raise_objection(this);
        
        //-- Wait for DUT reset completion.
        #150ns;

        

        // Set the sequencers
        ntt_virtual_seq_i.mem_seqr = ntt_env_i.ntt_mem_i.mem_sqcr_i;
        ntt_virtual_seq_i.ntt_seqr = ntt_env_i.ntt_agent_i.ntt_sqcr_i;

        // Set the sequences
        ntt_virtual_seq_i.mem_seq_i = mem_init_seq_i;
        //ntt_virtual_seq_i.ntt_seq_i = ntt_fwd_seq_i;
        ntt_virtual_seq_i.ntt_seq_i = ntt_inv_seq_i;

        // Start the virtual sequence
        ntt_virtual_seq_i.start(null);

        //-- wait for end
        #1400ns ;

        phase.drop_objection(this);
    
    endtask


endclass: ntt_base_test