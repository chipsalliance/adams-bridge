class ntt_combined_test extends uvm_test;

    `uvm_component_utils(ntt_combined_test)

    ntt_env             ntt_env_i;
    mem_init_seq        mem_init_seq_i;
    ntt_fwd_seq         ntt_fwd_seq_i;
    ntt_inv_seq         ntt_inv_seq_i;

    virtual ntt_if ntt_vif;
    virtual mem_if ntt_mem_vif;
    virtual mem_if pwm_a_mem_vif;
    virtual mem_if pwm_b_mem_vif;


    // Shared variable to store ntt_mem_base_addr
    ntt_mem_addr_t shared_ntt_mem_base_addr;

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
        `uvm_info("NTT_COMBINED_TEST", "Running ntt_combined_test", UVM_LOW)
        mem_init_seq_i = mem_init_seq::type_id::create(.name("mem_init_seq_i"));
        ntt_fwd_seq_i = ntt_fwd_seq::type_id::create(.name("ntt_fwd_seq_i"));
        ntt_inv_seq_i = ntt_inv_seq::type_id::create(.name("ntt_inv_seq_i"));

        phase.raise_objection(this);
        
        //-- Wait for DUT reset completion.
        #150ns;

        // Start the memory initialization sequence
        mem_init_seq_i.start(ntt_env_i.ntt_mem_i.mem_sqcr_i);

        // Start the forward NTT sequence
        ntt_fwd_seq_i.start(ntt_env_i.ntt_agent_i.ntt_sqcr_i);
        shared_ntt_mem_base_addr = ntt_fwd_seq_i.ntt_txn_i.ntt_mem_base_addr; // Store the ntt_mem_base_addr

        @ (posedge ntt_vif.ntt_done); // Wait for done signal from the DUT
        #100ns;
        ntt_inv_seq_i.ntt_mem_base_addr = shared_ntt_mem_base_addr; // Pass the shared ntt_mem_base_addr to the inverse sequence
        ntt_inv_seq_i.ntt_mem_base_addr.src_base_addr = shared_ntt_mem_base_addr.dest_base_addr;
        ntt_inv_seq_i.use_shared_addr = 1; // Set the flag to control address assignment
        ntt_inv_seq_i.start(ntt_env_i.ntt_agent_i.ntt_sqcr_i); // Start the inverse sequence

        //-- wait for end
        #1400ns;

        phase.drop_objection(this);
    endtask

endclass: ntt_combined_test