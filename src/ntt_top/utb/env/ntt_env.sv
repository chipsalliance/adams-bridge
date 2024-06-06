class ntt_env extends uvm_env;
    `uvm_component_utils(ntt_env)

    ntt_agent           ntt_agent_i;
    // NTT memory
    mem_agent           ntt_mem_i;
    // mem_agent_config    ntt_mem_cfg_i;
    // PWM_a memory
    mem_agent           pwm_a_mem_i;
    // mem_agent_config    pwm_a_mem_cfg_i;
    // PWM_b memory
    mem_agent           pwm_b_mem_i;
    // mem_agent_config    pwm_b_mem_cfg_i;

    ntt_sb              ntt_sb_i;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        ntt_agent_i = ntt_agent::type_id::create(.name("ntt_agent_i"), .parent(this));
        // Mempory agents for NTT, and two operands of PWMs
        ntt_mem_i = mem_agent::type_id::create(.name("ntt_mem_i"), .parent(this));
        // ntt_mem_cfg_i = mem_agent_config::type_id::create("ntt_mem_cfg_i");
        // // Set the desired memory path
        // ntt_mem_cfg_i.set_mem_path("mem_ntt");
        // uvm_config_db#(mem_agent_config)::set(this, "ntt_mem_i", "ntt_mem_cfg_i", ntt_mem_cfg_i);

        pwm_a_mem_i = mem_agent::type_id::create(.name("pwm_a_mem_i"), .parent(this));
        // pwm_a_mem_cfg_i = mem_agent_config::type_id::create("pwm_a_mem_cfg_i");
        // // Set the desired memory path
        // pwm_a_mem_cfg_i.set_mem_path("mem_pwm_a");
        // uvm_config_db#(mem_agent_config)::set(this, "pwm_a_mem_i", "pwm_a_mem_cfg_i", pwm_a_mem_cfg_i);

        pwm_b_mem_i = mem_agent::type_id::create(.name("pwm_b_mem_i"), .parent(this));
        // pwm_b_mem_cfg_i = mem_agent_config::type_id::create("pwm_b_mem_cfg_i");
        // // Set the desired memory path
        // pwm_b_mem_cfg_i.set_mem_path("mem_pwm_b");
        // uvm_config_db#(mem_agent_config)::set(this, "pwm_b_mem_i", "pwm_b_mem_cfg_i", pwm_b_mem_cfg_i);
        
        //Scoreboard
        ntt_sb_i = ntt_sb::type_id::create(.name("ntt_sb_i"), .parent(this));
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        ntt_agent_i.ntt_ap.connect(ntt_sb_i.ntt_ap);

        ntt_mem_i.mem_ap.connect(ntt_sb_i.ntt_mem_ap);
        pwm_a_mem_i.mem_ap.connect(ntt_sb_i.pwm_a_mem_ap);
        pwm_b_mem_i.mem_ap.connect(ntt_sb_i.pwm_b_mem_ap);
    endfunction: connect_phase

endclass: ntt_env