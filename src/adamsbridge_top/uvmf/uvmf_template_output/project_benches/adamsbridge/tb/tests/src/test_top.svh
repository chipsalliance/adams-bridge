//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
// Description: This top level UVM test is the base class for all
//     future tests created for this project.
//
//     This test class contains:
//          Configuration:  The top level configuration for the project.
//          Environment:    The top level environment for the project.
//          Top_level_sequence:  The top level sequence for the project.
//                                        
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

typedef adamsbridge_env_configuration adamsbridge_env_configuration_t;
typedef adamsbridge_environment adamsbridge_environment_t;

class test_top extends uvmf_test_base #(.CONFIG_T(adamsbridge_env_configuration_t), 
                                        .ENV_T(adamsbridge_environment_t), 
                                        .TOP_LEVEL_SEQ_T(adamsbridge_bench_sequence_base));

  `uvm_component_utils( test_top );

// This message handler can be used to redirect QVIP Memeory Model messages through
// the UVM messaging mecahanism.  How to enable and use it is described in 
//      $UVMF_HOME/common/utility_packages/qvip_utils_pkg/src/qvip_report_catcher.svh
qvip_memory_message_handler message_handler;


  string interface_names[] = {
    uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0 /* ahb_lite_slave_0     [0] */ 
};

uvmf_active_passive_t interface_activities[] = { 
    ACTIVE /* ahb_lite_slave_0     [0] */   };

  // pragma uvmf custom class_item_additional begin
    string command;
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  // FUNCTION: new()
  // This is the standard systemVerilog constructor.  All components are 
  // constructed in the build_phase to allow factory overriding.
  //
  function new( string name = "", uvm_component parent = null );
     super.new( name ,parent );
  endfunction



  // ****************************************************************************
  // FUNCTION: build_phase()
  // The construction of the configuration and environment classes is done in
  // the build_phase of uvmf_test_base.  Once the configuraton and environment
  // classes are built then the initialize call is made to perform the
  // following: 
  //     Monitor and driver BFM virtual interface handle passing into agents
  //     Set the active/passive state for each agent
  // Once this build_phase completes, the build_phase of the environment is
  // executed which builds the agents.
  //
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    // pragma uvmf custom configuration_settings_post_randomize begin
    
    // Initialize the command with a default value
    command = "test_dilithium5";

    // Check for the command line argument and update the command string
    if ($test$plusargs("DILITHIUM_COMMAND")) begin
      string arg_value;
      if ($value$plusargs("DILITHIUM_COMMAND=%s", arg_value)) begin
        command = arg_value;
      end
    end

    `uvm_info("TEST_TOP", $sformatf("DILITHIUM_COMMAND set to: %s", command), UVM_LOW)

    // Set the configuration parameter for the environment using wildcard
    uvm_config_db#(string)::set(null, "*", "dilithium_command", command);

    // pragma uvmf custom configuration_settings_post_randomize end
    configuration.initialize(NA, "uvm_test_top.environment", interface_names, null, interface_activities);
    
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

