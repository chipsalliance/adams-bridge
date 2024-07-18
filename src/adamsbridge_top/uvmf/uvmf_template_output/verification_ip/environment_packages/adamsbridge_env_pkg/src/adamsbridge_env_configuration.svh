//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: THis is the configuration for the adamsbridge environment.
//  it contains configuration classes for each agent.  It also contains
//  environment level configuration variables.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class adamsbridge_env_configuration 
extends uvmf_environment_configuration_base;

  `uvm_object_utils( adamsbridge_env_configuration )


//Constraints for the configuration variables:

// Instantiate the register model
  adamsbridge_reg_model_top  adamsbridge_rm;

  covergroup adamsbridge_configuration_cg;
    // pragma uvmf custom covergroup begin
    option.auto_bin_max=1024;
    // pragma uvmf custom covergroup end
  endgroup




    qvip_ahb_lite_slave_env_configuration     qvip_ahb_lite_slave_subenv_config;
    string                                   qvip_ahb_lite_slave_subenv_interface_names[];
    uvmf_active_passive_t                    qvip_ahb_lite_slave_subenv_interface_activity[];

  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(adamsbridge_env_configuration)) adamsbridge_vsqr_t;
  adamsbridge_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end

// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
// This function constructs the configuration object for each agent in the environment.
//
  function new( string name = "" );
    super.new( name );
    qvip_ahb_lite_slave_subenv_config = qvip_ahb_lite_slave_env_configuration::type_id::create("qvip_ahb_lite_slave_subenv_config");

    adamsbridge_configuration_cg=new;
    `uvm_warning("COVERAGE_MODEL_REVIEW", "A covergroup has been constructed which may need review because of either generation or re-generation with merging.  Please note that configuration variables added as a result of re-generation and merging are not automatically added to the covergroup.  Remove this warning after the covergroup has been reviewed.")

  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

// ****************************************************************************
// FUNCTION : set_vsqr()
// This function is used to assign the vsqr handle.
  virtual function void set_vsqr( adamsbridge_vsqr_t vsqr);
     this.vsqr = vsqr;
  endfunction : set_vsqr

// ****************************************************************************
// FUNCTION: post_randomize()
// This function is automatically called after the randomize() function 
// is executed.
//
  function void post_randomize();
    super.post_randomize();
    // pragma uvmf custom post_randomize begin
    // pragma uvmf custom post_randomize end
  endfunction
  
// ****************************************************************************
// FUNCTION: convert2string()
// This function converts all variables in this class to a single string for
// logfile reporting. This function concatenates the convert2string result for
// each agent configuration in this configuration class.
//
  virtual function string convert2string();
    // pragma uvmf custom convert2string begin
    return {
     


     "\n", qvip_ahb_lite_slave_subenv_config.convert2string
       };
    // pragma uvmf custom convert2string end
  endfunction
// ****************************************************************************
// FUNCTION: initialize();
// This function configures each interface agents configuration class.  The 
// sim level determines the active/passive state of the agent.  The environment_path
// identifies the hierarchy down to and including the instantiation name of the
// environment for this configuration class.  Each instance of the environment 
// has its own configuration class.  The string interface names are used by 
// the agent configurations to identify the virtual interface handle to pull from
// the uvm_config_db.  
//
  function void initialize(uvmf_sim_level_t sim_level, 
                                      string environment_path,
                                      string interface_names[],
                                      uvm_reg_block register_model = null,
                                      uvmf_active_passive_t interface_activity[] = {}
                                     );

    super.initialize(sim_level, environment_path, interface_names, register_model, interface_activity);


  // Interface initialization for QVIP sub-environments
    qvip_ahb_lite_slave_subenv_interface_names    = new[1];
    qvip_ahb_lite_slave_subenv_interface_activity = new[1];

    qvip_ahb_lite_slave_subenv_interface_names     = interface_names[0:0];
    qvip_ahb_lite_slave_subenv_interface_activity  = interface_activity[0:0];



    // pragma uvmf custom reg_model_config_initialize begin
    // Register model creation and configuation
    if (register_model == null) begin
      uvm_reg::include_coverage("*", UVM_CVR_ALL); // Register coverage config with resource DB, used later by build_coverage()
      adamsbridge_rm = adamsbridge_reg_model_top::type_id::create("adamsbridge_rm");
      adamsbridge_rm.build();
      // adamsbridge_rm.adamsbridge_uvm_rmlock_model();
      adamsbridge_rm.lock_model();

      // Check if the model is locked and provide an info message
      if (adamsbridge_rm.is_locked()) begin
        `uvm_info("LOCK_MODEL", "Register model adamsbridge_rm is successfully locked.", UVM_LOW)
      end else begin
          `uvm_error("LOCK_MODEL", "Register model adamsbridge_rm failed to lock.")
      end
      // Check if the model is locked and provide an info message
      // if (adamsbridge_rm.adamsbridge_uvm_rm.is_locked()) begin
      //   `uvm_info("LOCK_MODEL", "Register model adamsbridge_uvm_rm is successfully locked.", UVM_LOW)
      // end else begin
      //     `uvm_error("LOCK_MODEL", "Register model adamsbridge_uvm_rm failed to lock.")
      // end


      // adamsbridge_rm.build_ext_maps();
      enable_reg_adaptation = 1;
      enable_reg_prediction = 1;
    end else begin
      $cast(adamsbridge_rm,register_model);
      enable_reg_prediction = 1;
    end
    // pragma uvmf custom reg_model_config_initialize end


     qvip_ahb_lite_slave_subenv_config.initialize( sim_level, {environment_path,".qvip_ahb_lite_slave_subenv"}, qvip_ahb_lite_slave_subenv_interface_names, adamsbridge_rm,   qvip_ahb_lite_slave_subenv_interface_activity);


  // pragma uvmf custom initialize begin
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.slave = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.master = 1'b1;
     qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.agent_cfg.en_cvg.response = 1'b1;

    // Add analysis ports to send Bus traffic to the scoreboard, so that the predictor/scoreboard can check read transfer data
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_sb" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                     ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                     ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                     ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
    // Add analysis ports to send Bus traffic to the coverage subscriber
    void'(qvip_ahb_lite_slave_subenv_config.ahb_lite_slave_0_cfg.set_monitor_item( "burst_transfer_cov" , ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                                                                                                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                                                                                                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                                                                                                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH)::type_id::get() ));
  // pragma uvmf custom initialize end

  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

