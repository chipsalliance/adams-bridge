//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This environment contains all agents, predictors and
// scoreboards required for the block level design.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class adamsbridge_environment  extends uvmf_environment_base #(
    .CONFIG_T( adamsbridge_env_configuration 
  ));
  `uvm_component_utils( adamsbridge_environment )


  qvip_ahb_lite_slave_environment #()  qvip_ahb_lite_slave_subenv;
  uvm_analysis_port #( mvc_sequence_item_base ) qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap [string];




  typedef adamsbridge_predictor #(
                .CONFIG_T(CONFIG_T)
                )
 adamsbridge_pred_t;
  adamsbridge_pred_t adamsbridge_pred;
  typedef adamsbridge_scoreboard #(
                .CONFIG_T(CONFIG_T)
                )
 adamsbridge_sb_t;
  adamsbridge_sb_t adamsbridge_sb;

  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                                      ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                                      ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                                      ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                                      ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                                      ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_transfer_t;

  typedef reg2ahb_adapter #(ahb_reg_transfer_t,
                            ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                            ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                            ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                            ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                            ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                            ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_adapter_t;


  ahb_reg_adapter_t    ahb_reg_adapter;

  typedef ahb_reg_predictor #(ahb_reg_transfer_t,
                               ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                               ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                               ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                               ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                               ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                               ahb_lite_slave_0_params::AHB_RDATA_WIDTH) ahb_reg_predictor_t;

   ahb_reg_predictor_t    ahb_reg_predictor;



  typedef uvmf_virtual_sequencer_base #(.CONFIG_T(adamsbridge_env_configuration)) adamsbridge_vsqr_t;
  adamsbridge_vsqr_t vsqr;

  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
 
// ****************************************************************************
// FUNCTION : new()
// This function is the standard SystemVerilog constructor.
//
  function new( string name = "", uvm_component parent = null );
    super.new( name, parent );
  endfunction

// ****************************************************************************
// FUNCTION: build_phase()
// This function builds all components within this environment.
//
  virtual function void build_phase(uvm_phase phase);
// pragma uvmf custom build_phase_pre_super begin
// pragma uvmf custom build_phase_pre_super end
    super.build_phase(phase);
    qvip_ahb_lite_slave_subenv = qvip_ahb_lite_slave_environment#()::type_id::create("qvip_ahb_lite_slave_subenv",this);
    qvip_ahb_lite_slave_subenv.set_config(configuration.qvip_ahb_lite_slave_subenv_config);

    adamsbridge_pred = adamsbridge_pred_t::type_id::create("adamsbridge_pred",this);
    adamsbridge_pred.configuration = configuration;

    adamsbridge_sb = adamsbridge_sb_t::type_id::create("adamsbridge_sb",this);
    adamsbridge_sb.configuration = configuration;

  if (configuration.enable_reg_prediction) begin
    ahb_reg_predictor = ahb_reg_predictor_t::type_id::create("ahb_reg_predictor", this);
  end
// pragma uvmf custom reg_model_build_phase end

    vsqr = adamsbridge_vsqr_t::type_id::create("vsqr", this);
    vsqr.set_config(configuration);
    configuration.set_vsqr(vsqr);

    // pragma uvmf custom build_phase begin
    // pragma uvmf custom build_phase end
  endfunction

// ****************************************************************************
// FUNCTION: connect_phase()
// This function makes all connections within this environment.  Connections
// typically inclue agent to predictor, predictor to scoreboard and scoreboard
// to agent.
//
  virtual function void connect_phase(uvm_phase phase);

    super.connect_phase(phase);
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap = qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.ap; 
    
    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer"].connect(adamsbridge_pred.ahb_slave_0_ae);

    qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_ap["burst_transfer_sb"].connect(adamsbridge_sb.actual_ahb_analysis_export);
    adamsbridge_pred.adamsbridge_sb_ahb_ap.connect(adamsbridge_sb.expected_ahb_analysis_export);




    if ( configuration.qvip_ahb_lite_slave_subenv_interface_activity[0] == ACTIVE )
       uvm_config_db #(mvc_sequencer)::set(null,UVMF_SEQUENCERS,configuration.qvip_ahb_lite_slave_subenv_interface_names[0],qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer  );
    
    
    
    
    // pragma uvmf custom reg_model_connect_phase begin
    // Create register model adapter if required
    if (configuration.enable_reg_prediction ||
        configuration.enable_reg_adaptation) begin
      ahb_reg_adapter = ahb_reg_adapter_t::type_id::create("reg2ahb_adapter");
      ahb_reg_adapter.en_n_bits = 1; // This is to allow the adapter to generate addresses
                                      // that are not aligned to 64-bit width (the native AHB interface width)
    end

    if ((configuration.enable_reg_adaptation) && (qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer != null ))
      configuration.adamsbridge_rm.default_map.set_sequencer(qvip_ahb_lite_slave_subenv.ahb_lite_slave_0.m_sequencer, ahb_reg_adapter);
    // Set map and adapter handles within uvm predictor
    if (configuration.enable_reg_prediction) begin
      ahb_reg_predictor.map     = configuration.adamsbridge_rm.default_map;
      ahb_reg_predictor.adapter = ahb_reg_adapter;
      adamsbridge_pred.adamsbridge_ahb_reg_ap.connect(ahb_reg_predictor.bus_item_export);
    end
    // pragma uvmf custom reg_model_connect_phase end
  endfunction

// ****************************************************************************
// FUNCTION: end_of_simulation_phase()
// This function is executed just prior to executing run_phase.  This function
// was added to the environment to sample environment configuration settings
// just before the simulation exits time 0.  The configuration structure is 
// randomized in the build phase before the environment structure is constructed.
// Configuration variables can be customized after randomization in the build_phase
// of the extended test.
// If a sequence modifies values in the configuration structure then the sequence is
// responsible for sampling the covergroup in the configuration if required.
//
  virtual function void start_of_simulation_phase(uvm_phase phase);
     configuration.adamsbridge_configuration_cg.sample();
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

