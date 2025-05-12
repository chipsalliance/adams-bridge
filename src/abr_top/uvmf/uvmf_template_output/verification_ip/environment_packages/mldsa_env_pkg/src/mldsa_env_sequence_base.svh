//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains environment level sequences that will
//    be reused from block to top level simulations.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
class mldsa_env_sequence_base #( 
      type CONFIG_T
      ) extends uvmf_virtual_sequence_base #(.CONFIG_T(CONFIG_T));


  `uvm_object_param_utils( mldsa_env_sequence_base #(
                           CONFIG_T
                           ) );
  `m_uvm_get_type_name_func(mldsa_env_sequence_base)

  // Handle to the environments register model
// This handle needs to be set before use.
  mldsa_reg_model_top  reg_model;

// This mldsa_env_sequence_base contains a handle to a mldsa_env_configuration object 
// named configuration.  This configuration variable contains a handle to each 
// sequencer within each agent within this environment and any sub-environments.
// The configuration object handle is automatically assigned in the pre_body in the
// base class of this sequence.  The configuration handle is retrieved from the
// virtual sequencer that this sequence is started on.
// Available sequencer handles within the environment configuration:

  // Initiator agent sequencers in mldsa_environment:

  // Responder agent sequencers in mldsa_environment:





  // pragma uvmf custom class_item_additional begin
  // pragma uvmf custom class_item_additional end
  
  function new(string name = "" );
    super.new(name);
  endfunction

  virtual task body();



  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

