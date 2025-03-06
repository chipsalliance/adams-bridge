//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This test extends test_top and makes 
//    changes to test_top using the UVM factory type_override:
//
//    Test scenario: 
//      This is a template test that can be used to create future tests.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class ML_DSA_randomized_two_verif_on_fail_test extends test_top;

  `uvm_component_utils(ML_DSA_randomized_two_verif_on_fail_test);


  bit expect_verif_pass_after_failure;
  bit expect_predictor_verif_failure;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    // The factory override below is an example of how to replace the mldsa_bench_sequence_base 
    // sequence with the ML_DSA_randomized_two_verif_on_fail_sequence.
    mldsa_bench_sequence_base::type_id::set_type_override(ML_DSA_randomized_two_verif_on_fail_sequence::get_type());
    // Execute the build_phase of test_top AFTER all factory overrides have been created.
    super.build_phase(phase);
    // pragma uvmf custom configuration_settings_post_randomize begin
    // UVMF_CHANGE_ME Test specific configuration values can be set here.

    expect_verif_pass_after_failure = 1;
    expect_predictor_verif_failure = 1;

    uvm_config_db#(bit)::set(null, "*", "expect_verif_pass_after_failure", expect_verif_pass_after_failure);
    uvm_config_db#(bit)::set(null, "*", "expect_predictor_verif_failure", expect_predictor_verif_failure);
    // The configuration structure has already been randomized.
    // pragma uvmf custom configuration_settings_post_randomize end
  endfunction

  virtual task main_phase(uvm_phase phase);
    // Start the ML_DSA_randomized_two_verif_on_fail_sequence
    ML_DSA_randomized_two_verif_on_fail_sequence seq;
    seq = ML_DSA_randomized_two_verif_on_fail_sequence::type_id::create("ML_DSA_randomized_two_verif_on_fail_sequence");
    seq.start(null); // You may need to specify a sequencer if your environment requires it
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end


