//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
// DESCRIPTION: ML-DSA-87 randomized keygen + sign + verify self check test.
//   Exercises MLDSA_CTRL.PARAM_SET = 2'b00 on the keygen+sign and verify
//   flows over random seeds and random messages, checking that a signature
//   the hardware produced verifies back and that MLDSA_VERIFY_RES reproduces
//   c~ with a zero tail.
//----------------------------------------------------------------------

class ML_DSA_87_randomized_kg_sign_verify_test extends test_top;

  `uvm_component_utils(ML_DSA_87_randomized_kg_sign_verify_test);

  bit disable_scrboard_from_test;
  bit disable_pred_from_test;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    mldsa_bench_sequence_base::type_id::set_type_override(ML_DSA_87_randomized_kg_sign_verify_sequence::get_type());
    super.build_phase(phase);

    disable_scrboard_from_test = 1;
    disable_pred_from_test = 1;

    uvm_config_db#(bit)::set(null, "*", "disable_scrboard_from_test", disable_scrboard_from_test);
    uvm_config_db#(bit)::set(null, "*", "disable_pred_from_test", disable_pred_from_test);

  endfunction

  virtual task main_phase(uvm_phase phase);
    ML_DSA_87_randomized_kg_sign_verify_sequence seq;
    seq = ML_DSA_87_randomized_kg_sign_verify_sequence::type_id::create("seq");
    seq.start(null);
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
