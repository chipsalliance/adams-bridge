//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
// DESCRIPTION: Randomized algorithm and parameter set switching test.
//   Issues one reset and then runs three back to back self checking units at
//   randomly chosen (algorithm, parameter set) pairs - ML-DSA-44/65/87 and
//   ML-KEM-512/768/1024 - without resetting again, so every parameter set
//   change has to be absorbed by the command time PARAM_SET latch alone.
//   Consecutive units never repeat the same pair. Intended for the nightly
//   randomized regression, one seed per iteration; +ABR_PS_MIX_UNITS=<n>
//   lengthens the chain for a soak.
//----------------------------------------------------------------------

class ML_DSA_MLKEM_param_set_mix_test extends test_top;

  `uvm_component_utils(ML_DSA_MLKEM_param_set_mix_test);

  bit disable_scrboard_from_test;
  bit disable_pred_from_test;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    mldsa_bench_sequence_base::type_id::set_type_override(ML_DSA_MLKEM_param_set_mix_sequence::get_type());
    super.build_phase(phase);

    disable_scrboard_from_test = 1;
    disable_pred_from_test = 1;

    uvm_config_db#(bit)::set(null, "*", "disable_scrboard_from_test", disable_scrboard_from_test);
    uvm_config_db#(bit)::set(null, "*", "disable_pred_from_test", disable_pred_from_test);

  endfunction

  virtual task main_phase(uvm_phase phase);
    ML_DSA_MLKEM_param_set_mix_sequence seq;
    seq = ML_DSA_MLKEM_param_set_mix_sequence::type_id::create("seq");
    seq.start(null);
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
