//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION: ML-KEM-768 encapsulation and decapsulation known-answer test.
// Vectors come from the FIPS 203 reference model, so this pins the hardware
// to the standard instead of to its own round trip. See the sequence header.
//
//----------------------------------------------------------------------

class ML_KEM_768_encaps_decaps_KATs_test extends test_top;

  `uvm_component_utils(ML_KEM_768_encaps_decaps_KATs_test);

  bit disable_scrboard_from_test;
  bit disable_pred_from_test;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    mldsa_bench_sequence_base::type_id::set_type_override(ML_KEM_768_encaps_decaps_KATs_sequence::get_type());
    super.build_phase(phase);

    disable_scrboard_from_test = 1;
    disable_pred_from_test = 1;

    uvm_config_db#(bit)::set(null, "*", "disable_scrboard_from_test", disable_scrboard_from_test);
    uvm_config_db#(bit)::set(null, "*", "disable_pred_from_test", disable_pred_from_test);
  endfunction

  virtual task main_phase(uvm_phase phase);
    ML_KEM_768_encaps_decaps_KATs_sequence seq;
    seq = ML_KEM_768_encaps_decaps_KATs_sequence::type_id::create("ML_KEM_768_encaps_decaps_KATs_sequence");
    seq.start(null);
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
