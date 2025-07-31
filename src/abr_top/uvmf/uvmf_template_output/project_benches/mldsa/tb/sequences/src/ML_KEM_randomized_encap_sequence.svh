//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: This file contains the top level sequence used in  example_derived_test.
// It is an example of a sequence that is extended from %(benchName)_bench_sequence_base
// and can override %(benchName)_bench_sequence_base.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class ML_KEM_randomized_encap_sequence extends ML_KEM_base_sequence;

  `uvm_object_utils(ML_KEM_randomized_encap_sequence);

  

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    reg_model.reset();
    #400;


    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    run_model_for_encap_with_rand_val();
    wait_for_done(0, "ready");
    write_msg();
    write_ek();
    wait_for_done(0, "ready");
    run_operation(32'h2, "Encap Operation");
    wait_for_done(1, "valid");
    read_ciphertext();
    read_shared_key();
    compare_encap_vectors();
    check_mldsa_api();
    zeroize();
    wait_for_done(0, "ready");


    `uvm_info("Randomized Encap", $sformatf("ML-KEM Encapsulation validation completed"), UVM_LOW);


  endtask  


  endclass




// pragma uvmf custom external begin
// pragma uvmf custom external end



