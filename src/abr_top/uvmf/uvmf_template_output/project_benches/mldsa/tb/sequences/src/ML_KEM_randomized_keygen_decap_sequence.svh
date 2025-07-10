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

class ML_KEM_randomized_keygen_decap_sequence extends ML_KEM_base_sequence;

  `uvm_object_utils(ML_KEM_randomized_keygen_decap_sequence);

  rand bit decaps_rej;

  constraint decaps_rej_c {
    decaps_rej dist {1 := 1, 0 := 99}; // 1% chance of rejection
  };

  function new(string name = "");
    super.new(name);
  endfunction


  virtual task body();
    reg_model.reset();
    #400;
    if (!this.randomize()) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize sequence");
    end

    `uvm_info("DECAPS_REJ", $sformatf("Decaps rej flag set to %0d", decaps_rej), UVM_LOW);

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    run_model_for_decap_with_rand_val(decaps_rej);
    wait_for_done(0, "ready");
    write_z_and_d_sed();
    write_ciphertext();
    wait_for_done(0, "ready");
    run_operation(32'h4, "keygen decap Operation");
    wait_for_done(1, "valid");
    read_shared_key();
    compare_decap_vectors();
    zeroize();
    wait_for_done(0, "ready");


    `uvm_info("Randomized decap", $sformatf("ML-KEM decapsulation validation completed"), UVM_LOW);


  endtask  


  endclass




// pragma uvmf custom external begin
// pragma uvmf custom external end



