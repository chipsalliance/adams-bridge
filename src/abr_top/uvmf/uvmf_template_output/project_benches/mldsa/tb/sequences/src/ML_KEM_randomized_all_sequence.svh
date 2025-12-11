//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//                                          
// DESCRIPTION: Top level sequence that does random ML-KEM operations
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class ML_KEM_randomized_all_sequence extends ML_KEM_base_sequence;

  rand bit decaps_rej;
  rand bit [1:0] op;
  rand bit on_the_fly_zeroize;
  rand int rand_delay;

  constraint decaps_rej_c {
    decaps_rej dist {1 := 1, 0 := 99}; // 1% chance of rejection
  };

  constraint on_the_fly_zeroize_c {
    on_the_fly_zeroize dist {1 := 10, 0 := 90};  // 1% chance of reset per op
  }

  `uvm_object_utils(ML_KEM_randomized_all_sequence);

  function new(string name = "");
    super.new(name);
  endfunction

  task keygen(bit on_the_fly_zeroize = 0);
    run_model_for_keygen_with_rand_val(on_the_fly_zeroize);
    wait_for_done(0, "ready");
    write_z_and_d_sed();
    wait_for_done(0, "ready");
    run_operation(32'h1, "KeyGen Operation");
    maybe_reset_mid_op(on_the_fly_zeroize);
    if (on_the_fly_zeroize) begin
      wait_for_done(0, "ready");
    end else begin
      wait_for_done(1, "valid");
    end
    read_ek();
    read_dk();
    compare_keygen_vectors(on_the_fly_zeroize);
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task encap(bit on_the_fly_zeroize = 0);
    run_model_for_encap_with_rand_val(on_the_fly_zeroize);
    wait_for_done(0, "ready");
    write_msg();
    write_ek();
    wait_for_done(0, "ready");
    run_operation(32'h2, "Encap Operation");
    maybe_reset_mid_op(on_the_fly_zeroize);
    if (on_the_fly_zeroize) begin
      wait_for_done(0, "ready");
    end else begin
      wait_for_done(1, "valid");
    end
    read_ciphertext();
    read_shared_key();
    compare_encap_vectors(on_the_fly_zeroize);
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task decap(bit decaps_rej = 0, bit on_the_fly_zeroize = 0);
    run_model_for_decap_with_rand_val(decaps_rej, on_the_fly_zeroize);
    wait_for_done(0, "ready");
    write_dk();
    write_ciphertext();
    wait_for_done(0, "ready");
    run_operation(32'h3, "decap Operation");
    maybe_reset_mid_op(on_the_fly_zeroize);
    if (on_the_fly_zeroize) begin
      wait_for_done(0, "ready");
    end else begin
      wait_for_done(1, "valid");
    end
    read_shared_key();
    compare_decap_vectors(on_the_fly_zeroize);
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task keygen_decap(bit decaps_rej = 0, bit on_the_fly_zeroize = 0);
    run_model_for_decap_with_rand_val(decaps_rej, on_the_fly_zeroize);
    wait_for_done(0, "ready");
    write_z_and_d_sed();
    write_ciphertext();
    wait_for_done(0, "ready");
    run_operation(32'h4, "keygen decap Operation");
    maybe_reset_mid_op(on_the_fly_zeroize);
    if (on_the_fly_zeroize) begin
      wait_for_done(0, "ready");
    end else begin
      wait_for_done(1, "valid");
    end
    read_shared_key();
    compare_decap_vectors(on_the_fly_zeroize);
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task maybe_reset_mid_op(string from = "");
    if (on_the_fly_zeroize) begin
      if (!this.randomize(rand_delay) with { rand_delay >= 0 && rand_delay < 10000; }) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize delay");
      end
      `uvm_info("RND_GEN", $sformatf("randomize delay: %0d", rand_delay), UVM_LOW);
      
      #(rand_delay);
      `uvm_info("ZEROIZE", $sformatf("Triggering on-the-fly **zeroize**"), UVM_LOW);
      zeroize();
    end
  endtask

  virtual task body();
    reg_model.reset();
    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // Randomly choose an operation to perform
    for (int i = 0; i < 10; i++) begin
      if (!this.randomize()) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize sequence");
      end

      `uvm_info("RANDOM_OP", $sformatf("Random operation chosen: %0d, decaps_rej: %0d, on_the_fly_zeroize: %0d:", op, decaps_rej, on_the_fly_zeroize), UVM_LOW);
      
      unique case (op)
        2'b00: keygen(on_the_fly_zeroize);
        2'b01: encap(on_the_fly_zeroize);
        2'b10: decap(decaps_rej, on_the_fly_zeroize);
        2'b11: keygen_decap(decaps_rej, on_the_fly_zeroize);
        default: begin
          `uvm_fatal("INVALID_OP", "Invalid operation selected");
        end
      endcase
    end

    `uvm_info("Randomized Flows", $sformatf("ML-KEM Random validation completed"), UVM_LOW);

  endtask  

  endclass




// pragma uvmf custom external begin
// pragma uvmf custom external end



