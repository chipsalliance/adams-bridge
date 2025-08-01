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

class ML_KEM_overwrite_sequence extends ML_KEM_base_sequence;

  rand bit [1:0] op, overwrite_op;
  rand int rand_delay;


  `uvm_object_utils(ML_KEM_overwrite_sequence);

  function new(string name = "");
    super.new(name);
  endfunction

  task keygen(bit on_the_fly_reset = 0);
    run_model_for_keygen_with_rand_val(on_the_fly_reset);
    wait_for_done(0, "ready");
    write_z_and_d_sed();
    wait_for_done(0, "ready");
    run_operation(32'h1, "KeyGen Operation");
    overwrite_cmd();
    overwrite_cmd();
    wait_for_done(1, "valid");
    read_ek();
    read_dk();
    compare_keygen_vectors();
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task encap();
    run_model_for_encap_with_rand_val();
    wait_for_done(0, "ready");
    write_msg();
    write_ek();
    wait_for_done(0, "ready");
    run_operation(32'h2, "Encap Operation");
    overwrite_cmd();
    overwrite_cmd();
    wait_for_done(1, "valid");
    read_ciphertext();
    read_shared_key();
    compare_encap_vectors();
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task decap(bit decaps_rej = 0);
    run_model_for_decap_with_rand_val(decaps_rej);
    wait_for_done(0, "ready");
    write_dk();
    write_ciphertext();
    wait_for_done(0, "ready");
    run_operation(32'h3, "decap Operation");
    overwrite_cmd();
    overwrite_cmd();
    wait_for_done(1, "valid");
    read_shared_key();
    compare_decap_vectors();
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task keygen_decap(bit decaps_rej = 0);
    run_model_for_decap_with_rand_val(decaps_rej);
    wait_for_done(0, "ready");
    write_z_and_d_sed();
    write_ciphertext();
    wait_for_done(0, "ready");
    run_operation(32'h4, "keygen decap Operation");
    overwrite_cmd();
    overwrite_cmd();
    wait_for_done(1, "valid");
    read_shared_key();
    compare_decap_vectors();
    zeroize();
    wait_for_done(0, "ready");
  endtask

  task overwrite_cmd();
    if (!this.randomize(rand_delay) with { rand_delay >= 0 && rand_delay < 10000; }) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize delay");
    end
    `uvm_info("RND_GEN", $sformatf("randomize delay: %0d", rand_delay), UVM_LOW);
    #(rand_delay);

    if (!this.randomize(overwrite_op) with { overwrite_op >= 0 && overwrite_op < 4; }) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize overwrite_op");
    end
    `uvm_info("RND_GEN", $sformatf("overwrite_op: %0d", overwrite_op), UVM_LOW);
    
    unique case (overwrite_op)
        2'b00: run_operation(32'h1, "KeyGen Operation");
        2'b01: run_operation(32'h3, "Encap Operation");
        2'b10: run_operation(32'h3, "decap Operation");
        2'b11: run_operation(32'h4, "keygen decap Operation");
        default: begin
          `uvm_fatal("INVALID_OP", "Invalid operation selected");
        end
    endcase
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

      `uvm_info("RANDOM_OP", $sformatf("Random operation chosen: %0d", op), UVM_LOW);
      
      unique case (op)
        2'b00: keygen();
        2'b01: encap();
        2'b10: decap();
        2'b11: keygen_decap();
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



