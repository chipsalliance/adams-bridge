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

class ML_KEM_keygen_decaps_self_check_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_KEM_keygen_decaps_self_check_sequence);

    
  // Variable arrays
  bit [31:0] seed_d [];
  bit [31:0] seed_z [];
  bit [31:0] ek [];
  bit [31:0] dk [];
  bit [31:0] msg [];
  bit [31:0] ciphertext [];
  bit [31:0] shared_key [];
  bit ready;
  bit valid;
  int value;
  
  function new(string name = "");
    super.new(name);
    seed_d = new[8];
    seed_z = new[8];
    ek = new[392];
    dk = new[792];
    msg = new[8];
    ciphertext = new[392];
    shared_key = new[8];
  endfunction

  virtual task body();
    reg_model.reset();
    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // Generate a random SEED array
    foreach (seed_d[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED_D data");
      end
      seed_d[i] = data;
    end
    // Generate a random SEED array
    foreach (seed_z[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED_Z data");
      end
      seed_z[i] = data;
    end
    // Generate a random MSG array
    foreach (msg[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MSG data");
      end
      msg[i] = data;
    end

    // Running KEYGEN

    // Wait for ready flag in MLKEM_STATUS
    ready = 0;
    while (!ready) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ_FAIL", "Failed to read MLKEM_STATUS");
      end else begin
        `uvm_info("REG_READ_PASS", $sformatf("MLKEM_STATUS: %h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Write SEED to ML_KEM_SEED_D registers
    foreach (reg_model.MLKEM_SEED_D[j]) begin
      reg_model.MLKEM_SEED_D[j].write(status, seed_d[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_SEED_D[%0d] ", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_SEED_D[%0d]: %h", j, seed_d[j]), UVM_LOW);
      end
    end

    // Write SEED to ML_KEM_SEED_Z registers
    foreach (reg_model.MLKEM_SEED_Z[j]) begin
      reg_model.MLKEM_SEED_Z[j].write(status, seed_z[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_SEED_Z[%0d] ", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_SEED_Z[%0d]: %h", j, seed_z[j]), UVM_LOW);
      end
    end

    // Trigger KeyGen operation
    data = 'h00000001; // KeyGen command
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE_FAIL", "Failed to write MLKEM_CTRL to trigger KeyGen");
    end else begin
      `uvm_info("REG_WRITE_PASS", "Successfully wrote MLKEM_CTRL to trigger KeyGen", UVM_LOW);
    end

    // Wait for ready flag in MLKEM_STATUS
    valid = 0;
    while(!valid) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end
    
    // Reading MLKEM_ENCAPS_KEY register
    for(int i = 0; i < reg_model.MLKEM_ENCAPS_KEY.m_mem.get_size(); i++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_ENCAPS_KEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_ENCAPS_KEY[%0d]: %0h", i, data), UVM_LOW);
        ek[i] = data;
      end
    end

    // Reading MLKEM_DECAPS_KEY register
    for(int i = 0; i < reg_model.MLKEM_DECAPS_KEY.m_mem.get_size(); i++) begin
      reg_model.MLKEM_DECAPS_KEY.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_DECAPS_KEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_DECAPS_KEY[%0d]: %0h", i, data), UVM_LOW);
        dk[i] = data;
      end
    end

    data = 'h0000_0008; // Perform zeorization operation
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLKEM_CTRL written with %0h and zeroized", data), UVM_LOW);
    end

    //Run ENCAPS

    // Wait for ready flag in MLKEM_STATUS
    ready = 0;
    while (!ready) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ_FAIL", "Failed to read MLKEM_STATUS");
      end else begin
        `uvm_info("REG_READ_PASS", $sformatf("MLKEM_STATUS: %h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Write MLKEM_ENCAPS_KEY
    for(int j = 0; j < reg_model.MLKEM_ENCAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.write(status, j, ek[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_ENCAPS_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_ENCAPS_KEY[%0d]: %0h", j, ek[j]), UVM_LOW);
      end
    end

    // Write MLKEM_MSG
    for(int j = 0; j < reg_model.MLKEM_MSG.m_mem.get_size(); j++) begin
      reg_model.MLKEM_MSG.m_mem.write(status, j, msg[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_MSG[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_MSG[%0d]: %0h", j, msg[j]), UVM_LOW);
      end
    end

    // Trigger Encaps operation
    data = 'h00000002; // Encaps command
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE_FAIL", "Failed to write MLKEM_CTRL to trigger Encaps");
    end else begin
      `uvm_info("REG_WRITE_PASS", "Successfully wrote MLKEM_CTRL to trigger Encaps", UVM_LOW);
    end

    // Wait for ready flag in MLKEM_STATUS
    valid =0;
    while(!valid) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end
    
    // Reading MLKEM_SHARED_KEY register
    foreach (reg_model.MLKEM_SHARED_KEY[j]) begin
      reg_model.MLKEM_SHARED_KEY[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_SHARED_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_SHARED_KEY[%0d]: %0h", j, data), UVM_LOW);
        shared_key[j] = data;
      end
    end

    // Reading MLKEM_CIPHERTEXT register
    for(int j = 0; j < reg_model.MLKEM_CIPHERTEXT.m_mem.get_size(); j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_CIPHERTEXT[%0d]", j));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_CIPHERTEXT[%0d]: %0h", j, data), UVM_LOW);
        ciphertext[j] = data;
      end
    end

    data = 'h0000_0008; // Perform zeorization operation
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLKEM_CTRL written with %0h and zeroized", data), UVM_LOW);
    end

    // Run KEYGEN/DECAPS combined flow

    // Wait for ready flag in MLKEM_STATUS
    ready = 0;
    while (!ready) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ_FAIL", "Failed to read MLKEM_STATUS");
      end else begin
        `uvm_info("REG_READ_PASS", $sformatf("MLKEM_STATUS: %h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Write SEED to MLKEM_SEED_D registers
    foreach (reg_model.MLKEM_SEED_D[j]) begin
      reg_model.MLKEM_SEED_D[j].write(status, seed_d[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_SEED_D[%0d] ", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_SEED_D[%0d]: %h", j, seed_d[j]), UVM_LOW);
      end
    end

    // Write SEED to MLKEM_SEED_Z registers
    foreach (reg_model.MLKEM_SEED_Z[j]) begin
      reg_model.MLKEM_SEED_Z[j].write(status, seed_z[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_SEED_Z[%0d] ", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_SEED_Z[%0d]: %h", j, seed_z[j]), UVM_LOW);
      end
    end

    // Write MLKEM_CIPHERTEXT
    for(int j = 0; j < reg_model.MLKEM_CIPHERTEXT.m_mem.get_size(); j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.write(status, j, ciphertext[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_CIPHERTEXT[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_CIPHERTEXT[%0d]: %0h", j, ciphertext[j]), UVM_LOW);
      end
    end

    // Trigger Decaps operation
    data = 'h00000004; // Keygen/Decaps command
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE_FAIL", "Failed to write MLKEM_CTRL to trigger Keygen/Decaps");
    end else begin
      `uvm_info("REG_WRITE_PASS", "Successfully wrote MLKEM_CTRL to trigger Keygen/Decaps", UVM_LOW);
    end

    // Wait for ready flag in MLKEM_STATUS
    valid =0;
    while(!valid) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end
    
    // Reading MLKEM_SHARED_KEY register
    foreach (reg_model.MLKEM_SHARED_KEY[j]) begin
      reg_model.MLKEM_SHARED_KEY[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_SHARED_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_SHARED_KEY[%0d]: %0h", j, data), UVM_LOW);
      end

      if (data !== shared_key[j]) begin
        `uvm_error("VALIDATION_FAIL", $sformatf("SHARED KEY mismatch at index %0d: Expected %h, Got %h", j, shared_key[j], data));
      end else begin
        `uvm_info("VALIDATION_PASS", $sformatf("SHARED KEY match at index %0d: %h", j, data), UVM_LOW);
      end
    end
    
    data = 'h0000_0008; // Perform zeorization operation
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLKEM_CTRL written with %0h and zeroized", data), UVM_LOW);
    end

endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end