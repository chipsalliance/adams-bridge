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

class ML_DSA_randomized_all_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_all_sequence);
  

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    
    bit ready;
    bit valid;
    bit [31:0] SIGNATURE[0:1156];
    bit [31:0] PRIVKEY[0:1223];
    bit [31:0] PUBKEY[0:647];
    bit [31:0] MSG_IN[0:15];
    reg_model.reset();
    data = 0;
    ready = 0;
    valid = 0;
    #400;


    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // ---------------------------------------------------------
    //                    KEYGEN TEST
    // ---------------------------------------------------------

    //Wait until ready
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    ready = data[0];

    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Writing MLDSA_SEED register
    foreach (reg_model.MLDSA_SEED[i]) begin
      // Randomize the data before writing
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_SEED data");
      end

      reg_model.MLDSA_SEED[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SEED[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    data = 'h0000_0001; // generate keys
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    //Wait for valid
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    valid = data[1];

    while(!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end

    // Reading MLDSA_PUBKEY register
    for(int i = 0; i < reg_model.MLDSA_PUBKEY.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PUBKEY.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_PUBKEY[%0d]: %0h", i, data), UVM_LOW);
      end
      PUBKEY[i] = data;
    end

    // Reading MLDSA_PRIVKEY_OUT register
    for(int i = 0; i < reg_model.MLDSA_PRIVKEY_OUT.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PRIVKEY_OUT.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PRIVKEY_OUT[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_PRIVKEY_OUT[%0d]: %0h", i, data), UVM_LOW);
      end
      PRIVKEY[i] = data;
    end

    data = 'h0000_0008; // zeroize
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end
    // ---------------------------------------------------------
    //              KEYGEN TEST IS DONE
    // ---------------------------------------------------------

    // ---------------------------------------------------------
    //                    SIGNING TEST
    // ---------------------------------------------------------

    //Wait until ready
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    ready = data[0];

    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Writing MLDSA_MSG register
    foreach (reg_model.MLDSA_MSG[i]) begin
      // Randomize the data before writing
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG data");
      end
      MSG_IN[i] = data;
      reg_model.MLDSA_MSG[i].write(status, MSG_IN[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[%0d] written with %0h", i, MSG_IN[i]), UVM_LOW);
      end
    end

    // Writing MLDSA_SIGN_RND register
    foreach (reg_model.MLDSA_SIGN_RND[i]) begin
      data = 'h0000_0000; // example data
      reg_model.MLDSA_SIGN_RND[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGN_RND[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGN_RND[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    // Writing the PRIVKEY into the MLDSA_PRIVKEY_IN register array
    for (int i = 0; i < reg_model.MLDSA_PRIVKEY_IN.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PRIVKEY_IN.m_mem.write(status, i, PRIVKEY[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PRIVKEY_IN[%0d]", i));
      end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_PRIVKEY_IN[%0d] written with %0h", i, PRIVKEY[i]), UVM_LOW);
      end
    end

    data = 'h0000_0002; // generate singature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    //Wait for valid
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    valid = data[1];

    while(!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end

    // Reading MLDSA_SIGNATURE register
    for(int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d]: %0h", i, data), UVM_LOW);
      end
      SIGNATURE[i] = data;
    end

    data = 'h0000_0008; // zeroize
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    // ---------------------------------------------------------
    //              SIGNING TEST IS DONE
    // ---------------------------------------------------------


    // ---------------------------------------------------------
    //              VERIFYING TEST
    // ---------------------------------------------------------

    //Wait until ready
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    ready = data[0];

    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // Writing MLDSA_MSG register
    foreach (reg_model.MLDSA_MSG[i]) begin
      reg_model.MLDSA_MSG[i].write(status, MSG_IN[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[%0d] written with %0h", i, MSG_IN[i]), UVM_LOW);
      end
    end

    // Writing the PUBKEY into the MLDSA_PUBKEY register array
    for (int i = 0; i < reg_model.MLDSA_PUBKEY.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PUBKEY.m_mem.write(status, i, PUBKEY[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PUBKEY[%0d]", i));
      end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_PUBKEY[%0d] written with %0h", i, PUBKEY[i]), UVM_LOW);
      end
    end

    // Writing the SIGNATURE into the MLDSA_SIGNATURE register array
    for (int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.write(status, i, SIGNATURE[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGNATURE[%0d]", i));
      end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGNATURE[%0d] written with %0h", i, SIGNATURE[i]), UVM_LOW);
      end
    end

    data = 'h0000_0003; // verify singature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    //Wait for valid
    reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
    end else begin
      `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
    end
    valid = data[1];
    while(!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
    end

    // Reading MLDSA_VERIFY_RES register
    foreach (reg_model.MLDSA_VERIFY_RES[i]) begin
      reg_model.MLDSA_VERIFY_RES[i].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_VERIFY_RES[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_VERIFY_RES[%0d]: %0h", i, data), UVM_LOW);
      end
    end

    data = 'h0000_0008; // zeroize
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    // ---------------------------------------------------------
    //              VERIFIACTION TEST IS DONE
    // ---------------------------------------------------------

  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



