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

class ML_DSA_randomized_key_gen_sequence extends adamsbridge_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_key_gen_sequence);
  

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    
    bit ready;
    bit valid;
    reg_model.reset();
    data =0;
    ready =0;
    valid = 0;
    #400;


    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "adamsbridge_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "adamsbridge_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // ---------------------------------------------------------
    //                    KEYGEN TEST
    // ---------------------------------------------------------


    while(!ready) begin
      reg_model.ADAMSBRIDGE_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read ADAMSBRIDGE_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("ADAMSBRIDGE_STATUS: %0h", data), UVM_LOW);
      end
      ready = data[0];
    end

    // Writing ADAMSBRIDGE_SEED register
    foreach (reg_model.ADAMSBRIDGE_SEED[i]) begin
      // Randomize the data before writing
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize ADAMSBRIDGE_SEED data");
      end

      reg_model.ADAMSBRIDGE_SEED[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write ADAMSBRIDGE_SEED[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("ADAMSBRIDGE_SEED[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    data = 'h0000_0001; // generate keys
    reg_model.ADAMSBRIDGE_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write ADAMSBRIDGE_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("ADAMSBRIDGE_CTRL written with %0h", data), UVM_LOW);
    end

    while(!valid) begin
      reg_model.ADAMSBRIDGE_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read ADAMSBRIDGE_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("ADAMSBRIDGE_STATUS: %0h", data), UVM_LOW);
      end
      valid = data[1];
    end

    // Reading ADAMSBRIDGE_PUBKEY register
    foreach (reg_model.ADAMSBRIDGE_PUBKEY[i]) begin
      reg_model.ADAMSBRIDGE_PUBKEY[i].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read ADAMSBRIDGE_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("ADAMSBRIDGE_PUBKEY[%0d]: %0h", i, data), UVM_LOW);
      end
    end

    // Reading ADAMSBRIDGE_PRIVKEY_OUT register
    for(int i = 0; i < reg_model.ADAMSBRIDGE_PRIVKEY_OUT.m_mem.get_size(); i++) begin
      reg_model.ADAMSBRIDGE_PRIVKEY_OUT.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read ADAMSBRIDGE_PRIVKEY_OUT[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("ADAMSBRIDGE_PRIVKEY_OUT[%0d]: %0h", i, data), UVM_LOW);
      end
    end
    // ---------------------------------------------------------
    //              KEYGEN TEST IS DONE
    // ---------------------------------------------------------


  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



