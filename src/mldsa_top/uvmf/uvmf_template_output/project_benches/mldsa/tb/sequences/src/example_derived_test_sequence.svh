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

class example_derived_test_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(example_derived_test_sequence);

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    bit [31:0] data;
    bit ready;
    bit valid;
    bit [7:0][31:0] seed;
    reg_model.reset();
    data =0;
    ready =0;
    valid =0;
    seed[0] = 32'h38359FBC;
    seed[1] = 32'hD79582CF;
    seed[2] = 32'hFE609E13;
    seed[3] = 32'h7EE2EFE8;
    seed[4] = 32'hA8DBCBAD;
    seed[5] = 32'h18BA92BB;
    seed[6] = 32'h433AB4F0;
    seed[7] = 32'h9B49299D;
    #400;


    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // ---------------------------------------------------------
    //                    KEYGEN TEST
    // ---------------------------------------------------------

    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
      end
      ready = data[0];
    end

    // Writing MLDSA_SEED register
    foreach (reg_model.MLDSA_SEED[i]) begin
      data = seed[i]; // example data
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

    while(!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
      end
      valid = data[1];
    end

    // Reading MLDSA_PUBKEY register
    foreach (reg_model.MLDSA_PUBKEY[i]) begin
      reg_model.MLDSA_PUBKEY[i].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_PUBKEY[%0d]: %0h", i, data), UVM_LOW);
      end
    end

    // Reading MLDSA_PRIVKEY_OUT register
    //foreach (reg_model.MLDSA_PRIVKEY_OUT[i]) begin
    //  reg_model.MLDSA_PRIVKEY_OUT[i].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    //  if (status != UVM_IS_OK) begin
    //    `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PRIVKEY_OUT[%0d]", i));
    //  end else begin
    //    `uvm_info("REG_READ", $sformatf("MLDSA_PRIVKEY_OUT[%0d]: %0h", i, data), UVM_LOW);
    //  end
    //end
    // ---------------------------------------------------------
    //              KEYGEN TEST IS DONE
    // ---------------------------------------------------------
/*
    // ---------------------------------------------------------
    //                    SIGNING TEST
    // ---------------------------------------------------------

    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
      end
      ready = data[0];
    end

    // Writing MLDSA_MSG register
    foreach (reg_model.MLDSA_MSG[i]) begin
      data = 'h1122_3344; // example data
      reg_model.MLDSA_MSG[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[%0d] written with %0h", i, data), UVM_LOW);
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

    // Writing MLDSA_PRIVKEY_IN register
    for(int i = 0; i < reg_model.MLDSA_PRIVKEY_IN.m_mem.get_size(); i++) begin
      data = 'h0000_0000; // example data
      reg_model.MLDSA_PRIVKEY_IN.m_mem.write(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PRIVKEY_IN[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_PRIVKEY_IN[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    data = 'h0000_0002; // generate singature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    while(!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_LOW);
      end
      valid = data[1];
    end

    // Reading MLDSA_SIGNATURE register
    foreach (reg_model.MLDSA_SIGNATURE[i]) begin
      reg_model.MLDSA_SIGNATURE[i].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d]: %0h", i, data), UVM_LOW);
      end
    end

    // ---------------------------------------------------------
    //              SIGNING TEST IS DONE
    // ---------------------------------------------------------
*/
    // ---------------------------------------------------------
    //                VERIFIACTION TEST
    // ---------------------------------------------------------
/*
    // Writing MLDSA_SIGNATURE register
    foreach (reg_model.MLDSA_SIGNATURE[i]) begin
      data = 'h1122_3344; // example data
      reg_model.MLDSA_SIGNATURE[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGNATURE[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    // Writing MLDSA_PRIVKEY_IN register
    foreach (reg_model.MLDSA_PUBKEY[i]) begin
      data = 'h1122_3344; // example data
      reg_model.MLDSA_PUBKEY[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_PUBKEY[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    data = 'h0000_0003; // generate singature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
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
    // ---------------------------------------------------------
    //              VERIFIACTION TEST IS DONE
    // ---------------------------------------------------------
*/

  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



