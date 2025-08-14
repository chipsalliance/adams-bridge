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

class ML_DSA_randomized_sign_gen_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_sign_gen_sequence);

  // Members to control randomized failure
  rand int inject_failure;
  rand int fail_coeff;       // coeff in s1/s2
  rand bit [2:0] fail_value; // value to write to the coeff
  bit [(1224*32)-1:0] flat_SK;

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    bit ready;
    bit valid;
    bit error;
    string output_file = "./keygen_input_for_test.hex";
    string input_file = "./keygen_output_for_test.hex";
    int fd;
    string line;
    int value;
    reg_model.reset();
    data = 0;
    ready = 0;
    valid = 0;
    error = 0;
    #400;

    if (!randomize(inject_failure) with {
      inject_failure inside {[0:1]}; // 0 - no failure, 1 - inject failure
      (inject_failure == 1) dist {1 := 5, 0 := 95};
    }) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize inject_failure parameter");
    end else begin
      `uvm_info("RANDOMIZE", $sformatf("Inject failure: %0d", inject_failure), UVM_LOW);
    end

    if (inject_failure == 1) begin
      // Randomize the failure parameters
      if (!randomize(fail_coeff, fail_value) with {
          fail_coeff inside {[0:3839]};     // Bit position (0 to 31)
          fail_value inside {[5:7]};      // 5-7 are illegal values, triggers an error
      }) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize failure parameters");
      end
      else begin
        `uvm_info("RANDOMIZE", $sformatf("Injecting failure with coeff: %0d, value: %0d", fail_coeff, fail_value), UVM_LOW);
      end
    end

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end
    // ---------------------------------------------------------
    //                    SIGNING TEST
    // ---------------------------------------------------------



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
//=========================================================

    // Open the file for writing
    fd = $fopen(output_file, "w");
    if (fd == 0) begin
        $display("ERROR: Failed to open file: %s", output_file);
        return;
    end
    // Generate a random SEED array
    foreach (SEED[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED data");
      end
      SEED[i] = data;
    end
    // Write the KeyGen command and the SEED array to the file
    $fwrite(fd, "%02X\n", 0); // KeyGen command
    write_file(fd, 32/4, SEED); // Write 32-byte SEED to the file
    $fclose(fd);
    // Execute the key generation process
    $system("./test_dilithium5 keygen_input_for_test.hex keygen_output_for_test.hex");

    // Open the generated file for reading
    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    // Skip the two lines (KeyGen command and PK in output)
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    read_line(fd, 648, PK); // Read 2592-byte Public Key to the file
    // Read the secret key (SK) from the file into the SK array
    read_line(fd, 1224, SK);
    $fclose(fd);

    if (inject_failure == 1) begin
      // Flatten SK
      for (int i = 0; i < 1224; i++)
          flat_SK[i*32 +: 32] = SK[i];

      // Overwrite the coeff with the fail_value
      // S1 starts at bit 1024
      flat_SK[1024 + (fail_coeff*3) +: 3] = fail_value;

      // Repack into SK
      for (int i = 0; i < 1224; i++)
          SK[i] = flat_SK[i*32 +: 32];
    end


    // Writing the SK into the MLDSA_PRIVKEY_IN register array
    for (int i = 0; i < reg_model.MLDSA_PRIVKEY_IN.m_mem.get_size(); i++) begin
        reg_model.MLDSA_PRIVKEY_IN.m_mem.write(status, i, SK[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
            `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PRIVKEY_IN[%0d]", i));
        end else begin
            `uvm_info("REG_WRITE", $sformatf("MLDSA_PRIVKEY_IN[%0d] written with %0h", i, SK[i]), UVM_LOW);
        end
    end

//=========================================================


    data = 'h0000_0002; // generate singature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    while(!valid & !error) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      valid = data[1];
      error = data[3];
    end

    if (valid) begin
      // Reading MLDSA_SIGNATURE register
      for(int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
        reg_model.MLDSA_SIGNATURE.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
        end else begin
          `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d]: %0h", i, data), UVM_LOW);
        end
      end
    end

    if (error & !inject_failure) begin
      `uvm_error("SIGNING_ERROR", "MLDSA signing failed unexpectedly");
    end else if (valid & inject_failure) begin
      `uvm_error ("SIGNING_ERROR", "MLDSA signing succeeded unexpectedly despite injected failure");
    end else if (error & inject_failure) begin
      `uvm_info("SIGNING_ERROR", "MLDSA signing failed as expected due to injected failure", UVM_LOW);
    end else begin //valid & !inject_failure
      `uvm_info("SIGNING_SUCCESS", "MLDSA signing completed successfully", UVM_LOW);
    end

    
    // ---------------------------------------------------------
    //              SIGNING TEST IS DONE
    // ---------------------------------------------------------

  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



