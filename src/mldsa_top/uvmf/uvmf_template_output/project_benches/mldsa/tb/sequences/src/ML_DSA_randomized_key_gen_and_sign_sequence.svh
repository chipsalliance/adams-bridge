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

class ML_DSA_randomized_key_gen_and_sign_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_key_gen_and_sign_sequence);
  

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    
    bit ready;
    bit valid;
    string output_file = "./keygen_input_for_test.hex";
    string input_file = "./keygen_output_for_test.hex";
    int fd;
    string line;
    int value;
    reg_model.reset();
    data =0;
    ready =0;
    valid = 0;
    #400;


    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    //PRE test set up

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
    // $system("pwd");
    $system("./test_dilithium5 keygen_input_for_test.hex keygen_output_for_test.hex");

    // Open the generated file for reading
    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    // Skip the two lines (KeyGen command and PK in output)
    void'($fgets(line, fd));
    $sscanf(line, "%02x\n", value);
    read_line(fd, 648, PK); // Read 2592-byte Public Key to the file
    // Read the secret key (SK) from the file into the SK array
    read_line(fd, 1224, SK);
    $fclose(fd);

    // ---------------------------------------------------------
    //                    KEYGEN + SIGNING TEST
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

    // Writing MLDSA_SEED register
    foreach (reg_model.MLDSA_SEED[i]) begin
      reg_model.MLDSA_SEED[i].write(status, SEED[i], UVM_FRONTDOOR, reg_model.default_map, this);
      
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SEED[%0d] written with %0h", i, SEED[i]), UVM_LOW);
      end
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

    data = 'h0000_0004; // Perform signing operation
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
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
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
    //              KEYGEN TEST IS DONE
    // ---------------------------------------------------------


  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



