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

class ML_DSA_randomized_verif_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_verif_sequence);

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    bit ready;
    bit valid;
    bit ctx_enable;
    bit stream_msg_mode;
    bit stream_msg_rdy;
    string cmd_line;
    string output_file = "./keygen_input_for_test.hex";
    string input_file = "./keygen_output_for_test.hex";
    int fd;
    string line;
    int value;
    uvm_cmdline_processor clp;
    reg_model.reset();
    data = 0;
    ready = 0;
    valid = 0;
    stream_msg_rdy = 0;
  
    clp = uvm_cmdline_processor::get_inst();
    if ( clp.get_arg_value("+STREAM_MSG=",cmd_line) == 0) begin
      `uvm_info("CMD_LINE", "STREAM_MSG option not set, randomizing it", UVM_LOW);
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize STREAM_MSG mode");
      end
      stream_msg_mode = 0;//data[0];
    end else begin
      if (cmd_line == "1") begin
        `uvm_info("CMD_LINE", "STREAM_MSG option set to 1", UVM_LOW);
        stream_msg_mode = 1;
      end else begin
        `uvm_info("CMD_LINE", "STREAM_MSG option set to 0", UVM_LOW);
        stream_msg_mode = 0;
      end
    end

    if ( clp.get_arg_value("+CTX=",cmd_line) == 0) begin
      `uvm_info("CMD_LINE", "CTX option not set", UVM_LOW);
      ctx_enable = 0;
    end else begin
      if (cmd_line == "1") begin
        `uvm_info("CMD_LINE", "CTX option set to 1", UVM_LOW);
        ctx_enable = 1;
      end else begin
        `uvm_info("CMD_LINE", "CTX option set to 0", UVM_LOW);
        ctx_enable = 0;
      end
    end

    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end
    // ---------------------------------------------------------
    //                    VERIFY TEST
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

    // Writing the SK into the MLDSA_PUBKEY register array
    for (int i = 0; i < reg_model.MLDSA_PUBKEY.m_mem.get_size(); i++) begin
        reg_model.MLDSA_PUBKEY.m_mem.write(status, i, PK[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
            `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PUBKEY[%0d]", i));
        end else begin
            `uvm_info("REG_WRITE", $sformatf("MLDSA_PUBKEY[%0d] written with %0h", i, SK[i]), UVM_LOW);
        end
    end

//=========================================================
    output_file = "./signing_input_for_test.hex";
    input_file  = "./signing_ouput_for_test.hex";
    // Open the file for writing
    fd = $fopen(output_file, "w");
    if (fd == 0) begin
      $display("ERROR: Failed to open file: %s", output_file);
      return;
    end
    $fwrite(fd, "%02X\n", 1); // Signature generation cmd
    // Generate a random MSG array
    foreach (MSG[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MSG data");
      end
      MSG[i] = data;
    end
    // Generate random CTX data
    foreach (CTX[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize CTX data");
      end
      CTX[i] = data;
    end
    // Generate random CTX size
    if (!this.randomize(data)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize CTX size");
    end
    CTX_SIZE = data[7:0];

    write_file(fd, 16, MSG); // Write 64-byte Message to the file
    write_file(fd, 1224, SK); // Write 4864-byte Secret Key to the file
    $fclose(fd);
    $system("./test_dilithium5 signing_input_for_test.hex signing_ouput_for_test.hex");
    // Open the file for reading
    fd = $fopen(input_file, "r");
    if (fd == 0) begin
      `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
      return;
    end
    else begin
      // Skip the first line
      void'($fgets(line, fd)); // Read a line from the file
      void'($sscanf(line, "%02x\n", value));
    end
    // Skip the second line
    void'($fgets(line, fd)); // Read a line from the file
    void'($sscanf(line, "%08x\n", value));
    read_line(fd, 1157, SIG);// Read 4864-byte Signature to the file
    SIG[0] = SIG[0] >> 8;
    $fclose(fd);

    // Writing MLDSA_MSG register
    foreach (reg_model.MLDSA_MSG[i]) begin
      reg_model.MLDSA_MSG[i].write(status, MSG[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[%0d] written with %0h", i, MSG[i]), UVM_LOW);
      end
    end

    // Writing the SIGNATURE into the MLDSA_SIGNATURE register array
    for (int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.write(status, i, SIG[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGNATURE[%0d]", i));
      end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGNATURE[%0d] written with %0h", i, SIG[i]), UVM_LOW);
      end
    end
    if (ctx_enable) begin
      // Writing MLDSA_CTX_CONFIG register
      reg_model.MLDSA_CTX_CONFIG.write(status, CTX_SIZE, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTX_CONFIG"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_CTX_CONFIG written with %0h", CTX_SIZE), UVM_LOW);
      end

      // Writing MLDSA_CTX register
      foreach (reg_model.MLDSA_CTX[i]) begin
        reg_model.MLDSA_CTX[i].write(status, CTX[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTX[%0d]", i));
        end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_CTX[%0d] written with %0h", i, CTX[i]), UVM_LOW);
        end
      end
    end

//=========================================================

    data = stream_msg_mode ? 'h0000_0043 : 'h0000_0003;// verify signature
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    if (stream_msg_mode) begin
      //poll for stream msg rdy
      while(!stream_msg_rdy) begin
        reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
        end else begin
          `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
        end
        stream_msg_rdy = data[2];
      end

      // Writing MLDSA_MSG register
      // Hack to stream normal message in through streaming interface
      foreach (MSG[i]) begin
        reg_model.MLDSA_MSG[0].write(status, MSG[16-1-i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[0]"));
        end else begin
          `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[0] written with %0h", MSG[16-1-i]), UVM_LOW);
        end
      end
      //write 0 to strobe since it's aligned to trigger end
      reg_model.MLDSA_MSG_STROBE.write(status, 0, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG_STROBE"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG_STROBE written with %0h", 0), UVM_LOW);
      end
      //write junk to msg to trigger end
      reg_model.MLDSA_MSG[0].write(status, MSG[6], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[0]"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[0] written with %0h", MSG[6]), UVM_LOW);
      end
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

  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



