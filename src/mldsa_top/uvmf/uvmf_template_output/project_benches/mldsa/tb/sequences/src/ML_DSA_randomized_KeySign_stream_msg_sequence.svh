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

class ML_DSA_randomized_KeySign_stream_msg_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_KeySign_stream_msg_sequence);


  bit [31:0] STREAM_MSG [0:16383];
  // inside your sequence class
  int unsigned msg_length;
  bit[1:0] last_msg_padding;

  

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    
    bit ready;
    bit stream_msg_rdy;
    bit valid;
    bit [31:0] reversed_data;
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
    $system("./test_dilithium5_strm_msg keygen_input_for_test.hex keygen_output_for_test.hex");

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


    output_file = "./signing_input_for_test.hex";
    input_file = "./signing_output_for_test.hex";
    // Writing MLDSA_MSG register
    foreach (STREAM_MSG[i]) begin
      // Randomize the data before writing
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG data");
      end
      else begin
        STREAM_MSG[i] = data;
      end
    end
    data = 0;
    if (!this.randomize(last_msg_padding)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG last padding");
    end
    last_msg_padding = last_msg_padding & 3;
    `uvm_info("RANDOMIZATION", $sformatf("MLDSA_MSG last message padding is %0d", last_msg_padding), UVM_LOW);
    if (!this.randomize(msg_length)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG lenght");
    end
    msg_length = msg_length & 16'h3FFE;
    `uvm_info("RANDOMIZATION", $sformatf("MLDSA_MSG Lenght is %0d", ((msg_length*4)+last_msg_padding)), UVM_LOW);


    // Open the file for writing
    fd = $fopen(output_file, "w");
    if (fd == 0) begin
        $display("ERROR: Failed to open file: %s", output_file);
        return;
    end
    // Write the Signature generation command, message lenght, secret key
    $fwrite(fd, "%02X\n", 1); // Signing command
    $fwrite(fd, "%08X\n", (msg_length*4)+last_msg_padding); // Signing command
    write_strm_msg_file(fd, msg_length, STREAM_MSG, last_msg_padding); // Write 32-byte SEED to the file
    write_file(fd, 1224, SK); // Write 32-byte SEED to the file
    $fclose(fd);
    $system("./test_dilithium5_strm_msg signing_input_for_test.hex signing_output_for_test.hex");
    // Open the generated file for reading
    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    // Skip the one (Sign command)
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    // Skip the second line
    void'($fgets(line, fd)); // Read a line from the file
    void'($sscanf(line, "%08x\n", value));
    read_line(fd, 1157, SIG);// Read 4864-byte Signature to the file
    SIG[1156] = SIG[1156] >> 8;
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

    data = 'h0000_0044; // Perform signing operation
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h", data), UVM_LOW);
    end

    //poll for stream msg rdy
    stream_msg_rdy = 0;
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
    // 1) Write each word of the message
    for (int j = 0; j < msg_length; j++) begin
      reg_model.MLDSA_MSG[0].write(status,
                                  STREAM_MSG[j],
                                  UVM_FRONTDOOR,
                                  reg_model.default_map,
                                  this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at index %0d", j));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h at index %0d",
                            STREAM_MSG[j],
                            j),
                  UVM_LOW);
      end
    end
    //write 0 to strobe since it's aligned to trigger end
    if (last_msg_padding==1) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0001, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
                              32'h0000_00AB, // This is a hard-coded value
                              UVM_FRONTDOOR,
                              reg_model.default_map,
                              this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  32'h0000_00AB),
                  UVM_LOW);
      end
    end
    else if (last_msg_padding==2) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0011, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
      32'h0000_CDAB, // This is a hard-coded value
      UVM_FRONTDOOR,
      reg_model.default_map,
      this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  32'h0000_CDAB),
                  UVM_LOW);
      end
    end
    else if (last_msg_padding==3) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0111, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
      32'h00EF_CDAB, // This is a hard-coded value
      UVM_FRONTDOOR,
      reg_model.default_map,
      this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  32'h00EF_CDAB),
                  UVM_LOW);
      end
    end
    else begin    
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0000, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG_STROBE"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG_STROBE written with %0h", 0), UVM_LOW);
      end
      //write junk to msg to trigger end
      reg_model.MLDSA_MSG[0].write(status, 0, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[0]"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[0] written with %0h", 0), UVM_LOW);
      end
    end

    valid = 0;
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
        reversed_data = {data[7:0],  data[15:8], data[23:16], data[31:24]};
        if (PK[i] != reversed_data)
        `uvm_error("REG_READ", $sformatf("MLDSA_PUBKEY[%0d] mismatch: actual=0x%08h, expected=0x%08h",
                  i, reversed_data, PK[i]));
      end
    end

    // Reading MLDSA_SIGNATURE register
    for(int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d]: %0h", i, data), UVM_LOW);
        reversed_data = {data[7:0],  data[15:8], data[23:16], data[31:24]};
        if (SIG[i] != reversed_data)
        `uvm_error("REG_READ", $sformatf("MLDSA_SIG[%0d] mismatch: actual=0x%08h, expected=0x%08h",
                  i, reversed_data, SIG[i]));
      end
    end

    // ---------------------------------------------------------
    //              KEYGEN TEST IS DONE
    // ---------------------------------------------------------


  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end



