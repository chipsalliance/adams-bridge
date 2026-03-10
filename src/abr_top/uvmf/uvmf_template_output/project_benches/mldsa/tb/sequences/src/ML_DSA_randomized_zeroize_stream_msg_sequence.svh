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
// Test scenario:
//   Phase 1: Start a signing operation in stream msg mode, begin streaming
//            the message, then assert zeroize mid-stream.
//   Phase 2: Re-run a complete keygen + signing operation in stream msg mode
//            and verify the results match the reference model, proving the
//            zeroize properly cleared all internal state.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class ML_DSA_randomized_zeroize_stream_msg_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_zeroize_stream_msg_sequence);

  bit [31:0] STREAM_MSG [0:16383];
  int unsigned msg_length;
  bit[1:0] last_msg_padding;
  bit [31:0] last_msg_data;
  int unsigned random_delay;
  int unsigned zeroize_point;

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

    // =============================================================
    //  PHASE 1: Keygen + Signing in stream msg mode, zeroize mid-stream
    // =============================================================

    // --- Ref model: generate keys ---
    fd = $fopen(output_file, "w");
    if (fd == 0) begin
        $display("ERROR: Failed to open file: %s", output_file);
        return;
    end
    foreach (SEED[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED data");
      end
      SEED[i] = data;
    end
    $fwrite(fd, "%02X\n", 0); // KeyGen command
    write_file(fd, 32/4, SEED);
    $fclose(fd);
    $system("./test_dilithium5_strm_msg keygen_input_for_test.hex keygen_output_for_test.hex");

    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    read_line(fd, 648, PK);
    read_line(fd, 1224, SK);
    $fclose(fd);

    // --- Randomize stream msg data ---
    foreach (STREAM_MSG[i]) begin
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize STREAM_MSG data");
      end
      else begin
        STREAM_MSG[i] = data;
      end
    end
    data = 0;
    if (!this.randomize(last_msg_padding)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG last padding");
    end
    last_msg_padding = last_msg_padding & 2'h3;
    if (!this.randomize(msg_length)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG length");
    end
    msg_length = msg_length & 16'h1FFF;
    if (msg_length < 2) msg_length = 2; // Ensure at least 2 words so we can zeroize mid-stream
    `uvm_info("PHASE1", $sformatf("MLDSA_MSG Length is %0d bytes, %0d words", ((msg_length*4)+last_msg_padding), msg_length), UVM_LOW);

    if (!this.randomize(last_msg_data)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize last MLDSA_MSG data");
    end

    // --- HW: Wait for ready ---
    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // --- HW: Write SEED ---
    foreach (reg_model.MLDSA_SEED[i]) begin
      reg_model.MLDSA_SEED[i].write(status, SEED[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SEED[%0d] written with %0h", i, SEED[i]), UVM_LOW);
      end
    end

    // --- HW: Write SIGN_RND ---
    foreach (reg_model.MLDSA_SIGN_RND[i]) begin
      data = 'h0000_0000;
      reg_model.MLDSA_SIGN_RND[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGN_RND[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGN_RND[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    // --- HW: Start signing in stream msg mode ---
    data = 'h0000_0044; // Signing + stream msg mode
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h (sign + stream msg)", data), UVM_LOW);
    end

    // --- HW: Poll for stream msg ready ---
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

    // --- HW: Write partial stream msg then zeroize ---
    // Choose a random point to zeroize (between 1 and msg_length-1)
    if (!this.randomize(zeroize_point) with { zeroize_point inside {[1:msg_length-1]}; }) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize zeroize_point");
      zeroize_point = 1;
    end
    `uvm_info("PHASE1", $sformatf("Will zeroize after writing %0d of %0d msg words", zeroize_point, msg_length), UVM_LOW);

    for (int j = 0; j < zeroize_point; j++) begin
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
                  $sformatf("MLDSA_MSG[0] written with %0h at index %0d (phase1 partial)",
                            STREAM_MSG[j], j),
                  UVM_LOW);
      end
    end

    // --- HW: Assert zeroize ---
    `uvm_info("PHASE1", "Asserting zeroize during stream msg", UVM_LOW);
    data = 'h0000_0000; // Clear CTRL first
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL cleared to %0h", data), UVM_LOW);
    end

    // Random delay before zeroize
    if (!randomize(random_delay) with { random_delay inside {[0:100]}; }) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize delay");
    end else begin
      `uvm_info("RANDOM_DELAY", $sformatf("Random delay before zeroize: %0d cycles", random_delay), UVM_LOW);
    end
    #random_delay;

    data = 'h0000_0008; // Zeroize
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h (zeroize asserted)", data), UVM_LOW);
    end

    // Read registers after zeroize to let it complete
    for(int i = 0; i < reg_model.MLDSA_PUBKEY.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PUBKEY.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_PUBKEY[%0d] after zeroize: %0h", i, data), UVM_LOW);
      end
    end

    for(int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d] after zeroize: %0h", i, data), UVM_LOW);
      end
    end

    `uvm_info("PHASE1", "Phase 1 complete: zeroize during stream msg done", UVM_LOW);

    // =============================================================
    //  PHASE 2: Clean keygen + signing in stream msg mode, verify results
    // =============================================================

    // --- Ref model: generate new keys ---
    output_file = "./keygen_input_for_test.hex";
    input_file = "./keygen_output_for_test.hex";

    fd = $fopen(output_file, "w");
    if (fd == 0) begin
        $display("ERROR: Failed to open file: %s", output_file);
        return;
    end
    foreach (SEED[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED data");
      end
      SEED[i] = data;
    end
    $fwrite(fd, "%02X\n", 0); // KeyGen command
    write_file(fd, 32/4, SEED);
    $fclose(fd);
    $system("./test_dilithium5_strm_msg keygen_input_for_test.hex keygen_output_for_test.hex");

    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    read_line(fd, 648, PK);
    read_line(fd, 1224, SK);
    $fclose(fd);

    // --- Ref model: generate new stream msg and sign ---
    output_file = "./signing_input_for_test.hex";
    input_file = "./signing_output_for_test.hex";

    foreach (STREAM_MSG[i]) begin
      if (!this.randomize(data)) begin
          `uvm_error("RANDOMIZE_FAIL", "Failed to randomize STREAM_MSG data");
      end
      else begin
        STREAM_MSG[i] = data;
      end
    end
    data = 0;
    if (!this.randomize(last_msg_padding)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG last padding");
    end
    last_msg_padding = last_msg_padding & 2'h3;
    if (!this.randomize(msg_length)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MLDSA_MSG length");
    end
    msg_length = msg_length & 16'h1FFF;
    `uvm_info("PHASE2", $sformatf("MLDSA_MSG Length is %0d bytes", ((msg_length*4)+last_msg_padding)), UVM_LOW);

    if (!this.randomize(last_msg_data)) begin
      `uvm_error("RANDOMIZE_FAIL", "Failed to randomize last MLDSA_MSG data");
    end
    `uvm_info("PHASE2", $sformatf("MLDSA_MSG last message is %08h", last_msg_data), UVM_LOW);

    fd = $fopen(output_file, "w");
    if (fd == 0) begin
        $display("ERROR: Failed to open file: %s", output_file);
        return;
    end
    $fwrite(fd, "%02X\n", 1); // Signing command
    $fwrite(fd, "%08X\n", (msg_length*4)+last_msg_padding);
    write_strm_msg_file(fd, msg_length, STREAM_MSG, last_msg_padding, last_msg_data); 
    write_file(fd, 1224, SK); 
    $fclose(fd);
    $system("./test_dilithium5_strm_msg signing_input_for_test.hex signing_output_for_test.hex");

    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
        return;
    end
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    void'($fgets(line, fd));
    void'($sscanf(line, "%08x\n", value));
    read_line(fd, 1157, SIG);
    SIG[1156] = SIG[1156] >> 8;
    $fclose(fd);
    data = 0;

    // --- HW: Wait for ready after zeroize ---
    ready = 0;
    while(!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_STATUS"));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_STATUS: %0h", data), UVM_HIGH);
      end
      ready = data[0];
    end

    // --- HW: Write new SEED ---
    foreach (reg_model.MLDSA_SEED[i]) begin
      reg_model.MLDSA_SEED[i].write(status, SEED[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SEED[%0d] written with %0h", i, SEED[i]), UVM_LOW);
      end
    end

    // --- HW: Write SIGN_RND ---
    foreach (reg_model.MLDSA_SIGN_RND[i]) begin
      data = 'h0000_0000;
      reg_model.MLDSA_SIGN_RND[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGN_RND[%0d]", i));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_SIGN_RND[%0d] written with %0h", i, data), UVM_LOW);
      end
    end

    // --- HW: Start signing in stream msg mode ---
    data = 'h0000_0044; // Signing + stream msg mode
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_CTRL"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_CTRL written with %0h (sign + stream msg)", data), UVM_LOW);
    end

    // --- HW: Poll for stream msg ready ---
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

    // Restore MSG_STROBE to all-valid (zeroize hwclr sets it to 0)
    reg_model.MLDSA_MSG_STROBE.write(status, 4'b1111, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG_STROBE"));
    end else begin
      `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG_STROBE restored to 4'b1111"), UVM_LOW);
    end

    // --- HW: Write full stream message ---
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
                            STREAM_MSG[j], j),
                  UVM_LOW);
      end
    end

    // Write last msg word with padding/strobe
    if (last_msg_padding==1) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0001, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
                              {24'h0,last_msg_data[7:0]},
                              UVM_FRONTDOOR,
                              reg_model.default_map,
                              this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  {24'h0,last_msg_data[7:0]}),
                  UVM_LOW);
      end
    end
    else if (last_msg_padding==2) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0011, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
                                {16'h0,last_msg_data[7:0],last_msg_data[15:8]},
                                UVM_FRONTDOOR,
                                reg_model.default_map,
                                this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  {16'h0,last_msg_data[7:0],last_msg_data[15:8]}),
                  UVM_LOW);
      end
    end
    else if (last_msg_padding==3) begin
      reg_model.MLDSA_MSG_STROBE.write(status, 4'b0111, UVM_FRONTDOOR, reg_model.default_map, this);
      reg_model.MLDSA_MSG[0].write(status,
                            {8'h0,last_msg_data[7:0],last_msg_data[15:8],last_msg_data[23:16]},
                            UVM_FRONTDOOR,
                            reg_model.default_map,
                            this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE",
                  $sformatf("Failed to write MLDSA_MSG[0] at the last index"));
      end else begin
        `uvm_info("REG_WRITE",
                  $sformatf("MLDSA_MSG[0] written with %0h",
                  {8'h0,last_msg_data[7:0],last_msg_data[15:8],last_msg_data[23:16]}),
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
      reg_model.MLDSA_MSG[0].write(status, 0, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[0]"));
      end else begin
        `uvm_info("REG_WRITE", $sformatf("MLDSA_MSG[0] written with %0h", 0), UVM_LOW);
      end
    end

    // --- HW: Wait for valid ---
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

    // --- HW: Read and verify PUBKEY ---
    for(int i = 0; i < reg_model.MLDSA_PUBKEY.m_mem.get_size(); i++) begin
      reg_model.MLDSA_PUBKEY.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_PUBKEY[%0d]: %0h", i, data), UVM_LOW);
        if (PK[i] != data)
        `uvm_error("REG_READ", $sformatf("MLDSA_PUBKEY[%0d] mismatch: actual=0x%08h, expected=0x%08h",
                  i, data, PK[i]));
      end
    end

    // --- HW: Read and verify SIGNATURE ---
    for(int i = 0; i < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); i++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.read(status, i, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLDSA_SIGNATURE[%0d]: %0h", i, data), UVM_LOW);
        if (SIG[i] != data)
        `uvm_error("REG_READ", $sformatf("MLDSA_SIG[%0d] mismatch: actual=0x%08h, expected=0x%08h",
                  i, data, SIG[i]));
      end
    end

    // =============================================================
    //  PHASE 2 COMPLETE: Zeroize stream msg test done
    // =============================================================
    `uvm_info("TEST_DONE", "Zeroize during stream msg test completed successfully", UVM_LOW);

  endtask
endclass


// pragma uvmf custom external begin
// pragma uvmf custom external end


