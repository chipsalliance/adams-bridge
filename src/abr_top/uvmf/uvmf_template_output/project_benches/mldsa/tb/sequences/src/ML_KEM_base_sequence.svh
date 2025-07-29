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

class ML_KEM_base_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_KEM_base_sequence);

    
  // Variable arrays
  bit [31:0] seed_d [];
  bit [31:0] seed_z [];
  bit [31:0] ek [];
  bit [31:0] dk [];
  bit [31:0] msg [];
  bit [31:0] ciphertext [];
  bit [31:0] shared_key [];
  string input_fname, output_fname, cmd, line;
  int    fd;

  rand int rand_delay;

  //----------------------------------------------------------------------  
  // their expected vs. actual counterparts
  bit [31:0] expected_seed_d     [];
  bit [31:0] actual_seed_d       [];
  bit [31:0] expected_seed_z     [];
  bit [31:0] actual_seed_z       [];
  bit [31:0] expected_ek         [];
  bit [31:0] actual_ek           [];
  bit [31:0] expected_dk         [];
  bit [31:0] actual_dk           [];
  bit [31:0] expected_msg        [];
  bit [31:0] actual_msg          [];
  bit [31:0] expected_ciphertext [];
  bit [31:0] actual_ciphertext   [];
  bit [31:0] expected_shared_key [];
  bit [31:0] actual_shared_key   [];

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

    // size expected/actual to match
    expected_seed_d     = new[8];  actual_seed_d     = new[8];
    expected_seed_z     = new[8];  actual_seed_z     = new[8];
    expected_ek         = new[392]; actual_ek         = new[392];
    expected_dk         = new[792]; actual_dk         = new[792];
    expected_msg        = new[8];   actual_msg        = new[8];
    expected_ciphertext = new[392]; actual_ciphertext = new[392];
    expected_shared_key = new[8];   actual_shared_key = new[8];

  endfunction


  // Poll a single status bit until it becomes 1
  task wait_for_done(int bit_idx, string flag_name);
    bit done = 0;
    uvm_status_e status;
    while (!done) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ_FAIL", $sformatf("Failed to read %s", flag_name));
      end
      else begin
        `uvm_info("REG_READ", $sformatf("%s = %0h", flag_name, data), UVM_HIGH);
      end
      done = data[bit_idx];
    end
  endtask
  

  // 4) Write one register (used for CTRL writes)
  task run_operation(bit [31:0] cmd, string op_name);
    uvm_status_e status;
    reg_model.MLKEM_CTRL.write(status, cmd, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) begin
      `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_CTRL for %s", op_name));
    end
    else begin
      `uvm_info("REG_WRITE", $sformatf("Triggered %s (0x%0h)", op_name, cmd), UVM_LOW);
    end
  endtask

  // Zeroize via CTRL
  task zeroize();
    run_operation('h8, "zeroization");
  endtask

  task write_z_and_d_sed();
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
  endtask


  task write_ek();
    // Write MLKEM_ENCAPS_KEY
    for(int j = 0; j < reg_model.MLKEM_ENCAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.write(status, j, ek[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_ENCAPS_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_ENCAPS_KEY[%0d]: %0h", j, ek[j]), UVM_LOW);
      end
    end
  endtask

  task read_ek();
    // Reading MLKEM_ENCAPS_KEY register
    for(int i = 0; i < reg_model.MLKEM_ENCAPS_KEY.m_mem.get_size(); i++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.read(status, i, actual_ek[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_ENCAPS_KEY[%0d]", i));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_ENCAPS_KEY[%0d]: %0h", i, actual_ek[i]), UVM_LOW);
      end
    end
  endtask

  task write_dk();
    // Write MLKEM_DECAPS_KEY
    for(int j = 0; j < reg_model.MLKEM_DECAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_DECAPS_KEY.m_mem.write(status, j, dk[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_DECAPS_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_DECAPS_KEY[%0d]: %0h", j, dk[j]), UVM_LOW);
      end
    end
  endtask

  task read_dk();
    // Read MLKEM_DECAPS_KEY
    for(int j = 0; j < reg_model.MLKEM_DECAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_DECAPS_KEY.m_mem.read(status, j, actual_dk[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to read MLKEM_DECAPS_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully read MLKEM_DECAPS_KEY[%0d]: %0h", j, actual_dk[j]), UVM_LOW);
      end
    end
  endtask

  task write_msg();
    // Write MLKEM_MSG
    for(int j = 0; j < reg_model.MLKEM_MSG.m_mem.get_size(); j++) begin
      reg_model.MLKEM_MSG.m_mem.write(status, j, msg[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_MSG[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_MSG[%0d]: %0h", j, msg[j]), UVM_LOW);
      end
    end
  endtask

  task read_shared_key();
    // Reading MLKEM_SHARED_KEY register
    foreach (reg_model.MLKEM_SHARED_KEY[j]) begin
      reg_model.MLKEM_SHARED_KEY[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_SHARED_KEY[%0d]", j));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_SHARED_KEY[%0d]: %0h", j, data), UVM_LOW);
        actual_shared_key[j] = data;
      end
    end
  endtask

  task read_ciphertext();
    // Reading MLKEM_CIPHERTEXT register
    for(int j = 0; j < reg_model.MLKEM_CIPHERTEXT.m_mem.get_size(); j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_CIPHERTEXT[%0d]", j));
      end else begin
        `uvm_info("REG_READ", $sformatf("MLKEM_CIPHERTEXT[%0d]: %0h", j, data), UVM_LOW);
        actual_ciphertext[j] = data;
      end
    end
  endtask

  task write_ciphertext();
    // Write MLKEM_CIPHERTEXT
    for(int j = 0; j < reg_model.MLKEM_CIPHERTEXT.m_mem.get_size(); j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.write(status, j, ciphertext[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_WRITE_FAIL", $sformatf("Failed to write MLKEM_CIPHERTEXT[%0d]", j));
      end else begin
        `uvm_info("REG_WRITE_PASS", $sformatf("Successfully wrote MLKEM_CIPHERTEXT[%0d]: %0h", j, ciphertext[j]), UVM_LOW);
      end
    end
  endtask

  task run_model_for_keygen_with_rand_val(bit on_the_fly_reset = 0);
    // 1) randomize seeds
    foreach (seed_d[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED_D data");
      end
      seed_d[i] = data;
      `uvm_info("RND_GEN", $sformatf("randomize SEED_D[%0d]: %0h", i, seed_d[i]), UVM_LOW);
    end
    foreach (seed_z[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED_Z data");
      end
      seed_z[i] = data;
      `uvm_info("RND_GEN", $sformatf("randomize SEED_Z[%0d]: %0h", i, seed_z[i]), UVM_LOW);
    end
  
    // 2) write the python‐readable input file
    input_fname = "ml-kem/tv/keygen_ext_input.txt";
    fd = $fopen(input_fname, "w");
    if (fd == 0) $fatal("Cannot open %s for writing", input_fname);
  
    // line1: operation code
    $fwrite(fd, "1\n");

    // line2-3: z, d as hex strings
    write_file(fd, 8, seed_z);
    write_file(fd, 8, seed_d);
  
  
    $fclose(fd);
  
    // 3) invoke the python generator
    cmd = $sformatf(
      "python3.9 ml-kem/random_test_ml_kem.py 1 -i %s -o ml-kem/tv/keygen_ext_output.txt",
      input_fname
    );
    $display("## Running: %s", cmd);
    if ($system(cmd) != 0) 
      `uvm_error("PYTHON_FAIL","External Python script failed");
  
    // 4) read back ek and dk from the output file
    output_fname = "ml-kem/tv/keygen_ext_output.txt";
    fd = $fopen(output_fname, "r");
    if (fd == 0) $fatal("Cannot open %s for reading", output_fname);
  
  
    // skip lines 1–3 (op, z, d)
    void'($fgets(line, fd));
    void'($fgets(line, fd));
    void'($fgets(line, fd));

    read_line(fd, 392, expected_ek);
    read_line(fd, 792, expected_dk);  
    $fclose(fd);

    if (on_the_fly_reset) begin
      `uvm_info("ON_THE_FLY_RESET",$sformatf("reseting the expected results"), UVM_LOW);
      expected_ek = new[expected_ek.size()];
      expected_dk = new[expected_dk.size()];
    end 
  endtask

  task compare_keygen_vectors();
    // Compare Encapsulation Key (ek)
    foreach (expected_ek[i]) begin
      if (actual_ek[i] !== expected_ek[i]) begin
        `uvm_error("EK_MISMATCH",
          $sformatf("ek[%0d] mismatch: expected %08h, actual %08h",
            i, expected_ek[i], actual_ek[i]));
      end else begin
        `uvm_info("EK_MATCH",
          $sformatf("ek[%0d] match: %08h", i, actual_ek[i]),
          UVM_LOW);
      end
    end
  
    // Compare Decapsulation Key (dk)
    foreach (expected_dk[j]) begin
      if (actual_dk[j] !== expected_dk[j]) begin
        `uvm_error("DK_MISMATCH",
          $sformatf("dk[%0d] mismatch: expected %08h, actual %08h",
            j, expected_dk[j], actual_dk[j]));
      end else begin
        `uvm_info("DK_MATCH",
          $sformatf("dk[%0d] match: %08h", j, actual_dk[j]),
          UVM_LOW);
      end
    end
  endtask


  task run_model_for_encap_with_rand_val(bit decaps_rej = 0);
    run_model_for_keygen_with_rand_val();

    if (decaps_rej) begin
      `uvm_info("DECAPS_REJ", $sformatf("Decaps flow will reject due to wrong ek used"), UVM_LOW);
      //use expected ek as the "wrong" ek for decaps failure
      foreach (expected_ek[i]) begin
        ek[i] = expected_ek[i];
      end
      //generate new keys, but we won't use the new ek
      run_model_for_keygen_with_rand_val();
    end else begin
      `uvm_info("DECAPS_REJ", $sformatf("Decaps flow will not reject"), UVM_LOW);
      //just use the ek from the keygen flow
      foreach (expected_ek[i]) begin
        ek[i] = expected_ek[i];
      end
    end

    // 1) randomize seeds
    foreach (msg[i]) begin
      if (!this.randomize(data)) begin
        `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MSG data");
      end
      msg[i] = data;
      `uvm_info("RND_GEN", $sformatf("randomize MSG[%0d]: %0h", i, msg[i]), UVM_LOW);
    end
    
  
    // 2) write the python‐readable input file
    input_fname = "ml-kem/tv/encap_ext_input.txt";
    fd = $fopen(input_fname, "w");
    if (fd == 0) $fatal("Cannot open %s for writing", input_fname);
  
    // line1: operation code
    $fwrite(fd, "2\n");

    // line2-3: z, d as hex strings
    write_file(fd, 8, msg);
    write_file(fd, 392, ek);
  
  
    $fclose(fd);
  
    // 3) invoke the python generator
    cmd = $sformatf(
      "python3.9 ml-kem/random_test_ml_kem.py 2 -i %s -o ml-kem/tv/encap_ext_output.txt",
      input_fname
    );
    $display("## Running: %s", cmd);
    if ($system(cmd) != 0) 
      `uvm_error("PYTHON_FAIL","External Python script failed");
  
    // 4) read back ek and dk from the output file
    output_fname = "ml-kem/tv/encap_ext_output.txt";
    fd = $fopen(output_fname, "r");
    if (fd == 0) $fatal("Cannot open %s for reading", output_fname);
  
  
    // skip lines 1–3 (op, m, ek)
    void'($fgets(line, fd));
    void'($fgets(line, fd));
    void'($fgets(line, fd));

    read_line(fd, 8, expected_shared_key);
    read_line(fd, 392, expected_ciphertext);  
    $fclose(fd);
  endtask

  task compare_encap_vectors();
    // Compare Shared Key (K)
    foreach (expected_shared_key[i]) begin
      if (actual_shared_key[i] !== expected_shared_key[i]) begin
        `uvm_error("K_MISMATCH",
          $sformatf("K[%0d] mismatch: expected %08h, actual %08h",
            i, expected_shared_key[i], actual_shared_key[i]));
      end else begin
        `uvm_info("K_MATCH",
          $sformatf("K[%0d] match: %08h", i, actual_shared_key[i]),
          UVM_LOW);
      end
    end
  
    // Compare Ciphertext (c)
    foreach (expected_ciphertext[j]) begin
      if (actual_ciphertext[j] !== expected_ciphertext[j]) begin
        `uvm_error("c_MISMATCH",
          $sformatf("c[%0d] mismatch: expected %08h, actual %08h",
            j, expected_ciphertext[j], actual_ciphertext[j]));
      end else begin
        `uvm_info("c_MATCH",
          $sformatf("c[%0d] match: %08h", j, actual_ciphertext[j]),
          UVM_LOW);
      end
    end
  endtask

  task run_model_for_decap_with_rand_val(bit decaps_rej = 0);
    run_model_for_encap_with_rand_val(decaps_rej);
    foreach (expected_dk[i]) begin
      dk[i] = expected_dk[i];
    end
    foreach (expected_ciphertext[i]) begin
      ciphertext[i] = expected_ciphertext[i];
    end
  
    // 2) write the python‐readable input file
    input_fname = "ml-kem/tv/decap_ext_input.txt";
    fd = $fopen(input_fname, "w");
    if (fd == 0) $fatal("Cannot open %s for writing", input_fname);
  
    // line1: operation code
    $fwrite(fd, "3\n");

    // line2-3: z, d as hex strings
    write_file(fd, 792, dk);
    write_file(fd, 392, ciphertext);
  
  
    $fclose(fd);
  
    // 3) invoke the python generator
    cmd = $sformatf(
      "python3.9 ml-kem/random_test_ml_kem.py 3 -i %s -o ml-kem/tv/decap_ext_output.txt",
      input_fname
    );
    $display("## Running: %s", cmd);
    if ($system(cmd) != 0) 
      `uvm_error("PYTHON_FAIL","External Python script failed");
  
    // 4) read back ek and dk from the output file
    output_fname = "ml-kem/tv/decap_ext_output.txt";
    fd = $fopen(output_fname, "r");
    if (fd == 0) $fatal("Cannot open %s for reading", output_fname);
  
  
    // skip lines 1–3 (op, dk, c)
    void'($fgets(line, fd));
    void'($fgets(line, fd));
    void'($fgets(line, fd));

    read_line(fd, 8, expected_shared_key);  
    $fclose(fd);
  endtask

  task compare_decap_vectors();
    // Compare Shared Key (K)
    foreach (expected_shared_key[i]) begin
      if (actual_shared_key[i] !== expected_shared_key[i]) begin
        `uvm_error("K_MISMATCH",
          $sformatf("K[%0d] mismatch: expected %08h, actual %08h",
            i, expected_shared_key[i], actual_shared_key[i]));
      end else begin
        `uvm_info("K_MATCH",
          $sformatf("K[%0d] match: %08h", i, actual_shared_key[i]),
          UVM_LOW);
      end
    end
  endtask
  

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end