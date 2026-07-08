//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION:
//   Coverage-directed sequence that asserts ZEROIZE mid-signing with a wide
//   set of random delays spanning the entire signing operation. The intent is
//   to close the following ABR SCA coverage cross bins that the existing
//   ML_DSA_randomized_zeroize_sequence (0-100 ns delay) is too early to hit:
//
//     - zeroizeXmasking  [zeroize=1][masking=1]  (SCA masked NTT window)
//     - zeroizeXntt1     [zeroize=1][ntt1_en=1]  (NTT[1] active window)
//     - zeroizeXrecombine[zeroize=1][recombine=1](recombine phase)
//
//   Approach: run NUM_ITER back-to-back keygen+sign operations, each with a
//   random delay drawn from a wide bucket that covers the setup, masked-NTT,
//   PWM, and recombine phases. After the delay we deassert MLDSA_CTRL then
//   pulse zeroize (0x8), then re-init and continue.
//
//----------------------------------------------------------------------

class ML_DSA_randomized_zeroize_mid_op_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_randomized_zeroize_mid_op_sequence);

  // Number of signing iterations. Each iteration draws an independent delay
  // from one of the buckets below so all SCA windows are eventually hit.
  localparam int NUM_ITER = 8;

  // Delay buckets (in ns). Chosen to span the phases of an MLDSA-87 signing
  // operation observed in nightly regression:
  //   bucket 0:       0 ..   1_000 ns  — startup / message hash
  //   bucket 1:   1_000 ..  20_000 ns  — early NTT, first masked windows
  //   bucket 2:  20_000 ..  80_000 ns  — deep masked NTT + PWM (masking=1,
  //                                       ntt1_en=1 typically active here)
  //   bucket 3:  80_000 .. 200_000 ns  — recombine / late signing phases
  int unsigned random_delay;
  int          bucket;

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();

    bit ready;
    string output_file = "./keygen_input_for_test.hex";
    string input_file  = "./keygen_output_for_test.hex";
    int    fd;
    string line;
    int    value;

    reg_model.reset();
    data = 0;
    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map map is not initialized");
    end else begin
      `uvm_info("MAP_INIT", "mldsa_uvm_rm.default_map is initialized", UVM_LOW);
    end

    // --------------------------------------------------------------
    // PRE test: generate a reference keypair once (SEED/PK/SK reused)
    // --------------------------------------------------------------
    fd = $fopen(output_file, "w");
    if (fd == 0) begin
      $display("ERROR: Failed to open file: %s", output_file);
      return;
    end
    foreach (SEED[i]) begin
      if (!this.randomize(data)) `uvm_error("RANDOMIZE_FAIL", "SEED");
      SEED[i] = data;
    end
    $fwrite(fd, "%02X\n", 0);
    write_file(fd, 32/4, SEED);
    $fclose(fd);
    $system("./test_dilithium5 keygen_input_for_test.hex keygen_output_for_test.hex");

    fd = $fopen(input_file, "r");
    if (fd == 0) begin
      `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
      return;
    end
    void'($fgets(line, fd));
    void'($sscanf(line, "%02x\n", value));
    read_line(fd, 648,  PK);
    read_line(fd, 1224, SK);
    $fclose(fd);

    // --------------------------------------------------------------
    // Main loop: NUM_ITER signing attempts, each aborted by zeroize
    // at a bucket-random delay to hit all SCA-active windows.
    // --------------------------------------------------------------
    for (int iter = 0; iter < NUM_ITER; iter++) begin

      // Wait for ready
      ready = 0;
      while (!ready) begin
        reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_READ", "MLDSA_STATUS");
        ready = data[0];
      end

      // Write SEED
      foreach (reg_model.MLDSA_SEED[i]) begin
        reg_model.MLDSA_SEED[i].write(status, SEED[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("MLDSA_SEED[%0d]", i));
      end

      // Write MSG (random)
      foreach (reg_model.MLDSA_MSG[i]) begin
        if (!this.randomize(data)) `uvm_error("RANDOMIZE_FAIL", "MLDSA_MSG");
        reg_model.MLDSA_MSG[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("MLDSA_MSG[%0d]", i));
      end

      // Write SIGN_RND = 0
      foreach (reg_model.MLDSA_SIGN_RND[i]) begin
        data = 'h0;
        reg_model.MLDSA_SIGN_RND[i].write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("MLDSA_SIGN_RND[%0d]", i));
      end

      // Start signing
      data = 'h0000_0004;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "MLDSA_CTRL (start sign)");
      `uvm_info("ZERO_MIDOP", $sformatf("iter=%0d: signing started", iter), UVM_LOW);

      // Deassert start (per existing zeroize pattern)
      data = 'h0000_0000;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "MLDSA_CTRL (deassert)");

      // Draw delay from bucket (iter mod 4). Each bucket is exercised
      // twice per test invocation to survive seed variance.
      bucket = iter % 4;
      case (bucket)
        0: begin
          if (!randomize(random_delay) with { random_delay inside {[100:1_000]}; })
            `uvm_error("RANDOMIZE_FAIL", "delay bucket 0");
        end
        1: begin
          if (!randomize(random_delay) with { random_delay inside {[1_000:20_000]}; })
            `uvm_error("RANDOMIZE_FAIL", "delay bucket 1");
        end
        2: begin
          if (!randomize(random_delay) with { random_delay inside {[20_000:80_000]}; })
            `uvm_error("RANDOMIZE_FAIL", "delay bucket 2");
        end
        3: begin
          if (!randomize(random_delay) with { random_delay inside {[80_000:200_000]}; })
            `uvm_error("RANDOMIZE_FAIL", "delay bucket 3");
        end
      endcase
      `uvm_info("ZERO_MIDOP",
                $sformatf("iter=%0d bucket=%0d delay=%0d ns", iter, bucket, random_delay),
                UVM_LOW);

      #random_delay;

      // Pulse zeroize
      data = 'h0000_0008;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "MLDSA_CTRL (zeroize)");
      `uvm_info("ZERO_MIDOP", $sformatf("iter=%0d: zeroize asserted", iter), UVM_LOW);

      // Small settle so zeroize propagates through the datapath before next
      // iteration re-programs registers.
      #500;
    end

    `uvm_info("ZERO_MIDOP", "ML_DSA_randomized_zeroize_mid_op_sequence DONE", UVM_LOW);

  endtask
endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
