//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION: Randomized keygen + sign + verify self check, parameter set
// agnostic.
//
// Why this exists
// ---------------
// Every other randomized ML-DSA test (ML_DSA_randomized_all and friends)
// leaves MLDSA_CTRL.PARAM_SET at its reset value, so all randomized ML-DSA
// stimulus in the bench runs at category 5. ML-DSA-44 and ML-DSA-65 were
// covered only by fixed known-answer vectors, which means a datapath that is
// wrong for one particular secret - a rejection-rate dependent sampler bug, a
// hint that only overflows for some w1, a c~ width that only matters when the
// top bytes happen to be nonzero - would never have been hit at those sets.
// ML-KEM already had randomized round trips at all three of its parameter sets
// (ML_KEM_512/768/1024_kg_encaps_decaps); this closes the same hole on the
// signature side.
//
// Why it is a self check and not a known-answer test
// --------------------------------------------------
// The in-tree C Dilithium reference is hardcoded to the category-5 c~ and tr
// sizing for every DILITHIUM_MODE (see the warning block in
// Dilithium_ref/dilithium/ref/params.h), so it cannot act as a golden model at
// ML-DSA-44 or ML-DSA-65. Rather than bind randomized stimulus to a reference
// that cannot follow it, this sequence checks the property that does not need
// one: a signature the hardware produced over a random seed and a random
// message must verify back in the hardware, and MLDSA_VERIFY_RES must
// reproduce c~ exactly. Fixed vectors from tools/mldsa_ref.py still pin
// absolute correctness against FIPS 204; this pins self consistency across
// random secrets.
//
// What each iteration checks
//   1. KEYGEN+SIGN over a random seed and random message at the selected set
//   2. MLDSA_SIGNATURE and MLDSA_PUBKEY read zero past their FIPS 204 length
//   3. MLDSA_PRIVKEY_OUT reads zero - the keygen+sign privkey lock holds
//   4. The signature verifies back with hardware mu derivation
//   5. MLDSA_VERIFY_RES equals c~ and reads zero above the c~ length
//   6. MLDSA_STATUS.VERIFY_PASS agrees with the data comparison
//
// Derived classes set ps_name, ps_ctrl and the three length constants.
//
//----------------------------------------------------------------------

virtual class ML_DSA_randomized_kg_sign_verify_base_sequence extends mldsa_bench_sequence_base;

  // Selected by the derived class.
  string ps_name;              // for messages, e.g. "ML-DSA-65"
  bit [31:0] ps_ctrl;          // MLDSA_CTRL.PARAM_SET already shifted into place
  int pk_dwords;
  int sig_dwords;
  int ctilde_dwords;
  int num_iters = 3;

  localparam bit [31:0] MLDSA_CTRL_KEYGEN_SIGN = 32'h0000_0004;
  localparam bit [31:0] MLDSA_CTRL_VERIFY      = 32'h0000_0003;
  localparam bit [31:0] MLDSA_CTRL_ZEROIZE     = 32'h0000_0008;

  bit ready;
  bit valid;

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task wait_ready();
    ready = 0;
    while (!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLDSA_STATUS");
      ready = data[0];
    end
  endtask

  // Polls for completion and turns MLDSA_STATUS.ERROR into a fatal, which would
  // otherwise show up as a silent hang or as a wall of data mismatches instead
  // of one clear message.
  virtual task wait_valid(string what);
    valid = 0;
    while (!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLDSA_STATUS");
      if (data[3]) begin
        `uvm_fatal("MLDSA_ERROR", $sformatf(
          "MLDSA_STATUS.ERROR asserted for %s %s (status=%0h).",
          ps_name, what, data))
      end
      valid = data[1];
    end
  endtask

  virtual task zeroize();
    data = MLDSA_CTRL_ZEROIZE;
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (zeroize)");
  endtask

  virtual task body();
    bit [31:0] rnd_seed [];
    bit [31:0] rnd_msg  [];
    bit [31:0] hw_sig   [];
    bit [31:0] hw_pk    [];
    bit [31:0] exp_vres [];

    reg_model.reset();
    data  = 0;
    ready = 0;
    valid = 0;
    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map is not initialized");
    end

    rnd_seed = new[8];
    rnd_msg  = new[16];

    for (int it = 0; it < num_iters; it++) begin
      `uvm_info("RND_KSV", $sformatf("%s randomized keygen+sign+verify iteration %0d", ps_name, it), UVM_LOW);

      wait_ready();

      foreach (rnd_seed[i]) begin
        if (!this.randomize(data)) `uvm_error("RANDOMIZE_FAIL", "Failed to randomize SEED");
        rnd_seed[i] = data;
      end
      foreach (rnd_msg[i]) begin
        if (!this.randomize(data)) `uvm_error("RANDOMIZE_FAIL", "Failed to randomize MSG");
        rnd_msg[i] = data;
      end

      foreach (reg_model.MLDSA_SEED[i]) begin
        reg_model.MLDSA_SEED[i].write(status, rnd_seed[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
      end
      foreach (reg_model.MLDSA_MSG[i]) begin
        reg_model.MLDSA_MSG[i].write(status, rnd_msg[i], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
      end

      // --- KEYGEN + SIGN ---
      data = MLDSA_CTRL_KEYGEN_SIGN | ps_ctrl;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (keygen+sign)");

      wait_valid("keygen+sign");

      hw_sig = new[sig_dwords];
      for (int j = 0; j < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); j++) begin
        reg_model.MLDSA_SIGNATURE.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", j))
        end else if (j < sig_dwords) begin
          hw_sig[j] = data;
        end else if (data !== 32'h0) begin
          `uvm_error("TAIL_NOT_ZERO", $sformatf(
            "%s iter %0d: MLDSA_SIGNATURE[%0d] is past the signature length but reads 0x%08h",
            ps_name, it, j, data))
        end
      end

      // A signature of all zeros would trivially satisfy the round trip below,
      // so make sure the hardware actually produced something.
      begin
        bit any_nz = 0;
        foreach (hw_sig[j]) if (hw_sig[j] !== 32'h0) any_nz = 1;
        if (!any_nz) begin
          `uvm_error("SIG_ALL_ZERO", $sformatf("%s iter %0d: MLDSA_SIGNATURE is entirely zero", ps_name, it))
        end
      end

      hw_pk = new[pk_dwords];
      for (int j = 0; j < reg_model.MLDSA_PUBKEY.m_mem.get_size(); j++) begin
        reg_model.MLDSA_PUBKEY.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", j))
        end else if (j < pk_dwords) begin
          hw_pk[j] = data;
        end else if (data !== 32'h0) begin
          `uvm_error("TAIL_NOT_ZERO", $sformatf(
            "%s iter %0d: MLDSA_PUBKEY[%0d] is past the key length but reads 0x%08h",
            ps_name, it, j, data))
        end
      end

      // KEYGEN+SIGN raises mldsa_keygen_signing_process, not
      // mldsa_keygen_process, so abr_ctrl's privkey lock is never released and
      // the private key must not leave the core.
      for (int j = 0; j < reg_model.MLDSA_PRIVKEY_OUT.m_mem.get_size(); j++) begin
        reg_model.MLDSA_PRIVKEY_OUT.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PRIVKEY_OUT[%0d]", j))
        end else if (data !== 32'h0) begin
          `uvm_error("PRIVKEY_NOT_LOCKED", $sformatf(
            "%s iter %0d: MLDSA_PRIVKEY_OUT[%0d] reads 0x%08h after keygen+sign, expected the privkey lock to force zero",
            ps_name, it, j, data))
        end
      end

      zeroize();

      // --- VERIFY the hardware's own signature back, internal mu ---
      wait_ready();

      for (int j = 0; j < pk_dwords; j++) begin
        reg_model.MLDSA_PUBKEY.m_mem.write(status, j, hw_pk[j], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PUBKEY[%0d]", j));
      end

      // The SIGNATURE aperture is not flat: the z and h bases move with the c~
      // width, so the parameter set has to be reselected before the signature
      // is written back. The zeroize above returned it to the category-5
      // default.
      data = ps_ctrl;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (param set)");

      for (int j = 0; j < sig_dwords; j++) begin
        reg_model.MLDSA_SIGNATURE.m_mem.write(status, j, hw_sig[j], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGNATURE[%0d]", j));
      end

      foreach (reg_model.MLDSA_MSG[j]) begin
        reg_model.MLDSA_MSG[j].write(status, rnd_msg[j], UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", j));
      end

      data = MLDSA_CTRL_VERIFY | ps_ctrl;
      reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (verify)");

      wait_valid("verify");

      // MLDSA_VERIFY_RES presents c~ zero extended to the category-5 register
      // width, so build the expectation the same way.
      exp_vres = new[$size(reg_model.MLDSA_VERIFY_RES)];
      foreach (exp_vres[j]) exp_vres[j] = (j < ctilde_dwords) ? hw_sig[j] : 32'h0;

      foreach (reg_model.MLDSA_VERIFY_RES[j]) begin
        reg_model.MLDSA_VERIFY_RES[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
        if (status != UVM_IS_OK) begin
          `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_VERIFY_RES[%0d]", j))
        end else if (j < ctilde_dwords) begin
          if (data !== hw_sig[j]) begin
            `uvm_error("VALIDATION_FAIL", $sformatf(
              "%s iter %0d: VERIFY_RES[%0d] does not reproduce the signature c~: actual=0x%08h, expected=0x%08h",
              ps_name, it, j, data, hw_sig[j]))
          end
        end else if (data !== 32'h0) begin
          `uvm_error("CTILDE_TAIL_NOT_ZERO", $sformatf(
            "%s iter %0d: MLDSA_VERIFY_RES[%0d] is above the c~ length but reads 0x%08h",
            ps_name, it, j, data))
        end
      end

      check_verify_pass_ref(1, exp_vres);

      zeroize();
    end

    `uvm_info("RND_KSV", $sformatf("%s randomized keygen+sign+verify completed (%0d iterations)", ps_name, num_iters), UVM_LOW);

  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
