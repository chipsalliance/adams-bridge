//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION: Randomized parameter set and algorithm switching.
//
// Why this exists
// ---------------
// Every other sequence in the bench pins one algorithm and one parameter set
// for its whole run. That leaves one class of bug completely uncovered: state
// that is loaded when a command starts and is *not* reloaded when the next
// command starts at a different parameter set. A latched k/l, a tau that is
// only refreshed on reset, an aperture base that is captured once, a sampler
// mode register that keeps its previous value - any of these would pass every
// per set test in the bench and still break the moment a driver interleaves
// two security levels, which is exactly what a real integration does when one
// agent asks for ML-DSA-65 signatures while another asks for ML-KEM-512
// decapsulation on the same core.
//
// The sequence issues a single reg_model.reset() at the start and then never
// resets again. Every parameter set change after that has to be absorbed by
// the command time PARAM_SET latch in abr_ctrl alone.
//
// What it runs
//   num_units (default 3) self checking units, back to back, each at a
//   randomly chosen (algorithm, parameter set) pair, constrained so that
//   consecutive units never repeat the same pair - every boundary in the chain
//   is a real switch. Three is the shortest chain that contains two switches,
//   which keeps one run cheap enough for the nightly randomized regression to
//   repeat it a thousand times with a different seed each time; the coverage
//   comes from the iteration count, not from the length of one run.
//
// Every unit is self checking, so a switching bug shows up as a data mismatch
// and not as a silent pass:
//   ML-DSA unit - keygen+sign over a random seed and a random message, then the
//                 signature the hardware produced must verify back and
//                 MLDSA_VERIFY_RES must reproduce c~ with a zero tail
//   ML-KEM unit - keygen, encapsulate under the generated key, then
//                 keygen/decaps must recover the same shared secret
// Both also require every parameter set dependent aperture to read zero past
// its active length, and both guard against a trivially passing all zero
// result.
//
// Note that the check inside a unit already spans a switch: the unit's verify
// or decaps runs after the previous unit left the core at a different
// (algorithm, parameter set), so any state that leaked forward from it lands on
// a checked operation.
//
// The one subtlety the sequence encodes, and the reason a naive mixed test
// fails spuriously: PARAM_SET has to be reselected with CTRL = 0 after every
// zeroize and before any aperture writeback. None of the MLDSA_SIGNATURE, the
// MLKEM_ENCAPS_KEY or the MLKEM_CIPHERTEXT apertures is flat, and zeroize
// returns the latch to category 5.
//
//----------------------------------------------------------------------

class ML_DSA_MLKEM_param_set_mix_sequence extends mldsa_bench_sequence_base;

  `uvm_object_utils(ML_DSA_MLKEM_param_set_mix_sequence);

  // Number of back to back units in one run. Overridable with
  // +ABR_PS_MIX_UNITS=<n>.
  int num_units = 3;

  localparam bit [31:0] DSA_KEYGEN_SIGN = 32'h0000_0004;
  localparam bit [31:0] DSA_VERIFY      = 32'h0000_0003;
  localparam bit [31:0] DSA_ZEROIZE     = 32'h0000_0008;

  localparam bit [31:0] KEM_KEYGEN        = 32'h0000_0001;
  localparam bit [31:0] KEM_ENCAPS        = 32'h0000_0002;
  localparam bit [31:0] KEM_KEYGEN_DECAPS = 32'h0000_0004;
  localparam bit [31:0] KEM_ZEROIZE       = 32'h0000_0008;

  // Index 0/1/2 = category 5 / category 2 / category 3 for both algorithms, so
  // the same index can be reused for messages and for the tables below.
  string     dsa_name [3];
  bit [31:0] dsa_ps   [3];   // MLDSA_CTRL.PARAM_SET already shifted into place
  int        dsa_pk   [3];
  int        dsa_sig  [3];
  int        dsa_ct   [3];

  string     kem_name [3];
  bit [31:0] kem_ps   [3];   // MLKEM_CTRL.PARAM_SET already shifted into place
  int        kem_ek   [3];
  int        kem_dk   [3];
  int        kem_ctxt [3];

  bit ready;
  bit valid;

  function new(string name = "");
    super.new(name);

    dsa_name = '{"ML-DSA-87", "ML-DSA-44", "ML-DSA-65"};
    dsa_ps   = '{32'h0000_0000, 32'h0000_0080, 32'h0000_0100};
    dsa_pk   = '{648, 328, 488};
    dsa_sig  = '{1157, 605, 828};
    dsa_ct   = '{16, 8, 12};

    kem_name = '{"ML-KEM-1024", "ML-KEM-512", "ML-KEM-768"};
    kem_ps   = '{32'h0000_0000, 32'h0000_0010, 32'h0000_0020};
    kem_ek   = '{392, 200, 296};
    kem_dk   = '{792, 408, 600};
    kem_ctxt = '{392, 192, 272};
  endfunction

  //--------------------------------------------------------------------
  // Status polling
  //--------------------------------------------------------------------

  virtual task dsa_wait_ready();
    ready = 0;
    while (!ready) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLDSA_STATUS");
      ready = data[0];
    end
  endtask

  // A command issued at a parameter set that was not enabled at elaboration
  // aborts through MLDSA_STATUS.ERROR. Turning that into one clear fatal beats
  // letting it surface as a hang or as a wall of data mismatches.
  virtual task dsa_wait_valid(string what);
    valid = 0;
    while (!valid) begin
      reg_model.MLDSA_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLDSA_STATUS");
      if (data[3]) begin
        `uvm_fatal("MLDSA_ERROR", $sformatf(
          "MLDSA_STATUS.ERROR asserted for %s (status=%0h). Parameter set likely not enabled at elaboration.",
          what, data))
      end
      valid = data[1];
    end
  endtask

  virtual task dsa_zeroize();
    data = DSA_ZEROIZE;
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (zeroize)");
  endtask

  virtual task kem_wait_ready();
    ready = 0;
    while (!ready) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLKEM_STATUS");
      ready = data[0];
    end
  endtask

  virtual task kem_wait_valid(string what);
    valid = 0;
    while (!valid) begin
      reg_model.MLKEM_STATUS.read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", "Failed to read MLKEM_STATUS");
      if (data[3]) begin
        `uvm_fatal("MLKEM_ERROR", $sformatf(
          "MLKEM_STATUS.ERROR asserted for %s (status=%0h). Parameter set likely not enabled at elaboration.",
          what, data))
      end
      valid = data[1];
    end
  endtask

  virtual task kem_zeroize();
    data = KEM_ZEROIZE;
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (zeroize)");
  endtask

  virtual task rand_words(ref bit [31:0] a []);
    foreach (a[i]) begin
      if (!this.randomize(data)) `uvm_error("RANDOMIZE_FAIL", "Failed to randomize a data word");
      a[i] = data;
    end
  endtask

  //--------------------------------------------------------------------
  // ML-DSA
  //--------------------------------------------------------------------

  // Runs KEYGEN+SIGN at set s over the supplied seed and message and returns
  // the public key and signature truncated to that set's FIPS 204 lengths.
  // Leaves the core zeroized.
  virtual task dsa_keygen_sign(int s,
                               ref bit [31:0] seed [],
                               ref bit [31:0] msg  [],
                               ref bit [31:0] pk   [],
                               ref bit [31:0] sig  []);
    bit any_nz;

    dsa_wait_ready();

    foreach (reg_model.MLDSA_SEED[i]) begin
      reg_model.MLDSA_SEED[i].write(status, seed[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SEED[%0d]", i));
    end
    foreach (reg_model.MLDSA_MSG[i]) begin
      reg_model.MLDSA_MSG[i].write(status, msg[i], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", i));
    end

    data = DSA_KEYGEN_SIGN | dsa_ps[s];
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (keygen+sign)");

    dsa_wait_valid($sformatf("%s keygen+sign", dsa_name[s]));

    sig = new[dsa_sig[s]];
    for (int j = 0; j < reg_model.MLDSA_SIGNATURE.m_mem.get_size(); j++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_SIGNATURE[%0d]", j))
      end else if (j < dsa_sig[s]) begin
        sig[j] = data;
      end else if (data !== 32'h0) begin
        `uvm_error("TAIL_NOT_ZERO", $sformatf(
          "%s: MLDSA_SIGNATURE[%0d] is past the signature length but reads 0x%08h", dsa_name[s], j, data))
      end
    end

    // An all zero signature would satisfy the round trip trivially.
    any_nz = 0;
    foreach (sig[j]) if (sig[j] !== 32'h0) any_nz = 1;
    if (!any_nz) `uvm_error("SIG_ALL_ZERO", $sformatf("%s: MLDSA_SIGNATURE is entirely zero", dsa_name[s]));

    pk = new[dsa_pk[s]];
    for (int j = 0; j < reg_model.MLDSA_PUBKEY.m_mem.get_size(); j++) begin
      reg_model.MLDSA_PUBKEY.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PUBKEY[%0d]", j))
      end else if (j < dsa_pk[s]) begin
        pk[j] = data;
      end else if (data !== 32'h0) begin
        `uvm_error("TAIL_NOT_ZERO", $sformatf(
          "%s: MLDSA_PUBKEY[%0d] is past the key length but reads 0x%08h", dsa_name[s], j, data))
      end
    end

    // KEYGEN+SIGN never releases abr_ctrl's private key lock.
    for (int j = 0; j < reg_model.MLDSA_PRIVKEY_OUT.m_mem.get_size(); j++) begin
      reg_model.MLDSA_PRIVKEY_OUT.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_PRIVKEY_OUT[%0d]", j))
      end else if (data !== 32'h0) begin
        `uvm_error("PRIVKEY_NOT_LOCKED", $sformatf(
          "%s: MLDSA_PRIVKEY_OUT[%0d] reads 0x%08h after keygen+sign", dsa_name[s], j, data))
      end
    end

    dsa_zeroize();
  endtask

  // Writes the supplied public key, signature and message back and runs VERIFY
  // at set s. Leaves the core zeroized.
  virtual task dsa_verify(int s,
                          ref bit [31:0] msg [],
                          ref bit [31:0] pk  [],
                          ref bit [31:0] sig []);
    bit [31:0] exp_vres [];

    dsa_wait_ready();

    for (int j = 0; j < dsa_pk[s]; j++) begin
      reg_model.MLDSA_PUBKEY.m_mem.write(status, j, pk[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_PUBKEY[%0d]", j));
    end

    // The SIGNATURE aperture is not flat - the z and h bases move with the c~
    // width - so the parameter set has to be reselected before the signature is
    // written back. CTRL = 0 with PARAM_SET set selects the aperture without
    // starting an operation. This matters more here than in the single set
    // sequences: the preceding operation may have been at a different set, or a
    // different algorithm entirely.
    data = dsa_ps[s];
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (param set)");

    for (int j = 0; j < dsa_sig[s]; j++) begin
      reg_model.MLDSA_SIGNATURE.m_mem.write(status, j, sig[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_SIGNATURE[%0d]", j));
    end

    foreach (reg_model.MLDSA_MSG[j]) begin
      reg_model.MLDSA_MSG[j].write(status, msg[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLDSA_MSG[%0d]", j));
    end

    data = DSA_VERIFY | dsa_ps[s];
    reg_model.MLDSA_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLDSA_CTRL (verify)");

    dsa_wait_valid($sformatf("%s verify", dsa_name[s]));

    // MLDSA_VERIFY_RES presents c~ zero extended to the category-5 register
    // width, so build the expectation the same way.
    exp_vres = new[$size(reg_model.MLDSA_VERIFY_RES)];
    foreach (exp_vres[j]) exp_vres[j] = (j < dsa_ct[s]) ? sig[j] : 32'h0;

    foreach (reg_model.MLDSA_VERIFY_RES[j]) begin
      reg_model.MLDSA_VERIFY_RES[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLDSA_VERIFY_RES[%0d]", j))
      end else if (j < dsa_ct[s]) begin
        if (data !== sig[j]) begin
          `uvm_error("VALIDATION_FAIL", $sformatf(
            "%s: VERIFY_RES[%0d] does not reproduce c~: actual=0x%08h, expected=0x%08h",
            dsa_name[s], j, data, sig[j]))
        end
      end else if (data !== 32'h0) begin
        `uvm_error("CTILDE_TAIL_NOT_ZERO", $sformatf(
          "%s: MLDSA_VERIFY_RES[%0d] is above the c~ length but reads 0x%08h", dsa_name[s], j, data))
      end
    end

    check_verify_pass_ref(1, exp_vres);

    dsa_zeroize();
  endtask

  // One self contained ML-DSA unit: fresh random secret and message, sign,
  // verify back.
  virtual task dsa_unit(int s);
    bit [31:0] seed [];
    bit [31:0] msg  [];
    bit [31:0] pk   [];
    bit [31:0] sig  [];

    `uvm_info("PS_MIX", $sformatf("unit: %s keygen+sign+verify", dsa_name[s]), UVM_LOW);

    seed = new[8];
    msg  = new[16];
    rand_words(seed);
    rand_words(msg);

    dsa_keygen_sign(s, seed, msg, pk, sig);
    dsa_verify(s, msg, pk, sig);
  endtask

  //--------------------------------------------------------------------
  // ML-KEM
  //--------------------------------------------------------------------

  // One self contained ML-KEM unit at set y: keygen, encapsulate under the
  // generated encapsulation key, then keygen/decaps and require the shared
  // secret to match.
  virtual task kem_unit(int y);
    bit [31:0] seed_d [];
    bit [31:0] seed_z [];
    bit [31:0] msg    [];
    bit [31:0] ek     [];
    bit [31:0] ct     [];
    bit [31:0] ss     [];
    bit any_nz;

    `uvm_info("PS_MIX", $sformatf("unit: %s keygen+encaps+decaps", kem_name[y]), UVM_LOW);

    seed_d = new[8];
    seed_z = new[8];
    msg    = new[8];
    ss     = new[8];
    ek     = new[kem_ek[y]];
    ct     = new[kem_ctxt[y]];

    rand_words(seed_d);
    rand_words(seed_z);
    rand_words(msg);

    // --- KEYGEN ---
    kem_wait_ready();

    foreach (reg_model.MLKEM_SEED_D[j]) begin
      reg_model.MLKEM_SEED_D[j].write(status, seed_d[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_SEED_D[%0d]", j));
    end
    foreach (reg_model.MLKEM_SEED_Z[j]) begin
      reg_model.MLKEM_SEED_Z[j].write(status, seed_z[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_SEED_Z[%0d]", j));
    end

    data = KEM_KEYGEN | kem_ps[y];
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (keygen)");

    kem_wait_valid($sformatf("%s keygen", kem_name[y]));

    for (int j = 0; j < reg_model.MLKEM_ENCAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_ENCAPS_KEY[%0d]", j))
      end else if (j < kem_ek[y]) begin
        ek[j] = data;
      end else if (data !== 32'h0) begin
        `uvm_error("TAIL_NOT_ZERO", $sformatf(
          "%s: MLKEM_ENCAPS_KEY[%0d] past the active key length reads 0x%08h", kem_name[y], j, data))
      end
    end

    // The decapsulation key is not retained - the decaps step below regenerates
    // it from the same seeds - but its tail is still checked here because the
    // aperture length is parameter set dependent.
    for (int j = 0; j < reg_model.MLKEM_DECAPS_KEY.m_mem.get_size(); j++) begin
      reg_model.MLKEM_DECAPS_KEY.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_DECAPS_KEY[%0d]", j))
      end else if (j >= kem_dk[y] && data !== 32'h0) begin
        `uvm_error("TAIL_NOT_ZERO", $sformatf(
          "%s: MLKEM_DECAPS_KEY[%0d] past the active key length reads 0x%08h", kem_name[y], j, data))
      end
    end

    any_nz = 0;
    foreach (ek[j]) if (ek[j] !== 32'h0) any_nz = 1;
    if (!any_nz) `uvm_error("EK_ALL_ZERO", $sformatf("%s: MLKEM_ENCAPS_KEY is entirely zero", kem_name[y]));

    kem_zeroize();

    // --- ENCAPS ---
    kem_wait_ready();

    // The encapsulation key aperture splits ByteEncode12(t_hat) in memory from
    // the rho tail in flops using the active set, so the set has to be
    // reselected after the zeroize and before ek is written back.
    data = kem_ps[y];
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (param set)");

    for (int j = 0; j < kem_ek[y]; j++) begin
      reg_model.MLKEM_ENCAPS_KEY.m_mem.write(status, j, ek[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_ENCAPS_KEY[%0d]", j));
    end

    for (int j = 0; j < reg_model.MLKEM_MSG.m_mem.get_size(); j++) begin
      reg_model.MLKEM_MSG.m_mem.write(status, j, msg[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_MSG[%0d]", j));
    end

    data = KEM_ENCAPS | kem_ps[y];
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (encaps)");

    kem_wait_valid($sformatf("%s encaps", kem_name[y]));

    foreach (reg_model.MLKEM_SHARED_KEY[j]) begin
      reg_model.MLKEM_SHARED_KEY[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_SHARED_KEY[%0d]", j));
      ss[j] = data;
    end

    any_nz = 0;
    foreach (ss[j]) if (ss[j] !== 32'h0) any_nz = 1;
    if (!any_nz) `uvm_error("SS_ALL_ZERO", $sformatf("%s: encaps shared key is entirely zero", kem_name[y]));

    for (int j = 0; j < reg_model.MLKEM_CIPHERTEXT.m_mem.get_size(); j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.read(status, j, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_CIPHERTEXT[%0d]", j))
      end else if (j < kem_ctxt[y]) begin
        ct[j] = data;
      end else if (data !== 32'h0) begin
        `uvm_error("TAIL_NOT_ZERO", $sformatf(
          "%s: MLKEM_CIPHERTEXT[%0d] past the active ciphertext length reads 0x%08h", kem_name[y], j, data))
      end
    end

    kem_zeroize();

    // --- KEYGEN/DECAPS ---
    kem_wait_ready();

    foreach (reg_model.MLKEM_SEED_D[j]) begin
      reg_model.MLKEM_SEED_D[j].write(status, seed_d[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_SEED_D[%0d]", j));
    end
    foreach (reg_model.MLKEM_SEED_Z[j]) begin
      reg_model.MLKEM_SEED_Z[j].write(status, seed_z[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_SEED_Z[%0d]", j));
    end

    // The ciphertext aperture skips the padding between c1 and c2 using the
    // active set, so the set has to be reselected before the writeback.
    data = kem_ps[y];
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (param set)");

    for (int j = 0; j < kem_ctxt[y]; j++) begin
      reg_model.MLKEM_CIPHERTEXT.m_mem.write(status, j, ct[j], UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) `uvm_error("REG_WRITE", $sformatf("Failed to write MLKEM_CIPHERTEXT[%0d]", j));
    end

    data = KEM_KEYGEN_DECAPS | kem_ps[y];
    reg_model.MLKEM_CTRL.write(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
    if (status != UVM_IS_OK) `uvm_error("REG_WRITE", "Failed to write MLKEM_CTRL (keygen/decaps)");

    kem_wait_valid($sformatf("%s keygen/decaps", kem_name[y]));

    foreach (reg_model.MLKEM_SHARED_KEY[j]) begin
      reg_model.MLKEM_SHARED_KEY[j].read(status, data, UVM_FRONTDOOR, reg_model.default_map, this);
      if (status != UVM_IS_OK) begin
        `uvm_error("REG_READ", $sformatf("Failed to read MLKEM_SHARED_KEY[%0d]", j))
      end else if (data !== ss[j]) begin
        `uvm_error("VALIDATION_FAIL", $sformatf(
          "%s: shared key mismatch at index %0d: expected 0x%08h, got 0x%08h",
          kem_name[y], j, ss[j], data))
      end
    end

    kem_zeroize();
  endtask

  //--------------------------------------------------------------------
  // Body
  //--------------------------------------------------------------------

  virtual task body();
    int alg;       // 0 = ML-DSA, 1 = ML-KEM
    int set_idx;
    int prev_alg;
    int prev_set;

    // Nightly regression runs this test with a fresh seed per iteration, so the
    // coverage comes from the number of iterations, not from the length of one
    // run. Three units is deliberately short: it is the smallest chain that
    // contains two switches, and it keeps a single run cheap enough to repeat a
    // thousand times a night. Overridable for a longer soak.
    if ($value$plusargs("ABR_PS_MIX_UNITS=%d", num_units)) begin
      `uvm_info("PS_MIX", $sformatf("num_units overridden to %0d by plusarg", num_units), UVM_LOW);
    end

    reg_model.reset();
    data  = 0;
    ready = 0;
    valid = 0;
    #400;

    if (reg_model.default_map == null) begin
      `uvm_fatal("MAP_ERROR", "mldsa_uvm_rm.default_map is not initialized");
    end

    // Seed the "previous" pair from the reset state of the two latches, which
    // is category 5 for both algorithms, so even the first unit is a switch
    // unless it happens to pick ML-DSA-87.
    prev_alg = 0;
    prev_set = 0;

    for (int step = 0; step < num_units; step++) begin
      // Consecutive units never repeat the same (algorithm, parameter set)
      // pair, so every boundary in the chain is a real switch.
      do begin
        alg     = $urandom_range(1, 0);
        set_idx = $urandom_range(2, 0);
      end while (alg == prev_alg && set_idx == prev_set);

      `uvm_info("PS_MIX", $sformatf("unit %0d of %0d", step, num_units), UVM_LOW);

      if (alg == 0) dsa_unit(set_idx);
      else          kem_unit(set_idx);

      prev_alg = alg;
      prev_set = set_idx;
    end

    `uvm_info("PS_MIX", $sformatf(
      "parameter set mix completed: %0d back to back units, no reset after the first",
      num_units), UVM_LOW);

  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
