//----------------------------------------------------------------------
// ACVP ML-DSA-87 Rejection Path KAT Test
//
// Tests Sign_internal() rejection paths (z, r0, h) using ACVP Table 1
// vectors and Chris Celi's corrected vectors from NIST PQC Forum.
// Uses EXTERNAL_MU mode since ACVP M' is passed directly to Sign_internal.
//----------------------------------------------------------------------

class ML_DSA_ACVP_rejection_KATs_test extends test_top;

  `uvm_component_utils(ML_DSA_ACVP_rejection_KATs_test);

  bit disable_scrboard_from_test;
  bit disable_pred_from_test;

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    mldsa_bench_sequence_base::type_id::set_type_override(ML_DSA_ACVP_rejection_KATs_sequence::get_type());
    super.build_phase(phase);

    disable_scrboard_from_test = 1;
    disable_pred_from_test = 1;

    uvm_config_db#(bit)::set(null, "*", "disable_scrboard_from_test", disable_scrboard_from_test);
    uvm_config_db#(bit)::set(null, "*", "disable_pred_from_test", disable_pred_from_test);
  endfunction

  virtual task main_phase(uvm_phase phase);
    ML_DSA_ACVP_rejection_KATs_sequence seq;
    seq = ML_DSA_ACVP_rejection_KATs_sequence::type_id::create("ML_DSA_ACVP_rejection_KATs_sequence");
    seq.start(null);
  endtask

endclass
