//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION: ML-DSA-87 randomized keygen + sign + verify self check.
// Sets MLDSA_CTRL.PARAM_SET = 2'b00 and runs the parameter-set agnostic body in
// ML_DSA_randomized_kg_sign_verify_base_sequence over random seeds and random
// messages. See that file for the rationale.
//
//----------------------------------------------------------------------

class ML_DSA_87_randomized_kg_sign_verify_sequence extends ML_DSA_randomized_kg_sign_verify_base_sequence;

  `uvm_object_utils(ML_DSA_87_randomized_kg_sign_verify_sequence);

  function new(string name = "");
    super.new(name);
    ps_name       = "ML-DSA-87";
    ps_ctrl       = 32'h0000_0000;
    pk_dwords     = 648;
    sig_dwords    = 1157;
    ctilde_dwords = 16;
    num_iters     = 3;
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
