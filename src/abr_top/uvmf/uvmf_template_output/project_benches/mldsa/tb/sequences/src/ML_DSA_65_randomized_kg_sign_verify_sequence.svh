//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION: ML-DSA-65 randomized keygen + sign + verify self check.
// Sets MLDSA_CTRL.PARAM_SET = 2'b10 and runs the parameter-set agnostic body in
// ML_DSA_randomized_kg_sign_verify_base_sequence over random seeds and random
// messages. See that file for the rationale.
//
//----------------------------------------------------------------------

class ML_DSA_65_randomized_kg_sign_verify_sequence extends ML_DSA_randomized_kg_sign_verify_base_sequence;

  `uvm_object_utils(ML_DSA_65_randomized_kg_sign_verify_sequence);

  function new(string name = "");
    super.new(name);
    ps_name       = "ML-DSA-65";
    ps_ctrl       = 32'h0000_0100;
    pk_dwords     = 488;
    sig_dwords    = 828;
    ctilde_dwords = 12;
    num_iters     = 3;
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
