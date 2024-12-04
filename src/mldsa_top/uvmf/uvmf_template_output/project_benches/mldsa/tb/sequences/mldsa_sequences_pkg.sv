//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: This package includes all high level sequence classes used 
//     in the environment.  These include utility sequences and top
//     level sequences.
//
// CONTAINS:
//     -<mldsa_sequence_base>
//     -<example_derived_test_sequence>
//
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//

package mldsa_sequences_pkg;
  import uvm_pkg::*;
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import mldsa_parameters_pkg::*;
  import mldsa_env_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
  import mldsa_reg_model_top_pkg::*;
  `include "uvm_macros.svh"

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  `include "src/mldsa_bench_sequence_base.svh"
  `include "src/register_test_sequence.svh"
  `include "src/example_derived_test_sequence.svh"
  `include "src/ML_DSA_randomized_key_gen_sequence.svh"
  `include "src/ML_DSA_randomized_key_gen_and_sign_sequence.svh"
  `include "src/ML_DSA_randomized_early_run_sequence.svh"
  `include "src/ML_DSA_randomized_zeroize_sequence.svh"
  `include "src/ML_DSA_randomized_sign_gen_sequence.svh"
  `include "src/ML_DSA_randomized_verif_sequence.svh"
  `include "src/ML_DSA_randomized_verif_fail_sequence.svh"
  `include "src/ML_DSA_randomized_reset_sequence.svh"
  `include "src/ML_DSA_randomized_all_sequence.svh"
  `include "src/ML_DSA_keygen_KATs_sequence.svh"
  `include "src/ML_DSA_keygen_signing_KATs_sequence.svh"
  `include "src/ML_DSA_verif_KATs_sequence.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the sequence package.  Be sure to place
  //    the new sequence after any base sequences of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

