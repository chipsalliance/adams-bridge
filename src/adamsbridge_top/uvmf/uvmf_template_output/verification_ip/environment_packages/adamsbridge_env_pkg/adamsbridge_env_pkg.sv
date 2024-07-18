//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//     
// PACKAGE: This file defines all of the files contained in the
//    environment package that will run on the host simulator.
//
// CONTAINS:
//     - <adamsbridge_configuration.svh>
//     - <adamsbridge_environment.svh>
//     - <adamsbridge_env_sequence_base.svh>
//     - <adamsbridge_predictor.svh>
//     - <adamsbridge_scoreboard.svh>
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
package adamsbridge_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import uvmf_base_pkg::*;
  import mvc_pkg::*;
  import mgc_ahb_v2_0_pkg::*;
  import rw_txn_pkg::*;
  import adamsbridge_reg_model_top_pkg::*;
  import qvip_ahb_lite_slave_pkg::*;
  import qvip_ahb_lite_slave_params_pkg::*;
 
  `uvm_analysis_imp_decl(_ahb_slave_0_ae)
  `uvm_analysis_imp_decl(_actual_ahb_analysis_export)
  `uvm_analysis_imp_decl(_expected_ahb_analysis_export)

  // pragma uvmf custom package_imports_additional begin
  // pragma uvmf custom package_imports_additional end

  // Parameters defined as HVL parameters

  `include "src/adamsbridge_env_typedefs.svh"
  `include "src/adamsbridge_env_configuration.svh"
  `include "src/adamsbridge_predictor.svh"
  `include "src/adamsbridge_scoreboard.svh"
  `include "src/adamsbridge_environment.svh"
  `include "src/adamsbridge_env_sequence_base.svh"

  // pragma uvmf custom package_item_additional begin
  // UVMF_CHANGE_ME : When adding new environment level sequences to the src directory
  //    be sure to add the sequence file here so that it will be
  //    compiled as part of the environment package.  Be sure to place
  //    the new sequence after any base sequence of the new sequence.
  // pragma uvmf custom package_item_additional end

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

