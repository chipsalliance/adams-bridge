//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//   actual_ahb_analysis_export receives transactions of type  ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH)  
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//


class mldsa_scoreboard #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( mldsa_scoreboard #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;

  
  // Instantiate the analysis exports
  uvm_analysis_imp_actual_ahb_analysis_export #(mvc_sequence_item_base, mldsa_scoreboard #(
    .CONFIG_T(CONFIG_T),
    .BASE_T(BASE_T)
    )
) actual_ahb_analysis_export;


 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_expected_ahb_analysis_export #(mvc_sequence_item_base, mldsa_scoreboard #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) expected_ahb_analysis_export;


  // pragma uvmf custom class_item_additional begin
    // Use Queues for AHB/APB txns since there is no get_key() method
  ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                            ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                            ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                            ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                            ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                            ahb_lite_slave_0_params::AHB_RDATA_WIDTH)     ahb_expected_q       [$];

  ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                            ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                            ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                            ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                            ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                            ahb_lite_slave_0_params::AHB_RDATA_WIDTH)     ahb_actual_q       [$];

  
  ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS,
                            ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS,
                            ahb_lite_slave_0_params::AHB_NUM_SLAVES,
                            ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH,
                            ahb_lite_slave_0_params::AHB_WDATA_WIDTH,
                            ahb_lite_slave_0_params::AHB_RDATA_WIDTH)     ahb_expected_verif_q       [$];


  // pragma uvmf custom class_item_additional end
  bit expect_verif_failure = 0;
  bit disable_scrboard_from_test = 0;
  bit expect_verif_pass_after_failure = 0;
  int transaction_count = 0;
  int verif_transaction_count = 0;
  int match_count = 0;
  int mismatch_count = 0;
  int verif_unexpected_match_count = 0;
  int nothing_to_compare_against_count = 0;
  event entry_received;
  mldsa_reg_model_top scbr_mldsa_rm;
  uvm_reg_map scbr_mldsa_map; // Block map

  // FUNCTION: new
  function new(string name, uvm_component parent);
     super.new(name,parent);
  // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    actual_ahb_analysis_export = new("actual_ahb_analysis_export", this);
    expected_ahb_analysis_export = new("expected_ahb_analysis_export", this);
  // pragma uvmf custom build_phase begin

    if (!uvm_config_db#(bit)::get(this, "", "expect_verif_failure", expect_verif_failure)) begin
      expect_verif_failure = '0; // default value
    end
    if (!uvm_config_db#(bit)::get(this, "", "expect_verif_pass_after_failure", expect_verif_pass_after_failure)) begin
      expect_verif_pass_after_failure = '0; // default value
    end

    if (!uvm_config_db#(bit)::get(this, "", "disable_scrboard_from_test", disable_scrboard_from_test)) begin
      disable_scrboard_from_test = '0; // default value
    end

    `uvm_info("SCOREBOARD", $sformatf("expect_verif_failure to be used: %d", expect_verif_failure), UVM_LOW)
    `uvm_info("SCOREBOARD", $sformatf("expect_verif_pass_after_failure to be used: %d", expect_verif_pass_after_failure), UVM_LOW)
    `uvm_info("SCOREBOARD", $sformatf("disable_scrboard_from_test to be used: %d", disable_scrboard_from_test), UVM_LOW)
    // Instantiate the register model
    // scbr_mldsa_rm = mldsa_reg_model_top::type_id::create("scbr_mldsa_rm", this);
    scbr_mldsa_rm = configuration.mldsa_rm;
    scbr_mldsa_map = scbr_mldsa_rm.get_default_map();
  // pragma uvmf custom build_phase end
  endfunction

  // FUNCTION: write_actual_ahb_analysis_export
  // Transactions received through actual_ahb_analysis_export initiate the execution of this function.
  // This function performs prediction of DUT output values based on DUT input, configuration and state
  // FUNCTION: write_actual_ahb_analysis_export
  // QVIP transactions received through actual_ahb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_actual_ahb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom actual_ahb_analysis_export_scoreboard begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t;
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t_exp;
    bit txn_eq;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_AHB","Cast from mvc_sequence_item_base to ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) in write_actual_ahb_analysis_export failed!")
    end
    // `uvm_info("SCBD_AHB", "Transaction Received through actual_ahb_analysis_export", UVM_MEDIUM)
    // `uvm_info("SCBD_AHB",{"            Data: ",t.convert2string()}, UVM_HIGH)

    if (t.RnW == 1'b0 && !disable_scrboard_from_test) begin
      // `uvm_info("SCBD_AHB", "Transaction is a read", UVM_MEDIUM)
      // Check if the transaction address matches any of the registers to be skipped
      if ((t.address >= scbr_mldsa_rm.MLDSA_NAME[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_NAME[$size(scbr_mldsa_rm.MLDSA_NAME)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_VERSION[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_VERSION[$size(scbr_mldsa_rm.MLDSA_VERSION)-1].get_address(scbr_mldsa_map)) ||
        (t.address == scbr_mldsa_rm.MLDSA_CTRL.get_address(scbr_mldsa_map)) ||
        (t.address == scbr_mldsa_rm.MLDSA_STATUS.get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_ENTROPY[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_ENTROPY[$size(scbr_mldsa_rm.MLDSA_ENTROPY)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_SEED[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_SEED[$size(scbr_mldsa_rm.MLDSA_SEED)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_SIGN_RND[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_SIGN_RND[$size(scbr_mldsa_rm.MLDSA_SIGN_RND)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_MSG[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_MSG[$size(scbr_mldsa_rm.MLDSA_MSG)-1].get_address(scbr_mldsa_map))
      ) begin
        `uvm_info("SCBD_AHB", $sformatf("Skipping register access in scoreboard at address: 0x%x", t.address), UVM_HIGH)
      end
      else if ( (t.address >= scbr_mldsa_rm.MLDSA_VERIFY_RES[0].get_address(scbr_mldsa_map) &&
                t.address <= scbr_mldsa_rm.MLDSA_VERIFY_RES[$size(scbr_mldsa_rm.MLDSA_VERIFY_RES)-1].get_address(scbr_mldsa_map)) &&
                expect_verif_failure &&
                ahb_expected_verif_q.size() > 0)
      begin
        t_exp = ahb_expected_verif_q.pop_front();
        txn_eq = (t_exp.data[0][31:0] == t.data[0][31:0]);
        // `uvm_info("SCBD_AHB",{"           Poped Data: ",t_exp.convert2string()}, UVM_MEDIUM)
        if ((t_exp.data[0][31:0] == t.data[0][31:0])) begin
            verif_unexpected_match_count++;
            // `uvm_info ("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} matches expected",t.address,t.data[0],t.RnW), UVM_MEDIUM)
        end
        verif_transaction_count++;
        if (verif_transaction_count==16 && verif_unexpected_match_count==16) begin
          verif_transaction_count = 0;
          `uvm_error("SCBD_AHB", $sformatf("Although the verification failure is expected, the verif result matches with the successful verif output"))
        end
        else if (verif_transaction_count==16 && verif_unexpected_match_count<16) begin
          verif_transaction_count = 0;
        end
      end
      else if ( (t.address >= scbr_mldsa_rm.MLDSA_VERIFY_RES[0].get_address(scbr_mldsa_map) &&
                t.address <= scbr_mldsa_rm.MLDSA_VERIFY_RES[$size(scbr_mldsa_rm.MLDSA_VERIFY_RES)-1].get_address(scbr_mldsa_map)) &&
                expect_verif_pass_after_failure &&
                ahb_expected_verif_q.size() > 0)
      begin
        t_exp = ahb_expected_verif_q.pop_front();
        txn_eq = (t_exp.data[0][31:0] == t.data[0][31:0]);
        // `uvm_info("SCBD_AHB",{"           Poped Data: ",t_exp.convert2string()}, UVM_MEDIUM)
        if ((t_exp.data[0][31:0] == t.data[0][31:0])) begin
            verif_unexpected_match_count++;
            // `uvm_info ("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} matches expected",t.address,t.data[0],t.RnW), UVM_LOW)
        end
        verif_transaction_count++;
        if (verif_transaction_count==16 && verif_unexpected_match_count == 16) begin
          verif_transaction_count = 0;
          `uvm_error("SCBD_AHB", $sformatf("Although the verification failure is expected, the first verif result matches with the successful verif output"))
        end
        else if (verif_transaction_count == 32 && verif_unexpected_match_count != 16) begin
          verif_transaction_count = 0;
          `uvm_error("SCBD_AHB", $sformatf("Although the verification failure is NOT expected, the second verif result does not match with the successful verif output"))
        end
      end
      else if (ahb_expected_q.size() > 0) begin
          t_exp = ahb_expected_q.pop_front();
          txn_eq = (t_exp.data[0][31:0] == t.data[0][31:0]);
          // `uvm_info("SCBD_AHB",{"           Poped Data: ",t_exp.convert2string()}, UVM_MEDIUM)
          if ((t_exp.data[0][31:0] == t.data[0][31:0])) begin
              match_count++;
              // `uvm_info ("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} matches expected",t.address,t.data[0],t.RnW), UVM_MEDIUM)
          end
          else begin
              mismatch_count++;
              `uvm_error("SCBD_AHB", $sformatf("Actual AHB txn with {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p} does not match expected: {Address: 0x%x} {Data: 0x%x} {RnW: %p} {Resp: %p}",t.address,t.data[0],t.RnW,t.resp[0],t_exp.address,t_exp.data[0],t_exp.RnW,t_exp.resp[0]))
          end
      end
      else begin
          `uvm_info("FIXME_CUSTOM_SCOREBOARD", "UVMF_CHANGE_ME: The mldsa_scoreboard::write_actual_ahb_analysis_export function needs to be completed with custom scoreboard functionality for unexpected actual transactions",UVM_HIGH)
          `uvm_error("SCBD_AHB",$sformatf("NO PREDICTED ENTRY TO COMPARE AGAINST:%s",t.convert2string()))
          nothing_to_compare_against_count++;
      end
      -> entry_received;
    end
 
    // pragma uvmf custom actual_ahb_analysis_export_scoreboard end
  endfunction


  /// FUNCTION: write_expected_ahb_analysis_export
  // QVIP transactions received through expected_ahb_analysis_export initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_expected_ahb_analysis_export(mvc_sequence_item_base _t);
    // pragma uvmf custom expected_ahb_analysis_export_scoreboard begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t;
    if (!$cast(t,_t)) begin
      `uvm_fatal("SCBD_AHB","Cast from mvc_sequence_item_base to ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) in write_expected_ahb_analysis_export failed!")
    end
    // `uvm_info("SCBD_AHB", "Transaction Received through expected_ahb_analysis_export", UVM_MEDIUM)
    // `uvm_info("SCBD_AHB",{"            Data: ",t.convert2string()}, UVM_HIGH)
    if (t.RnW == 1'b0 && !disable_scrboard_from_test) begin
      // `uvm_info("SCBD_AHB", "Transaction is a read", UVM_MEDIUM)
      // Check if the transaction address matches any of the registers to be skipped
      if ((t.address >= scbr_mldsa_rm.MLDSA_NAME[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_NAME[$size(scbr_mldsa_rm.MLDSA_NAME)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_VERSION[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_VERSION[$size(scbr_mldsa_rm.MLDSA_VERSION)-1].get_address(scbr_mldsa_map)) ||
        (t.address == scbr_mldsa_rm.MLDSA_CTRL.get_address(scbr_mldsa_map)) ||
        (t.address == scbr_mldsa_rm.MLDSA_STATUS.get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_ENTROPY[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_ENTROPY[$size(scbr_mldsa_rm.MLDSA_ENTROPY)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_SEED[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_SEED[$size(scbr_mldsa_rm.MLDSA_SEED)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_SIGN_RND[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_SIGN_RND[$size(scbr_mldsa_rm.MLDSA_SIGN_RND)-1].get_address(scbr_mldsa_map)) ||
        (t.address >= scbr_mldsa_rm.MLDSA_MSG[0].get_address(scbr_mldsa_map) &&
          t.address <= scbr_mldsa_rm.MLDSA_MSG[$size(scbr_mldsa_rm.MLDSA_MSG)-1].get_address(scbr_mldsa_map))
      ) begin
        `uvm_info("SCBD_AHB", $sformatf("Skipping monitor message in scoreboard at address: 0x%x", t.address), UVM_HIGH)
      end
      else if ( (t.address >= scbr_mldsa_rm.MLDSA_VERIFY_RES[0].get_address(scbr_mldsa_map) &&
                t.address <= scbr_mldsa_rm.MLDSA_VERIFY_RES[$size(scbr_mldsa_rm.MLDSA_VERIFY_RES)-1].get_address(scbr_mldsa_map)) &&
                (expect_verif_failure || expect_verif_pass_after_failure) 
      )begin

        ahb_expected_verif_q.push_back(t);
        -> entry_received;
      end
      else begin

        ahb_expected_q.push_back(t);

        transaction_count++;
        -> entry_received;
      end
    end
 
    // pragma uvmf custom expected_ahb_analysis_export_scoreboard end
  endfunction
  

  // FUNCTION: extract_phase
  virtual function void extract_phase(uvm_phase phase);
// pragma uvmf custom extract_phase begin
     super.extract_phase(phase);
// pragma uvmf custom extract_phase end
  endfunction

  // FUNCTION: check_phase
  virtual function void check_phase(uvm_phase phase);
// pragma uvmf custom check_phase begin
     super.check_phase(phase);
// pragma uvmf custom check_phase end
  endfunction

  // FUNCTION: report_phase
  virtual function void report_phase(uvm_phase phase);
// pragma uvmf custom report_phase begin
     super.report_phase(phase);
     `uvm_info("SCBD_REPORT", $sformatf("Total Matches: %0d", match_count), UVM_LOW)
     `uvm_info("SCBD_REPORT", $sformatf("Total Mismatches: %0d", mismatch_count), UVM_LOW)
     `uvm_info("SCBD_REPORT", $sformatf("No Predicted Entries to Compare Against: %0d", nothing_to_compare_against_count), UVM_LOW)
      if (mismatch_count == 0)
          $display("* TESTCASE PASSED");
      else
          $display("* TESTCASE FAILED");
// pragma uvmf custom report_phase end
  endfunction

endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

