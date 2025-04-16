//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//
// DESCRIPTION: This analysis component contains analysis_exports for receiving
//   data and analysis_ports for sending data.
// 
//   This analysis component has the following analysis_exports that receive the 
//   listed transaction type.
//   
//
//   This analysis component has the following analysis_ports that can broadcast 
//   the listed transaction type.
//
//  mldsa_sb_ahb_ap broadcasts transactions of type ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH)
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class mldsa_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( mldsa_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;


  
  // Instantiate the analysis ports
  uvm_analysis_port #(mvc_sequence_item_base) mldsa_sb_ahb_ap;

 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, mldsa_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  // Transaction variable for predicted values to be sent out mldsa_sb_ahb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) mldsa_sb_ahb_ap_output_transaction_t;
  mldsa_sb_ahb_ap_output_transaction_t mldsa_sb_ahb_ap_output_transaction;
  // Code for sending output transaction out through mldsa_sb_ahb_ap
  // mldsa_sb_ahb_ap.write(mldsa_sb_ahb_ap_output_transaction);


  // Create QVIP transaction handles for debug visibility 
  mvc_sequence_item_base ahb_slave_0_ae_debug_t;
  // Create transaction handles for visibility in visualizer

  // pragma uvmf custom class_item_additional begin
  string dilithium_command;
  bit expect_predictor_verif_failure;
  // pragma uvmf custom class_item_additional end

  uvm_analysis_port #(mvc_sequence_item_base) mldsa_ahb_reg_ap;
  uvm_reg_map p_mldsa_map; // Block map
  mldsa_reg_model_top  p_mldsa_rm;

  bit [31:0] SEED [0:7]; //32 Bytes
  bit [31:0] SK []; //4896 Bytes
  bit [31:0] PK []; //2592 Bytes
  bit [31:0] MSG [0:15]; //64 Bytes
  bit [31:0] SIG []; //4628 Bytes
  bit [31:0] VERIF []; //64 Bytes

  bit lock_IP;
  bit valid;
  bit [31:0] data;
  uvm_status_e status;

  // FUNCTION: new
  function new(string name, uvm_component parent);
    super.new(name,parent);
    // Construct arrays
    SK = new[1224];
    PK = new[648];
    SIG = new[1157];
    VERIF = new[16];
    lock_IP = 0;
    data = '0;
    //`uvm_warning("PREDICTOR_REVIEW", "This predictor has been created either through generation or re-generation with merging.  Remove this warning after the predictor has been reviewed.")
  
     // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    mldsa_sb_ahb_ap =new("mldsa_sb_ahb_ap", this );
    mldsa_ahb_reg_ap = new("mldsa_ahb_reg_ap", this);

    p_mldsa_rm = configuration.mldsa_rm;
    p_mldsa_map = p_mldsa_rm.get_default_map();
    
  // pragma uvmf custom build_phase begin
    // Read the configuration parameter
    if (!uvm_config_db#(string)::get(this, "", "dilithium_command", dilithium_command)) begin
      dilithium_command = "test_dilithium5"; // default value
    end
    `uvm_info("PREDICTOR", $sformatf("DILITHIUM_COMMAND to be used: %s", dilithium_command), UVM_LOW)

    if (!uvm_config_db#(bit)::get(this, "", "expect_predictor_verif_failure", expect_predictor_verif_failure)) begin
      expect_predictor_verif_failure = 0; // default value
    end
    `uvm_info("PREDICTOR", $sformatf("expect_predictor_verif_failure to be used: %d", expect_predictor_verif_failure), UVM_LOW)
  // pragma uvmf custom build_phase end
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask


  // FUNCTION: write_ahb_slave_0_ae
  // QVIP transactions received through ahb_slave_0_ae initiate the execution of this function.
  // This function casts incoming QVIP transactions into the correct protocol type and then performs prediction 
  // of DUT output values based on DUT input, configuration and state
  virtual function void write_ahb_slave_0_ae(mvc_sequence_item_base _t);
    logic [31:0] written_value, expected_value;
    uvm_reg_addr_t privkey_out_base_addr, privkey_in_base_addr, signature_base_addr, pubkey_base_addr;
    uvm_reg_addr_t privkey_out_size, privkey_in_size, signature_size, pubkey_size;
    uvm_reg_addr_t reg_addr;
    uvm_mem privkey_out_mem, privkey_in_mem, signature_mem, pubkey_mem;
    uvm_reg reg_obj;
    bit MEM_range_true;
    // pragma uvmf custom ahb_slave_0_ae_predictor begin
    ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, 
                                ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, 
                                ahb_lite_slave_0_params::AHB_NUM_SLAVES, 
                                ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, 
                                ahb_lite_slave_0_params::AHB_WDATA_WIDTH, 
                                ahb_lite_slave_0_params::AHB_RDATA_WIDTH) t;
    ahb_slave_0_ae_debug_t = _t;
    if (!$cast(t,_t)) begin
      `uvm_fatal("PRED","Cast from mvc_sequence_item_base to ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) in write_ahb_slave_0_ae failed!")
    end
    // `uvm_info("PRED", "Transaction Received through ahb_slave_0_ae", UVM_MEDIUM)
    // `uvm_info("PRED",{"            Data: ",t.convert2string()}, UVM_FULL)
    // Construct one of each output transaction type.
    mldsa_sb_ahb_ap_output_transaction = mldsa_sb_ahb_ap_output_transaction_t::type_id::create("mldsa_sb_ahb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  

    reg_obj = p_mldsa_rm.default_map.get_reg_by_offset(t.address);


    
    
//==========================================================================================
    
    privkey_out_base_addr = p_mldsa_rm.default_map.get_submap_offset(p_mldsa_rm.MLDSA_PRIVKEY_OUT.default_map);
    privkey_out_mem = p_mldsa_rm.default_map.get_mem_by_offset(privkey_out_base_addr);
    privkey_out_size = uvm_reg_addr_t'(privkey_out_mem.get_size());
    // Check if MLDSA_PRIVKEY_OUT memory is correctly retrieved
    if (privkey_out_mem != null) begin
      //`uvm_info("PRED_AHB", $sformatf("MLDSA_PRIVKEY_OUT: Base Addr = 0x%0h, Size = %0d", privkey_out_base_addr, privkey_out_size), UVM_LOW)
    end
    else begin
      `uvm_fatal("PRED_AHB", "Could not retrieve MLDSA_PRIVKEY_OUT memory from sub-map")
    end

    // Retrieve base address and memory object for MLDSA_PRIVKEY_IN
    privkey_in_base_addr = p_mldsa_rm.default_map.get_submap_offset(p_mldsa_rm.MLDSA_PRIVKEY_IN.default_map);
    privkey_in_mem = p_mldsa_rm.default_map.get_mem_by_offset(privkey_in_base_addr);
    privkey_in_size = uvm_reg_addr_t'(privkey_in_mem.get_size());

    // Check if MLDSA_PRIVKEY_IN memory is correctly retrieved
    if (privkey_in_mem != null) begin
      //`uvm_info("PRED_AHB", $sformatf("MLDSA_PRIVKEY_IN: Base Addr = 0x%0h, Size = %0d", privkey_in_base_addr, privkey_in_size), UVM_LOW)
    end
    else begin
      `uvm_fatal("PRED_AHB", "Could not retrieve MLDSA_PRIVKEY_IN memory from sub-map")
    end

    // Retrieve base address and memory object for MLDSA_SIGNATURE
    signature_base_addr = p_mldsa_rm.default_map.get_submap_offset(p_mldsa_rm.MLDSA_SIGNATURE.default_map);
    signature_mem = p_mldsa_rm.default_map.get_mem_by_offset(signature_base_addr);
    signature_size = uvm_reg_addr_t'(signature_mem.get_size());

    // Check if MLDSA_SIGNATURE memory is correctly retrieved
    if (signature_mem != null) begin
      //`uvm_info("PRED_AHB", $sformatf("MLDSA_SIGNATURE: Base Addr = 0x%0h, Size = %0d", signature_base_addr, signature_size), UVM_LOW)
    end
    else begin
      `uvm_fatal("PRED_AHB", "Could not retrieve MLDSA_SIGNATURE memory from sub-map")
    end
    
    // Retrieve base address and memory object for MLDSA_PUBKEY
    pubkey_base_addr = p_mldsa_rm.default_map.get_submap_offset(p_mldsa_rm.MLDSA_PUBKEY.default_map);
    pubkey_mem = p_mldsa_rm.default_map.get_mem_by_offset(pubkey_base_addr);
    pubkey_size = uvm_reg_addr_t'(pubkey_mem.get_size());

    // Check if MLDSA_PUBKEY memory is correctly retrieved
    if (pubkey_mem != null) begin
      //`uvm_info("PRED_AHB", $sformatf("MLDSA_PUBKEY: Base Addr = 0x%0h, Size = %0d", pubkey_base_addr, pubkey_size), UVM_LOW)
    end
    else begin
      `uvm_fatal("PRED_AHB", "Could not retrieve MLDSA_PUBKEY memory from sub-map")
    end
    reg_addr = t.address;
    MEM_range_true = (reg_addr >= privkey_in_base_addr && reg_addr < privkey_in_base_addr + privkey_in_size * 4)
                      ||
                     (reg_addr >= privkey_out_base_addr && reg_addr < privkey_out_base_addr + privkey_out_size * 4)
                      ||
                     (reg_addr >= signature_base_addr && reg_addr < signature_base_addr + signature_size * 4)
                      ||
                     (reg_addr >= pubkey_base_addr && reg_addr < pubkey_base_addr + pubkey_size * 4);

//===========================================================================================
    if (t.RnW == 1'b1) begin // write
      if (reg_obj == null && !MEM_range_true) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from AHB_map", t.address))
      end
      else begin
        uvm_reg_addr_t base_addr;
        int idx;
        if (reg_addr >= p_mldsa_rm.MLDSA_SEED[0].get_address(p_mldsa_map) &&
            reg_addr <= p_mldsa_rm.MLDSA_SEED[$size(p_mldsa_rm.MLDSA_SEED)-1].get_address(p_mldsa_map)) begin
          base_addr = p_mldsa_rm.MLDSA_SEED[0].get_address(p_mldsa_map);
          idx = (reg_addr - base_addr) / 4;
          SEED[idx] = t.data[0][31:0];
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_MSG[0].get_address(p_mldsa_map) &&
                 reg_addr <= p_mldsa_rm.MLDSA_MSG[$size(p_mldsa_rm.MLDSA_MSG)-1].get_address(p_mldsa_map)) begin 
          base_addr = p_mldsa_rm.MLDSA_MSG[0].get_address(p_mldsa_map);
          idx = (reg_addr - base_addr) / 4;
          if (!lock_IP) MSG[idx] = t.data[0][31:0]; //hack to avoid writing over MSG
        end
        // Accessing data in MLDSA_PRIVKEY_IN
        else if (reg_addr >= privkey_in_base_addr && reg_addr < privkey_in_base_addr + privkey_in_size * 4) begin
          idx = (reg_addr - privkey_in_base_addr) / 4;
          SK[idx] = t.data[0][31:0];
          //`uvm_info("PRED_AHB", $sformatf("Writing to MLDSA_PRIVKEY_IN: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
        end
        // Accessing data in MLDSA_PUBKEY
        else if (reg_addr >= pubkey_base_addr && reg_addr < pubkey_base_addr + pubkey_size * 4) begin
          idx = (reg_addr - pubkey_base_addr) / 4;
          PK[idx] = t.data[0][31:0];
          //`uvm_info("PRED_AHB", $sformatf("Writing to MLDSA_PUBKEY: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
        end
        // Accessing data in MLDSA_SIGNATURE
        else if (reg_addr >= signature_base_addr && reg_addr < signature_base_addr + signature_size * 4) begin
          idx = (reg_addr - signature_base_addr) / 4;
          SIG[idx] = t.data[0][31:0];
          //`uvm_info("PRED_AHB", $sformatf("Writing to MLDSA_SIGNATURE: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
        end
        else if (reg_addr == p_mldsa_rm.MLDSA_CTRL.get_address(p_mldsa_map)) begin
          run_executable(t.data[0][2:0]);
          zeroize_registers(t.data[0][3]);
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_SIGN_RND[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_SIGN_RND[$size(p_mldsa_rm.MLDSA_SIGN_RND)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_SIGN_RND at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else begin
          `uvm_error("PRED_AHB", $sformatf("Unhandled register write at address: 0x%x", reg_addr))
        end
      end
    end
    else if (t.RnW == 1'b0) begin // read
      if (reg_obj == null && !MEM_range_true) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from AHB_map", t.address))
      end
      else begin
        uvm_reg_addr_t base_addr;
        // uvm_reg_addr_t reg_addr = t.address;
        int idx;
        // Accessing data in MLDSA_PRIVKEY_OUT
        if (reg_addr >= privkey_out_base_addr && reg_addr < privkey_out_base_addr + privkey_out_size * 4) begin
            idx = (reg_addr - privkey_out_base_addr) / 4;
            if (idx < privkey_out_size) begin
                t.data[0][31:0] = SK[idx]; // Example read from SK
                //`uvm_info("PRED_AHB", $sformatf("Reading from MLDSA_PRIVKEY_OUT: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
            end
            else begin
                `uvm_error("PRED_AHB", "Private key out read out of bounds")
            end
        end
        // Accessing data in MLDSA_PUBKEY
        else if (reg_addr >= pubkey_base_addr && reg_addr < pubkey_base_addr + pubkey_size * 4) begin
            idx = (reg_addr - pubkey_base_addr) / 4;
            if (idx < pubkey_size) begin
                t.data[0][31:0] = PK[idx]; // Example read from SIG
                //`uvm_info("PRED_AHB", $sformatf("Reading from MLDSA_PUBKEY: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
            end
            else begin
                `uvm_error("PRED_AHB", "Pubkey read out of bounds")
            end
        end
        // Accessing data in MLDSA_SIGNATURE
        else if (reg_addr >= signature_base_addr && reg_addr < signature_base_addr + signature_size * 4) begin
            idx = (reg_addr - signature_base_addr) / 4;
            if (idx < signature_size) begin
                t.data[0][31:0] = SIG[idx]; // Example read from SIG
                //`uvm_info("PRED_AHB", $sformatf("Reading from MLDSA_SIGNATURE: Addr = 0x%0h, Data = 0x%0h", reg_addr, t.data[0][31:0]), UVM_LOW)
            end
            else begin
                `uvm_error("PRED_AHB", "Signature read out of bounds")
            end
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_VERIFY_RES[0].get_address(p_mldsa_map) &&
                 reg_addr <= p_mldsa_rm.MLDSA_VERIFY_RES[$size(p_mldsa_rm.MLDSA_VERIFY_RES)-1].get_address(p_mldsa_map)) begin
          base_addr = p_mldsa_rm.MLDSA_VERIFY_RES[0].get_address(p_mldsa_map);
          idx = (reg_addr - base_addr) / 4;
          if (idx < $size(VERIF)) begin
            t.data[0][31:0] = VERIF[idx];
          end
          else begin
            `uvm_error("PRED_AHB", "Verification result read out of bounds")
          end
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_NAME[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_NAME[$size(p_mldsa_rm.MLDSA_NAME)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_NAME at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_VERSION[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_VERSION[$size(p_mldsa_rm.MLDSA_VERSION)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_VERSION at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr == p_mldsa_rm.MLDSA_CTRL.get_address(p_mldsa_map)) begin
          `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_CTRL at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr == p_mldsa_rm.MLDSA_STATUS.get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_STATUS at address: 0x%x", reg_addr), UVM_HIGH)
          // // This part checks if data is valid
          // data = t.data[0][31:0];
          // valid = data[1];
          // if (valid) begin
          //   lock_IP = 0;
          //   `uvm_info("PRED_AHB", $sformatf("The IP done signal released the lock"), UVM_LOW)
          // end else begin
          //   lock_IP = lock_IP;
          // end
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_ENTROPY[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_ENTROPY[$size(p_mldsa_rm.MLDSA_ENTROPY)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_ENTROPY at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_SEED[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_SEED[$size(p_mldsa_rm.MLDSA_SEED)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_SEED at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_SIGN_RND[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_SIGN_RND[$size(p_mldsa_rm.MLDSA_SIGN_RND)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_SIGN_RND at address: 0x%x", reg_addr), UVM_HIGH)
        end
        else if (reg_addr >= p_mldsa_rm.MLDSA_MSG[0].get_address(p_mldsa_map) &&
                reg_addr <= p_mldsa_rm.MLDSA_MSG[$size(p_mldsa_rm.MLDSA_MSG)-1].get_address(p_mldsa_map)) begin
            `uvm_info("PRED_AHB", $sformatf("Skipping register MLDSA_MSG at address: 0x%x", reg_addr), UVM_HIGH)
        end
        // Add more cases as needed for other registers
        else begin
          `uvm_error("PRED_AHB", $sformatf("Unhandled register read at address: 0x%x", reg_addr))
        end
        // Send the transaction to the scoreboard
        mldsa_sb_ahb_ap_output_transaction.copy(t);
        mldsa_sb_ahb_ap.write(mldsa_sb_ahb_ap_output_transaction);
      end
    end
    

    // Code for sending output transaction out through mldsa_sb_ahb_ap
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction

  function void run_executable(bit [2:0] op_code);
    string input_file;
    string output_file;
    string line;
    int words_read;
    bit [31:0] value;
    int fd;
    if (!lock_IP) begin
      case (op_code)
        3'b000: begin
          `uvm_info("PRED", "CTRL Reg is written 3'b00 (No operation)...", UVM_MEDIUM)
        end
        3'b001: begin
          lock_IP = 1;
          output_file = "./keygen_input.hex";
          input_file = "./keygen_output.hex";
          // Open the file for writing
          fd = $fopen(output_file, "w");
          if (fd == 0) begin
            $display("ERROR: Failed to open file: %s", output_file);
            return;
          end
          $fwrite(fd, "%02X\n", op_code-1); // KeyGen cmd
          write_file(fd, 32/4, SEED); // Write 32-byte SEED to the file
          $fclose(fd);
          // $system("test_dilithium5 keygen_input.hex keygen_output.hex");
          $system($sformatf("./%s keygen_input.hex keygen_output.hex >> keygen.log", dilithium_command));
          `uvm_info("PRED", $sformatf("%s is being executed", dilithium_command), UVM_MEDIUM)
          `uvm_info("PRED", "CTRL Reg is configured to perform KeyGen", UVM_MEDIUM)
          // Open the file for reading
          fd = $fopen(input_file, "r");
          if (fd == 0) begin
            `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
            return;
          end
          else begin
            // Skip the first line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
          end
          read_line(fd, 648, PK); // Read 2592-byte Public Key to the file
          read_line(fd, 1224, SK); // Read 4864-byte Secret Key to the file
          $fclose(fd);
        end
        3'b010: begin
          lock_IP = 1;
          output_file = "./signing_input.hex";
          input_file  = "./signing_ouput.hex";
          // Open the file for writing
          fd = $fopen(output_file, "w");
          if (fd == 0) begin
            $display("ERROR: Failed to open file: %s", output_file);
            return;
          end
          $fwrite(fd, "%02X\n", op_code-1); // Signature generation cmd
          write_file(fd, 16, MSG); // Write 64-byte Message to the file
          write_file(fd, 1224, SK); // Write 4864-byte Secret Key to the file
          $fclose(fd);
          //$system("test_dilithium5 signing_input.hex signing_ouput.hex");
          $system($sformatf("./%s signing_input.hex signing_ouput.hex >> signing.log", dilithium_command));
          `uvm_info("PRED", "CTRL Reg is configured to perform Signature Generation", UVM_MEDIUM)
          // Open the file for reading
          fd = $fopen(input_file, "r");
          if (fd == 0) begin
            `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
            return;
          end
          else begin
            // Skip the first line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
          end
          // Skip the second line
          void'($fgets(line, fd)); // Read a line from the file
          void'($sscanf(line, "%08x\n", value));
          read_line(fd, 1157, SIG);// Read 4864-byte Signature to the file
          SIG[1156] = SIG[1156] >> 8;
          $fclose(fd);
        end
        3'b011: begin
          lock_IP = 1;
          if ( ! expect_predictor_verif_failure) begin
            output_file = "./verif_input.hex";
            input_file  = "./verif_ouput.hex";
            // Open the file for writing
            fd = $fopen(output_file, "w");
            if (fd == 0) begin
              $display("ERROR: Failed to open file: %s", output_file);
              return;
            end
            $fwrite(fd, "%02X\n", op_code-1); // Verification cmd
            //$fwrite(fd, "00001253\n"); // Signature lenght
            // write_file(fd, 1157, SIG); // Write 4864-byte Signature to the file
            write_file_without_newline(fd, 1157, SIG);
            $fwrite(fd, "%02X%02X%02X", SIG[1156][7:0],SIG[1156][15:8],SIG[1156][23:16]);
            write_file(fd, 16, MSG); // Write 64-byte message to the file
            write_file(fd, 648, PK); // Write 2592-byte Public Key to the file
            $fclose(fd);
            $system($sformatf("./%s verif_input.hex verif_ouput.hex >> verif.log", dilithium_command));
            `uvm_info("PRED", "CTRL Reg is configured to perform Verification", UVM_MEDIUM)
            // Open the file for reading
            fd = $fopen(input_file, "r");
            if (fd == 0) begin
              `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
              return;
            end
            else begin
              // Skip the first line
              void'($fgets(line, fd)); // Read a line from the file
              void'($sscanf(line, "%02x\n", value));
            end
            // Skip the second line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
            read_line(fd, 16, VERIF);// Read 16 dword verify result from the file
            $fclose(fd);
          end
          else begin
            input_file  = "./verif_ouput.hex";
            $system($sformatf("./%s verif_failure_input_test.hex verif_ouput.hex >> verif.log", dilithium_command));
            `uvm_info("PRED", "CTRL Reg is configured to perform Verification", UVM_MEDIUM)
            // Open the file for reading
            fd = $fopen(input_file, "r");
            if (fd == 0) begin
              `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
              return;
            end
            else begin
              // Skip the first line
              void'($fgets(line, fd)); // Read a line from the file
              void'($sscanf(line, "%02x\n", value));
            end
            // Skip the second line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
            read_line(fd, 16, VERIF);// Read 16 dword verify result from the file
            $fclose(fd);
          end
        end
        3'b100: begin
          lock_IP = 1;
          output_file = "./keygen_input.hex";
          input_file = "./keygen_output.hex";
          // Open the file for writing
          fd = $fopen(output_file, "w");
          if (fd == 0) begin
            $display("ERROR: Failed to open file: %s", output_file);
            return;
          end
          $fwrite(fd, "%02X\n", 0); // KeyGen cmd
          write_file(fd, 32/4, SEED); // Write 32-byte SEED to the file
          $fclose(fd);
          // $system("test_dilithium5 keygen_input.hex keygen_output.hex");
          $system($sformatf("./%s keygen_input.hex keygen_output.hex >> keygen.log", dilithium_command));
          `uvm_info("PRED", $sformatf("%s is being executed", dilithium_command), UVM_MEDIUM)
          `uvm_info("PRED", "CTRL Reg is configured to perform KeyGen", UVM_MEDIUM)
          // Open the file for reading
          fd = $fopen(input_file, "r");
          if (fd == 0) begin
            `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
            return;
          end
          else begin
            // Skip the first line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
          end
          read_line(fd, 648, PK); // Read 2592-byte Public Key to the file
          read_line(fd, 1224, SK); // Read 4864-byte Secret Key to the file
          $fclose(fd);
          //Perform Signing
          output_file = "./signing_input.hex";
          input_file  = "./signing_ouput.hex";
          // Open the file for writing
          fd = $fopen(output_file, "w");
          if (fd == 0) begin
            $display("ERROR: Failed to open file: %s", output_file);
            return;
          end
          $fwrite(fd, "%02X\n", 1); // Signature generation cmd
          write_file(fd, 16, MSG); // Write 64-byte Message to the file
          write_file(fd, 1224, SK); // Write 4864-byte Secret Key to the file
          $fclose(fd);
          //$system("test_dilithium5 signing_input.hex signing_ouput.hex");
          $system($sformatf("./%s signing_input.hex signing_ouput.hex >> signing.log", dilithium_command));
          `uvm_info("PRED", "CTRL Reg is configured to perform Signature Generation", UVM_MEDIUM)
          // Open the file for reading
          fd = $fopen(input_file, "r");
          if (fd == 0) begin
            `uvm_error("PRED", $sformatf("Failed to open input_file: %s", input_file));
            return;
          end
          else begin
            // Skip the first line
            void'($fgets(line, fd)); // Read a line from the file
            void'($sscanf(line, "%02x\n", value));
          end
          // Skip the second line
          void'($fgets(line, fd)); // Read a line from the file
          void'($sscanf(line, "%08x\n", value));
          read_line(fd, 1157, SIG);// Read 4864-byte Signature to the file
          SIG[1156] = SIG[1156] >> 8;
          $fclose(fd);

        end
      endcase
    end
    if (lock_IP)
    `uvm_info("PRED_RUN_EXE", $sformatf("The IP is locked"), UVM_LOW)
  endfunction

  
  function void zeroize_registers(bit zeroize);

    // Define the zero_value at the beginning
    uvm_reg_data_t zero_value = 32'b0;

    if (zeroize) begin
      lock_IP = 0;
  
      // Zeroize local variables
      foreach (SEED[i]) begin
        SEED[i] = 32'b0;
      end
      foreach (SK[i]) begin
        SK[i] = 32'b0;
      end
      foreach (PK[i]) begin
        PK[i] = 32'b0;
      end
      foreach (MSG[i]) begin
        MSG[i] = 32'b0;
      end
      foreach (SIG[i]) begin
        SIG[i] = 32'b0;
      end
      foreach (VERIF[i]) begin
        VERIF[i] = 32'b0;
      end
  
      // Zeroize registers in the register block using set method
      foreach (p_mldsa_rm.MLDSA_NAME[i]) begin
        p_mldsa_rm.MLDSA_NAME[i].set(zero_value);
      end
      foreach (p_mldsa_rm.MLDSA_VERSION[i]) begin
        p_mldsa_rm.MLDSA_VERSION[i].set(zero_value);
      end
      p_mldsa_rm.MLDSA_CTRL.set(zero_value);
      p_mldsa_rm.MLDSA_STATUS.set(zero_value);
      foreach (p_mldsa_rm.MLDSA_ENTROPY[i]) begin
        p_mldsa_rm.MLDSA_ENTROPY[i].set(zero_value);
      end
      foreach (p_mldsa_rm.MLDSA_SEED[i]) begin
        p_mldsa_rm.MLDSA_SEED[i].set(zero_value);
      end
      foreach (p_mldsa_rm.MLDSA_SIGN_RND[i]) begin
        p_mldsa_rm.MLDSA_SIGN_RND[i].set(zero_value);
      end
      foreach (p_mldsa_rm.MLDSA_MSG[i]) begin
        p_mldsa_rm.MLDSA_MSG[i].set(zero_value);
      end
      foreach (p_mldsa_rm.MLDSA_VERIFY_RES[i]) begin
        p_mldsa_rm.MLDSA_VERIFY_RES[i].set(zero_value);
      end
      //foreach (p_mldsa_rm.MLDSA_PRIVKEY_OUT[i]) begin
      //  p_mldsa_rm.MLDSA_PRIVKEY_OUT[i].set(zero_value);
      //end
      //foreach (p_mldsa_rm.MLDSA_PRIVKEY_IN[i]) begin
      //  p_mldsa_rm.MLDSA_PRIVKEY_IN[i].set(zero_value);
      //end
      //foreach (p_mldsa_rm.MLDSA_PUBKEY[i]) begin
      //  p_mldsa_rm.MLDSA_PUBKEY[i].set(zero_value);
      //end
      //foreach (p_mldsa_rm.MLDSA_SIGNATURE[i]) begin
      //  p_mldsa_rm.MLDSA_SIGNATURE[i].set(zero_value);
      //end
    end
  endfunction

  
  

  function void read_line(int fd, int bit_length_words, ref bit [31:0] array []);
    string line;
    int words_read;
    bit [31:0] word;
    bit [31:0] reversed_word;

    // Read the data from the file line by line
    words_read = 0;
    while (!$feof(fd) && words_read < bit_length_words) begin
      line = "";
      void'($fgets(line, fd)); // Read a line from the file
      while ($sscanf(line, "%08x", word) == 1) begin
        reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]};
        array[words_read] = reversed_word;
        words_read++;
        // Remove the parsed part from the line
        line = line.substr(8);
      end
    end
  endfunction

  function void write_file(int fd, int bit_length_words, bit [31:0] array []);
    int i;
    int words_to_write;

    // Write the data from the array to the file
    words_to_write = bit_length_words;
    for (i = 0; i < words_to_write; i++) begin
      $fwrite(fd, "%02X%02X%02X%02X", array[i][7:0],  array[i][15:8],
                                      array[i][23:16],array[i][31:24]);
    end
    $fwrite(fd, "\n");

  endfunction

  function void write_file_without_newline(int fd, int bit_length_words, bit [31:0] array []);
    int i;
    int words_to_write;

    // Write the data from the array to the file
    words_to_write = bit_length_words;
    for (i = 0; i < words_to_write-1; i++) begin
      $fwrite(fd, "%02X%02X%02X%02X", array[i][7:0],  array[i][15:8],
                                      array[i][23:16],array[i][31:24]);
    end

  endfunction


  
endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

