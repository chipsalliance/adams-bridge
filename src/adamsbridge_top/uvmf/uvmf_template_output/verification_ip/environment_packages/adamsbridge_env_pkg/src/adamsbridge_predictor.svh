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
//  adamsbridge_sb_ahb_ap broadcasts transactions of type ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH)
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

class adamsbridge_predictor #(
  type CONFIG_T,
  type BASE_T = uvm_component
  )
 extends BASE_T;

  // Factory registration of this class
  `uvm_component_param_utils( adamsbridge_predictor #(
                              CONFIG_T,
                              BASE_T
                              )
)


  // Instantiate a handle to the configuration of the environment in which this component resides
  CONFIG_T configuration;


  
  // Instantiate the analysis ports
  uvm_analysis_port #(mvc_sequence_item_base) adamsbridge_sb_ahb_ap;

 
  // Instantiate QVIP analysis exports
  uvm_analysis_imp_ahb_slave_0_ae #(mvc_sequence_item_base, adamsbridge_predictor #(
                              .CONFIG_T(CONFIG_T),
                              .BASE_T(BASE_T)
                              )
) ahb_slave_0_ae;

  // Transaction variable for predicted values to be sent out adamsbridge_sb_ahb_ap
  // Once a transaction is sent through an analysis_port, another transaction should
  // be constructed for the next predicted transaction. 
  typedef ahb_master_burst_transfer #(ahb_lite_slave_0_params::AHB_NUM_MASTERS, ahb_lite_slave_0_params::AHB_NUM_MASTER_BITS, ahb_lite_slave_0_params::AHB_NUM_SLAVES, ahb_lite_slave_0_params::AHB_ADDRESS_WIDTH, ahb_lite_slave_0_params::AHB_WDATA_WIDTH, ahb_lite_slave_0_params::AHB_RDATA_WIDTH) adamsbridge_sb_ahb_ap_output_transaction_t;
  adamsbridge_sb_ahb_ap_output_transaction_t adamsbridge_sb_ahb_ap_output_transaction;
  // Code for sending output transaction out through adamsbridge_sb_ahb_ap
  // adamsbridge_sb_ahb_ap.write(adamsbridge_sb_ahb_ap_output_transaction);


  // Create QVIP transaction handles for debug visibility 
  mvc_sequence_item_base ahb_slave_0_ae_debug_t;
  // Create transaction handles for visibility in visualizer

  // pragma uvmf custom class_item_additional begin
  string dilithium_command;
  // pragma uvmf custom class_item_additional end

  uvm_analysis_port #(mvc_sequence_item_base) adamsbridge_ahb_reg_ap;
  uvm_reg_map p_adamsbridge_map; // Block map
  adamsbridge_reg_model_top  p_adamsbridge_rm;

  bit [31:0] SEED [0:7]; //32 Bytes
  bit [31:0] SK []; //4864 Bytes
  bit [31:0] PK []; //2592 Bytes
  bit [31:0] MSG [0:15]; //64 Bytes
  bit [31:0] SIG []; //4864 Bytes
  bit [31:0] VERIF [0:15]; //64 Bytes

  // FUNCTION: new
  function new(string name, uvm_component parent);
    super.new(name,parent);
    // Construct arrays
    SK = new[1216];
    PK = new[648];
    SIG = new[1149];
    `uvm_warning("PREDICTOR_REVIEW", "This predictor has been created either through generation or re-generation with merging.  Remove this warning after the predictor has been reviewed.")
  
     // pragma uvmf custom new begin
  // pragma uvmf custom new end
  endfunction

  // FUNCTION: build_phase
  virtual function void build_phase (uvm_phase phase);

    ahb_slave_0_ae = new("ahb_slave_0_ae", this);
    adamsbridge_sb_ahb_ap =new("adamsbridge_sb_ahb_ap", this );
    adamsbridge_ahb_reg_ap = new("adamsbridge_ahb_reg_ap", this);

    p_adamsbridge_rm = configuration.adamsbridge_rm;
    p_adamsbridge_map = p_adamsbridge_rm.get_default_map();
    
  // pragma uvmf custom build_phase begin
    // Read the configuration parameter
    if (!uvm_config_db#(string)::get(this, "", "dilithium_command", dilithium_command)) begin
      dilithium_command = "test_dilithium5"; // default value
    end

    `uvm_info("PREDICTOR", $sformatf("DILITHIUM_COMMAND to be used: %s", dilithium_command), UVM_LOW)
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
    uvm_reg reg_obj;
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
    adamsbridge_sb_ahb_ap_output_transaction = adamsbridge_sb_ahb_ap_output_transaction_t::type_id::create("adamsbridge_sb_ahb_ap_output_transaction");
    //  UVMF_CHANGE_ME: Implement predictor model here.  

    reg_obj = p_adamsbridge_rm.default_map.get_reg_by_offset(t.address);
    if (t.RnW == 1'b1) begin // write
      if (reg_obj == null) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from AHB_map", t.address))
      end
      else begin
        uvm_reg_addr_t base_addr;
        uvm_reg_addr_t reg_addr = t.address;
        int idx;
        if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_SEED[0].get_address(p_adamsbridge_map) &&
            reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_SEED[$size(p_adamsbridge_rm.ADAMSBRIDGE_SEED)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_SEED[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          SEED[idx] = t.data[0][31:0];
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_MSG[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_MSG[$size(p_adamsbridge_rm.ADAMSBRIDGE_MSG)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_MSG[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          MSG[idx] = t.data[0][31:0];
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN[$size(p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          SK[idx] = t.data[0][31:0];
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[$size(p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          PK[idx] = t.data[0][31:0];
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[$size(p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          SIG[idx] = t.data[0][31:0];
        end
        else if (reg_addr == p_adamsbridge_rm.ADAMSBRIDGE_CTRL.get_address(p_adamsbridge_map)) begin
          run_executable(t.data[0][1:0]);
          zeroize_registers(t.data[0][2]);
        end
        else begin
          `uvm_error("PRED_AHB", $sformatf("Unhandled register write at address: 0x%x", reg_addr))
        end
      end
    end
    else if (t.RnW == 1'b0) begin // read
      if (reg_obj == null) begin
        `uvm_error("PRED_AHB", $sformatf("AHB transaction to address: 0x%x decodes to null from AHB_map", t.address))
      end
      else begin
        uvm_reg_addr_t base_addr;
        uvm_reg_addr_t reg_addr = t.address;
        int idx;
        if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[0].get_address(p_adamsbridge_map) &&
            reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[$size(p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          if (idx < $size(PK)) begin
            t.data[0][31:0] = PK[idx];
          end
          else begin
            `uvm_error("PRED_AHB", "Public key read out of bounds")
          end
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT[$size(p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          if (idx < $size(SK)) begin
            t.data[0][31:0] = SK[idx];
          end
          else begin
            `uvm_error("PRED_AHB", "Private key read out of bounds")
          end
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[$size(p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          if (idx < $size(SIG)) begin
            t.data[0][31:0] = SIG[idx];
          end
          else begin
            `uvm_error("PRED_AHB", "Signature read out of bounds")
          end
        end
        else if (reg_addr >= p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES[0].get_address(p_adamsbridge_map) &&
                 reg_addr <= p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES[$size(p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES)-1].get_address(p_adamsbridge_map)) begin
          base_addr = p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES[0].get_address(p_adamsbridge_map);
          idx = (reg_addr - base_addr) / 4;
          if (idx < $size(VERIF)) begin
            t.data[0][31:0] = VERIF[idx];
          end
          else begin
            `uvm_error("PRED_AHB", "Verification result read out of bounds")
          end
        end
        // Add more cases as needed for other registers
        else begin
          `uvm_error("PRED_AHB", $sformatf("Unhandled register read at address: 0x%x", reg_addr))
        end
        // Send the transaction to the scoreboard
        adamsbridge_sb_ahb_ap_output_transaction.copy(t);
        adamsbridge_sb_ahb_ap.write(adamsbridge_sb_ahb_ap_output_transaction);
      end
    end
    

    // Code for sending output transaction out through adamsbridge_sb_ahb_ap
    // pragma uvmf custom ahb_slave_0_ae_predictor end
  endfunction

  function void run_executable(bit [1:0] op_code);
    string input_file;
    string output_file;
    string line;
    int words_read;
    bit [31:0] value;
    int fd;
    case (op_code)
      2'b00: begin
        `uvm_info("PRED", "CTRL Reg is written 2'b00 (No operation)...", UVM_MEDIUM)
      end
      2'b01: begin
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
        $system($sformatf("%s keygen_input.hex keygen_output.hex", dilithium_command));
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
          $sscanf(line, "%02x\n", value);
        end
        read_line(fd, 2592/4, PK); // Read 2592-byte Public Key to the file
        read_line(fd, 4864/4, SK); // Read 4864-byte Secret Key to the file
        $fclose(fd);
      end
      2'b10: begin
        output_file = "./signing_input.hex";
        input_file  = "./signing_ouput.hex";
        // Open the file for writing
        fd = $fopen(output_file, "w");
        if (fd == 0) begin
          $display("ERROR: Failed to open file: %s", output_file);
          return;
        end
        $fwrite(fd, "%02X\n", op_code-1); // Signature generation cmd
        write_file(fd, 64/4, MSG); // Write 64-byte Message to the file
        write_file(fd, 4864/4, SK); // Write 4864-byte Secret Key to the file
        $fclose(fd);
        $system("test_dilithium5 signing_input.hex signing_ouput.hex");
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
          $sscanf(line, "%02x\n", value);
        end
        // Skip the second line
        void'($fgets(line, fd)); // Read a line from the file
        $sscanf(line, "%08x\n", value);
        read_line(fd, 4864/4, SIG);// Read 4864-byte Signature to the file
        $fclose(fd);
      end
      2'b11: begin
        output_file = "./verif_input.hex";
        input_file  = "./verif_ouput.hex";
        // Open the file for writing
        fd = $fopen(output_file, "w");
        if (fd == 0) begin
          $display("ERROR: Failed to open file: %s", output_file);
          return;
        end
        $fwrite(fd, "%02X\n", op_code-1); // Verification cmd
        $fwrite(fd, "00001233\n"); // Signature lenght
        write_file(fd, 4864/4, SIG); // Write 4864-byte Signature to the file
        write_file(fd, 2592/4, PK); // Write 2592-byte Public Key to the file
        $fclose(fd);
        $system("test_dilithium5 verif_input.hex verif_ouput.hex");
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
          $sscanf(line, "%02x\n", value);
        end
        // Skip the second line
        void'($fgets(line, fd)); // Read a line from the file
        $sscanf(line, "%08x\n", value);
        // TODO: Implement returned verification result
        $fclose(fd);
      end
    endcase
  endfunction

  // TODO: Please learn which registers that I need to zeroize
  function void zeroize_registers(bit zeroize);

    // Define the zero_value at the beginning
    uvm_reg_data_t zero_value = 32'b0;

    if (zeroize) begin
  
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
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_NAME[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_NAME[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_VERSION[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_VERSION[i].set(zero_value);
      end
      p_adamsbridge_rm.ADAMSBRIDGE_CTRL.set(zero_value);
      p_adamsbridge_rm.ADAMSBRIDGE_STATUS.set(zero_value);
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_IV[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_IV[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_SEED[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_SEED[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_SIGN_RND[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_SIGN_RND[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_MSG[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_MSG[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_VERIFY_RES[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_OUT[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_PRIVKEY_IN[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_PUBKEY[i].set(zero_value);
      end
      foreach (p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[i]) begin
        p_adamsbridge_rm.ADAMSBRIDGE_SIGNATURE[i].set(zero_value);
      end
    end
endfunction

  
  

  function void read_line(int fd, int bit_length_words, ref bit [31:0] array []);


    string line;
    int words_read;
    bit [31:0] word;

    // Read the data from the file line by line
    words_read = 0;
    while (!$feof(fd) && words_read < bit_length_words) begin
      line = "";
      void'($fgets(line, fd)); // Read a line from the file
      while ($sscanf(line, "%08x", word) == 1) begin
        array[words_read] = word;
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
      $fwrite(fd, "%08X", array[i]);
    end
    $fwrite(fd, "\n");

  endfunction


  
endclass 

// pragma uvmf custom external begin
// pragma uvmf custom external end

