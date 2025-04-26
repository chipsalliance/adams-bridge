//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//
// Description: This file contains the top level and utility sequences
//     used by test_top. It can be extended to create derivative top
//     level sequences.
//
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
//


typedef mldsa_env_configuration  mldsa_env_configuration_t;

class mldsa_bench_sequence_base extends uvmf_sequence_base #(uvm_sequence_item);

  `uvm_object_utils( mldsa_bench_sequence_base );

  // pragma uvmf custom sequences begin

typedef mldsa_env_sequence_base #(
        .CONFIG_T(mldsa_env_configuration_t)
        )
        mldsa_env_sequence_base_t;
rand mldsa_env_sequence_base_t mldsa_env_seq;



  // UVMF_CHANGE_ME : Instantiate, construct, and start sequences as needed to create stimulus scenarios.
  // Instantiate sequences here
  // pragma uvmf custom sequences end

  // Sequencer handles for each active interface in the environment

  // Sequencer handles for each QVIP interface
  mvc_sequencer uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr;

  // Top level environment configuration handle
  mldsa_env_configuration_t top_configuration;

  // Configuration handles to access interface BFM's
  // Local handle to register model for convenience
  mldsa_reg_model_top reg_model;
  uvm_status_e status;

  // pragma uvmf custom class_item_additional begin
  bit [31:0] data;
  bit [31:0] SEED [0:7]; //32 Bytes
  bit [31:0] SK []; //4896 Bytes
  bit [31:0] PK []; //2592 Bytes
  bit [31:0] MSG [0:15]; //64 Bytes
  bit [31:0] SIG []; //4628 Bytes
  bit [7:0]  CTX_SIZE;
  bit [31:0] CTX [0:63]; //256 Bytes
  bit [31:0] VERIF []; //64 Bytes
  // pragma uvmf custom class_item_additional end

  // ****************************************************************************
  function new( string name = "" );
    super.new( name );
    // Retrieve the configuration handles from the uvm_config_db

    // Retrieve top level configuration handle
    if ( !uvm_config_db#(mldsa_env_configuration_t)::get(null,UVMF_CONFIGURATIONS, "TOP_ENV_CONFIG",top_configuration) ) begin
      `uvm_info("CFG", "*** FATAL *** uvm_config_db::get can not find TOP_ENV_CONFIG.  Are you using an older UVMF release than what was used to generate this bench?",UVM_NONE);
      `uvm_fatal("CFG", "uvm_config_db#(mldsa_env_configuration_t)::get cannot find resource TOP_ENV_CONFIG");
    end

    // Retrieve config handles for all agents

    // Assign the sequencer handles from the handles within agent configurations

    // Retrieve QVIP sequencer handles from the uvm_config_db
    if( !uvm_config_db #(mvc_sequencer)::get( null,UVMF_SEQUENCERS,"uvm_test_top.environment.qvip_ahb_lite_slave_subenv.ahb_lite_slave_0", uvm_test_top_environment_qvip_ahb_lite_slave_subenv_ahb_lite_slave_0_sqr) ) 
      `uvm_warning("CFG" , "uvm_config_db #( mvc_sequencer )::get cannot find resource ahb_lite_slave_0" ) 
    reg_model = top_configuration.mldsa_rm;
    if (reg_model == null) begin
      `uvm_fatal("CFG", "reg_model is null. Ensure that the register model is properly initialized.");
    end


    // pragma uvmf custom new begin
    // Construct arrays
    SK = new[1224];
    PK = new[648];
    SIG = new[1157];
    VERIF = new[16];
    // pragma uvmf custom new end

  endfunction

  // ****************************************************************************
  virtual task body();
    // pragma uvmf custom body begin

    // Construct sequences here

    mldsa_env_seq = mldsa_env_sequence_base_t::type_id::create("mldsa_env_seq");

    fork
    join
    reg_model.reset();
    // Start RESPONDER sequences here
    fork
    join_none
    // Start INITIATOR sequences here
    fork
    join

mldsa_env_seq.start(top_configuration.vsqr);

    // UVMF_CHANGE_ME : Extend the simulation XXX number of clocks after 
    // the last sequence to allow for the last sequence item to flow 
    // through the design.
    fork
    join

    // pragma uvmf custom body end
  endtask


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

  function void write_strm_msg_file(int fd, int bit_length_words, bit [31:0] array [], bit [1:0] padding, bit [31:0] data);
    int i;
    int words_to_write;

    // Write the data from the array to the file
    words_to_write = bit_length_words;
    for (i = 0; i < words_to_write; i++) begin
      $fwrite(fd, "%02X%02X%02X%02X", array[i][7:0],  array[i][15:8],
                                      array[i][23:16],array[i][31:24]);
    end
    if (padding == 1)
      $fwrite(fd, "%02X", (data & 8'hFF));
    else if (padding == 2)
      $fwrite(fd, "%04X", (data & 16'hFFFF));
    else if (padding == 3)
      $fwrite(fd, "%06X", (data & 24'hFFFFFF));
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

  function void parse_hex_to_array(string hex_data, ref bit [31:0] array []);
    int hex_len;
    int bit_length_words;
    bit [31:0] word;
    bit [31:0] reversed_word;
    string chunk;

    // Calculate the number of words from the length of the hexadecimal string
    hex_len = hex_data.len();
    bit_length_words = hex_len / 8;
    array = new[bit_length_words];

    // Parse the hexadecimal string into the array
    for (int i = 0; i < bit_length_words; i++) begin
      chunk = hex_data.substr(8*i, 8*(i + 1)-1);
      void'($sscanf(chunk, "%08x", word));
      reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]};
      // Reverse the order of the words as well as their bytes
      array[i] = reversed_word;
    end
  endfunction

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end

