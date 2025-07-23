// parameter NTT_SRC_BASE_ADDR = 12'h0;
//    parameter NTT_INTERIM_BASE_ADDR = 12'h40;
//    parameter NTT_DST_BASE_ADDR = 12'h80;
//    parameter NTT_STATUS_REG = 12'hFFF;
//    parameter NTT_ENABLE_REG = 12'hFFE;
//    parameter NTT_CTRL_REG = 12'hFFD;
//    parameter NTT_BASE_ADDR_REG = 12'hFFC;
//    parameter NTT_SAMPLER_INPUT_0_REG = 12'hFFB;
//    parameter NTT_SAMPLER_INPUT_1_REG = 12'hFFA;
//    parameter NTT_SAMPLER_INPUT_2_REG = 12'hFF9;
//    parameter NTT_SAMPLER_INPUT_3_REG = 12'hFF8;
//    parameter NTT_LFSR_EN_REG = 12'hFF7;
//    parameter NTT_LFSR_SEED0_0_REG = 12'hFF6;
//    parameter NTT_LFSR_SEED0_1_REG = 12'hFF5;
//    parameter NTT_LFSR_SEED1_0_REG = 12'hFF4;
//    parameter NTT_LFSR_SEED1_1_REG = 12'hFF3;


  //  parameter pADDR_WIDTH = 20;
  //   parameter pBYTECNT_SIZE = 8;
  //   parameter pUSB_CLOCK_PERIOD = 10;
  //   parameter pPLL_CLOCK_PERIOD = 10;
  //   parameter pSEED = 1;
  //   parameter pTIMEOUT = 30000;
  //   parameter pVERBOSE = 0;
  //   parameter pDUMP = 0;

  //  reg [63:0] read_data;
  //  reg [63:0] reg_address;
//----------------------------------------------------------------
  // reset_dut()
  //
  // Toggle reset to put the DUT into a well known state.
  //----------------------------------------------------------------
  // task reset_dut;
  //   begin
  //     $display("*** Toggle reset.");
  //     reset_n_tb = 0;

  //     #(2 * USB_CLK_PERIOD);

  //     #(2 * USB_CLK_PERIOD);
  //     reset_n_tb = 1;

  //     $display("");
  //   end
  // endtask // reset_dut

  //----------------------------------------------------------------
  // display_test_results()
  //
  // Display the accumulated test results.
  //----------------------------------------------------------------
  // task display_test_results;
  //   begin
  //     if (error_ctr == 0)
  //       begin
  //         $display("*** All %02d test cases completed successfully", tc_ctr);
  //         $display("* TESTCASE PASSED");
  //       end
  //     else
  //       begin
  //         $display("*** %02d tests completed - %02d test cases did not complete successfully.",
  //                  tc_ctr, error_ctr);
  //         $display("* TESTCASE FAILED");
  //       end
  //   end
  // endtask // display_test_results


  //----------------------------------------------------------------
  // wait_ready_cw310()
  //
  // Wait for the ready flag in the dut to be set.
  // (Actually we wait for either ready or valid to be set.)
  //
  // Note: It is the callers responsibility to call the function
  // when the dut is actively processing and will in fact at some
  // point set the flag.
  //----------------------------------------------------------------
  task wait_ready_cw310;
    begin
      read_single_word(NTT_STATUS_REG); //(ADDR_STATUS);
      while (read_data == 0)
        begin
          read_single_word(NTT_STATUS_REG); //(ADDR_STATUS);
        end
    end
  endtask // wait_ready_cw310

  //----------------------------------------------------------------
  // write_single_word()
  //
  // Write the given word to the DUT using the DUT interface.
  //----------------------------------------------------------------
  task write_single_byte(input [pADDR_WIDTH-pBYTECNT_SIZE-1 : 0]  address, input [pBYTECNT_SIZE-1 : 0] byte_cnt,
                  input [7 : 0] word);
    begin
      reg_address = {address, byte_cnt};
      usb_write_data = word;
      usb_reg_read = 0;
      usb_reg_write = 1;
      usb_reg_addrvalid = 1;
      
      #(USB_CLK_PERIOD);
      usb_reg_write = 0;
      usb_reg_addrvalid = 0;
    end
  endtask // write_single_byte
  
  task write_ahb_word(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      for (int i=0; i<4; i++)
        begin
          write_single_byte(address, i, word[i*8 +: 8]);
          #(10 * USB_CLK_PERIOD);
        end
    end
  endtask // write_ahb_word

  task write_ahb_dword(input [11 : 0]  address,
                  input [63 : 0] dword);
    begin
      for (int i=0; i<8; i++)
        begin
          write_single_byte(address, i, dword[i*8 +: 8]);
          #(10 * USB_CLK_PERIOD);
        end
    end
  endtask // write_ahb_dword
  
  
  task write_single_word(input [31 : 0]  address,
                  input [31 : 0] word);
    begin
      write_ahb_word(REG_CRYPT_ADDR, address);
      write_ahb_word(REG_CRYPT_WR, word);
      write_single_byte(REG_CRYPT_CTRL, 0, 1);
      #(50*USB_CLK_PERIOD);
    end
  endtask // write_single_word

  task write_single_dword (input [11:0] address, input [63:0] dword);
    begin
      write_ahb_dword(REG_CRYPT_ADDR, address);
      write_ahb_dword(REG_CRYPT_WR, dword);
      write_single_byte(REG_CRYPT_CTRL, 0, 1);
      #(50*USB_CLK_PERIOD);
    end
  endtask // write_single_dword

  
//----------------------------------------------------------------
// write_block()
// 
// Write the given block of variable length to the DUT.
// 'len' specifies how many 32-bit words are in the block.
//----------------------------------------------------------------
task write_block(input [31:0] addr, input integer len, input bit [31:0] block[]);
  integer i;
  begin
    for (i = 0; i < len; i = i + 1) begin
      // Print the value before writing
    //   $display("Writing to address %h: block[%0d] = %h", addr + 4 * i, i, block[len-1-i]);
      write_single_word(addr + 4 * i, block[len-1-i]);
    end
  end
endtask // write_block


  //----------------------------------------------------------------
  // read_word()
  //
  // Read a data word from the given address in the DUT.
  // the word read will be available in the global variable
  // read_data.
  //----------------------------------------------------------------
  task read_single_byte(input [pADDR_WIDTH-pBYTECNT_SIZE-1 : 0]  address, input [pBYTECNT_SIZE-1 : 0] byte_cnt);
    begin
      reg_address = {address, byte_cnt};
      usb_reg_read = 1;
      usb_reg_write = 0;
      usb_reg_addrvalid = 1;
      
      #(USB_CLK_PERIOD);
      usb_reg_read = 0;
      usb_reg_addrvalid = 0;
    end
  endtask // read_single_byte
  
  task read_word_ahb(input [31 : 0]  address);
    begin
     for (int i=0; i<4; i++)
        begin
          read_single_byte(address, i);
          read_data[8*i +: 8] = usb_read_data;
          #(10 * USB_CLK_PERIOD);
        end
    end
  endtask // read_word_ahb

  task read_dword_ahb(input [11 : 0]  address);
    begin
     for (int i=0; i<8; i++)
        begin
          read_single_byte(address, i);
          read_data[8*i +: 8] = usb_read_data;
          #(10 * USB_CLK_PERIOD);
        end
    end
  endtask // read_dword_ahb
  
  task read_single_word(input [31 : 0]  address);
    begin
      write_ahb_word(REG_CRYPT_ADDR, address);
      write_single_byte(REG_CRYPT_CTRL, 0, 2);
      #(50*USB_CLK_PERIOD);
      read_word_ahb(REG_CRYPT_RD);
    end
  endtask // read_word

  task read_single_dword(input [11 : 0]  address);
    begin
      write_ahb_word(REG_CRYPT_ADDR, address);
      write_single_byte(REG_CRYPT_CTRL, 0, 2);
      #(50*USB_CLK_PERIOD);
      read_dword_ahb(REG_CRYPT_RD);
    end
  endtask // read_word


  //----------------------------------------------------------------
// read_block()
// 
// Read the block from the DUT. The resulting block will be 
// available in the provided array `block`.
//----------------------------------------------------------------
task read_block_PK(input [31:0] addr, output bit [31:0] block[648]);
  integer i;
  bit mismatch_found;
  begin
    mismatch_found = 0;
    for (i = 0; i < 648; i = i + 1) begin
      read_single_word(addr + 4 * i);
      block[i] = read_data;
      // Print the value after reading
    //   $display("Read from address %h: block[%0d] = %h and read data = %h and time  %t", addr + 4 * i, i, block[i], read_data, $time);
    end

    foreach (PK[i]) begin
        if (PK[647-i] != block[i]) begin
        $display("Mismatch at index %0d: PK Expected: %h, Actual: %h", i, PK[i], block[i]);
        mismatch_found = 1; // Flag to indicate a mismatch was found
        error_ctr = error_ctr + 1;
        end
    end

    // If no mismatches were found, print "Passed"
    if (!mismatch_found) begin
        $display("Passed: All elements match.");
    end
  end
endtask // read_block_PK

task read_block_SIG(input [31:0] addr, output bit [31:0] block[1157]);
  integer i;
  bit mismatch_found;
  begin
    mismatch_found = 0;
    for (i = 0; i < 1157; i = i + 1) begin
      read_single_word(addr + 4 * i);
      block[i] = read_data;
      // Print the value after reading
    //   $display("Read from address %h: block[%0d] = %h and read data = %h and time  %t", addr + 4 * i, i, block[i], read_data, $time);
    end// Compare elements using foreach

    foreach (SIG[i]) begin
        if (SIG[i] != block[i]) begin
          $display("Mismatch at index %0d: SIG Expected: %h, Actual: %h", i, SIG[i], block[i]);
          mismatch_found = 1; // Flag to indicate a mismatch was found
          error_ctr = error_ctr + 1;
        end
    end

    // If no mismatches were found, print "Passed"
    if (!mismatch_found) begin
        $display("Passed: All elements match.");
    end
  end
endtask // read_block_PK


//----------------------------------------------------------------
// trig_IP()
//
// Write the given word to the DUT using the DUT interface.
//----------------------------------------------------------------
task trig_IP(input [2 : 0] cmd);
begin
    write_single_word(ADDR_CTRL, cmd);
    #(CLK_PERIOD);
end
endtask // trig_IP

task read_test_vectors(int fin, int fin2);
    bit [255:0] unorganized_seed;      // 64 hex characters = 256 bits
    bit [511:0] unorganized_msg;       // 128 hex characters = 512 bits
    bit [20735:0] unorganized_pk;      // 2592 hex characters = 20736 bits
    bit [37023:0] unorganized_sig;     // 4628 hex characters = 37024 bits
    integer rv;
    bit [31:0] word, reversed_word;
    integer i;

    // Read SEED (64 hex characters)
    rv = $fscanf(fin, "%h\n", unorganized_seed);
    if (rv != 1) begin
        $error("Failed to read SEED.");
        $fclose(fin);
        return;
    end
    $display("SEED: %h", unorganized_seed);
    // Split SEED into 32-bit words and reverse byte order
    for (i = 0; i < 8; i++) begin
        word = unorganized_seed[255 - i*32 -: 32];  // Extract 32-bit word
        reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]}; // Reverse byte order
        SEED[i] = reversed_word;  // Assign to dynamic array
        // $display("Read word: %h, Reversed word: %h", word, SEED[i]);
    end

    // Read MSG (128 hex characters)
    rv = $fscanf(fin, "%h\n", unorganized_msg);
    if (rv != 1) begin
        $error("Failed to read MSG.");
        $fclose(fin);
        return;
    end
    $display("MSG: %h", unorganized_msg);
     // Split MSG into 32-bit words and reverse byte order
    for (i = 0; i < 16; i++) begin
        word = unorganized_msg[511 - i*32 -: 32];  // Extract 32-bit word
        reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]}; // Reverse byte order
        MSG[i] = reversed_word;  // Assign to dynamic array
        // $display("Read word: %h, Reversed word: %h", word, MSG[i]);
    end


    // Read PK (2592 hex characters = 20736 bits)
    rv = $fscanf(fin2, "%h\n", unorganized_pk);
    if (rv != 1) begin
        $error("Failed to read PK.");
        $fclose(fin2);
        return;
    end
    // Split PK into 32-bit words and reverse byte order
    $display("PK: %h", unorganized_pk);
    for (i = 0; i < 648; i++) begin
        word = unorganized_pk[20735 - i*32 -: 32];  // Extract 32-bit word
        reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]}; // Reverse byte order
        PK[i] = reversed_word;  // Assign to dynamic array
        // $display("Read word: %h, Reversed word: %h", word, PK[i]);
    end

    // Read SIG (4628 hex characters = 37024 bits)
    rv = $fscanf(fin2, "%h\n", unorganized_sig);
    if (rv != 1) begin
        $error("Failed to read SIG.");
        $fclose(fin2);
        return;
    end
    // Split SIG into 32-bit words and reverse byte order
    $display("SIG: %h", unorganized_sig);
    for (i = 0; i < 1157; i++) begin
        word = unorganized_sig[37023 - i*32 -: 32];  // Extract 32-bit word
        reversed_word = {word[7:0], word[15:8], word[23:16], word[31:24]}; // Reverse byte order
        SIG[1156-i] = reversed_word;  // Assign to dynamic array
        // $display("Read word: %h, Reversed word: %h", word, SIG[i]);
    end
    // SIG[0] = SIG[0] >> 8;


endtask

//----------------------------------------------------------------
  // mldsa_keygen_and_signing_test()
  //
  // Perform a single point multiplication block test.
  //----------------------------------------------------------------
  task mldsa_keygen_and_signing_test();
    string input_file;
    string output_file;
    string line;
    int words_read;
    bit [31:0] value;
    int fd, fd2;
    reg [31  : 0]   start_time;
    reg [31  : 0]   end_time;
    begin
        
        input_file = "./keygen_and_signing_input.hex";
        output_file = "./keygen_and_signing_output.hex";        

    wait_ready_cw310();
    
    fd = $fopen(input_file, "r");
    if (fd == 0) begin
        $display("Failed to open input_file: %s", input_file);
    end
    fd2 = $fopen(output_file, "r");
    if (fd2 == 0) begin
        $display("Failed to open output_file: %s", output_file);
    end
    read_test_vectors(fd, fd2);
    $fclose(fd);
    $fclose(fd2);

        $display("*** TC %0d keygen and signing test started.", tc_number);  
        $display("*** TC %0d writing seed value", tc_number);
        write_block(ADDR_SEED_START, 8, SEED);
        $display("*** TC %0d writing MSG value", tc_number);
        write_block(ADDR_MSG_START, 16, MSG);
        $display("*** TC %0d writing SIGN_RND value", tc_number);
        write_block(ADDR_SIGN_RND_START, 8, SIGN_RND);


    $display("*** TC %0d starting MLDSA keygen and signing flow", tc_number);
    start_time = cycle_ctr;
    trig_IP(3'd4);      
    wait_ready_cw310();
    end_time = cycle_ctr - start_time;

        $display("*** TC %0d reading PUBLIC KEY", tc_number);
        read_block_PK(ADDR_PUBKEY_START, actual_PK);
        $display("*** TC %0d reading Signature", tc_number);
        read_block_SIG(ADDR_SIGN_START, actual_SIG);
        
      
    // $display("*** keygen and signing test processing time = %01d cycles.", end_time);
    // $display("*** TC %0d comparing PK", tc_number);
    // compare_arrays(PK, actual_PK);
    // $display("*** TC %0d comparing SIG", tc_number);
    // compare_arrays(SIG, actual_SIG);
    tc_ctr = tc_ctr + 1;  
    end
  endtask // mldsa_keygen_and_signing_test

  //----------------------------------------------------------------
  // init mem with coeffs
  //----------------------------------------------------------------
  task init_mem_with_coeffs();
    $display("Initializing memory with coefficients...");
    for (int i = 0; i < 256; i++) begin
      write_single_dword(NTT_SRC_BASE_ADDR + i, i); // Example initialization
    end
  endtask

  //----------------------------------------------------------------
  // init mem with shares
  //----------------------------------------------------------------
  task init_mem_with_shares();
    $display("Initializing memory with shares of coefficients...");
    for (int i = 0; i < 512; i+=2) begin
      write_single_dword(NTT_SRC_BASE_ADDR+i, i); //TODO: replace with actual shares
      write_single_dword(NTT_SRC_BASE_ADDR+i+1, i+1); //TODO: replace with actual shares
    end
  endtask

  //----------------------------------------------------------------
  // Program base address
  //----------------------------------------------------------------
  task pgm_base_addr();
    $display("Programming base address...");
    write_single_dword(NTT_BASE_ADDR_REG, {22'h0, NTT_SRC_BASE_ADDR, NTT_INTERIM_BASE_ADDR, NTT_DST_BASE_ADDR});
  endtask

  //----------------------------------------------------------------
  // Start LFSR
  //----------------------------------------------------------------
  task start_lfsr();
    $display("Starting LFSR...");
    write_single_dword(NTT_LFSR_SEED0_0_REG, {$urandom(), $urandom()});
    write_single_dword(NTT_LFSR_SEED0_1_REG, {$urandom(), $urandom()});
    write_single_dword(NTT_LFSR_SEED1_0_REG, {$urandom(), $urandom()});
    write_single_dword(NTT_LFSR_SEED1_1_REG, {$urandom(), $urandom()});
    write_single_word(NTT_LFSR_EN_REG, 1); // Enable LFSR
    $display("LFSR started.");
  endtask

  //----------------------------------------------------------------
  // Zeroize dut
  //----------------------------------------------------------------
  task zeroize_dut();
    $display("Zeroizing DUT...");
    write_single_dword(NTT_CTRL_REG, {56'h0, 1'b1, 7'h0}); // Zeroize command
  endtask

  //----------------------------------------------------------------
  // Wait for ready
  //----------------------------------------------------------------
  task wait_ready_cw310();
    $display("Waiting for DUT to be ready...");
    read_single_dword(NTT_STATUS_REG);
    while (read_data != 1) begin
      read_single_dword(NTT_STATUS_REG);
    end
    $display("DUT is ready.");
  endtask

  //----------------------------------------------------------------
  // NTT (ct mode)
  //----------------------------------------------------------------
  task ct_test (input logic shuf_en);
    $display("Starting CT test...");

    $display("Writing control register with shuf_en = %0d", shuf_en);
    write_single_dword(NTT_CTRL_REG, {56'h0, 1'b0, shuf_en, 1'b0, 1'b1, 1'b0, 3'h0}); // sampler mode, zeroize, shuf, mask, svalid, acc, CT mode

    $display("Writing enable register with NTT_ENABLE = 1");
    write_single_dword(NTT_ENABLE_REG, {63'h0, 1'b1}); // Enable NTT

    $display("Waiting for NTT to complete...");
    wait_ready_cw310();

    $display("CT test completed.");
  endtask

  //----------------------------------------------------------------
  // NTT (gs mode)
  //----------------------------------------------------------------
  task gs_test (input logic shuf_en, input logic mask_en, input logic check_en);
    $display("Starting GS test...");

    $display("Writing control register with shuf_en = %0d, mask_en = %0d", shuf_en, mask_en);
    write_single_dword(NTT_CTRL_REG, {56'h0, 1'b0, shuf_en, mask_en, 1'b1, 1'b0, 3'h1}); // sampler mode, zeroize, shuf, mask, svalid, acc, GS mode

    $display("Writing enable register with NTT_ENABLE = 1");
    write_single_dword(NTT_ENABLE_REG, {63'h0, 1'b1}); // Enable NTT

    $display("Waiting for NTT to complete...");
    wait_ready_cw310();

    if (check_en) begin //TODO
      for (int i = 0; i < 256; i++) begin
        read_single_dword(i+(128*4));
        if (read_data != i)
          $error("Mismatch at address %0h: expected %0h, got %0h", i+(128*4), i, read_data);
      end
    end

    $display("GS test completed.");
  endtask

