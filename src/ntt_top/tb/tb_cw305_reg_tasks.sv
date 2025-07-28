// parameter pADDR_WIDTH = 20;
//     parameter pBYTECNT_SIZE = 8;
//     parameter pUSB_CLOCK_PERIOD = 10;
//     parameter pPLL_CLOCK_PERIOD = 10;
//     parameter pSEED = 1;
//     parameter pTIMEOUT = 30000;
//     parameter pVERBOSE = 0;
//     parameter pDUMP = 0;

    // reg usb_clk;
    // reg usb_clk_enable;
    // wire [7:0] usb_data;
    // reg [7:0] usb_wdata;
    // reg [pADDR_WIDTH-1:0] usb_addr;
    // reg usb_rdn;
    // reg usb_wrn;
    // reg usb_cen;
    // reg usb_trigger;

task write_byte;
   input [1:0] block;
   input [pADDR_WIDTH-pBYTECNT_SIZE-1:0] address;
   input [pBYTECNT_SIZE-1:0] subbyte;
   input [7:0] data;
   @(posedge usb_clk);
   usb_addr = {block, address[5:0], subbyte};
   usb_wdata = data;
   usb_wrn = 0;
   @(posedge usb_clk);
   usb_cen = 0;
   @(posedge usb_clk);
   usb_cen = 1;
   @(posedge usb_clk);
   usb_wrn = 1;
   @(posedge usb_clk);
endtask


task read_byte;
   input [1:0] block;
   input [pADDR_WIDTH-pBYTECNT_SIZE-1:0] address;
   input [pBYTECNT_SIZE-1:0] subbyte;
   output [7:0] data;
   @(posedge usb_clk);
   usb_addr = {block, address[5:0], subbyte};
   @(posedge usb_clk);
   usb_rdn = 0;
   usb_cen = 0;
   @(posedge usb_clk);
   @(posedge usb_clk);
   #1 data = usb_data;
   @(posedge usb_clk);
   usb_rdn = 1;
   usb_cen = 1;
   repeat(2) @(posedge usb_clk);
endtask

task write_a_word(input [31 : 0]  address,
               input [31 : 0] word);
   begin
   for (int i=0; i<4; i++)
      begin
         write_byte(0, address, i, word[i*8 +: 8]);
      end
   end
endtask // write_ahb_word

task write_a_dword(input [11 : 0]  address,
               input [63 : 0] word);
   begin
   for (int i=0; i<8; i++)
      begin
         write_byte(0, address, i, word[i*8 +: 8]);
      end
   end
endtask // write_ahb_word

task write_a_full_word(input [31 : 0]  address,
                  input [31 : 0] word);
   begin
      write_a_word(REG_CRYPT_ADDR, address);
      write_a_word(REG_CRYPT_WR, word);
      write_byte(0, REG_CRYPT_CTRL, 0, 8'b1);
   end
endtask // write_a_full_word

task write_a_full_dword(input [11 : 0]  address,
                  input [63 : 0] word);
   begin
      write_a_word(REG_CRYPT_ADDR, address);
      write_a_dword(REG_CRYPT_WR, word);
      write_byte(0, REG_CRYPT_CTRL, 0, 8'b1);
   end
endtask // write_a_full_word

task write_block(input [31:0] addr, input integer len, input bit [31:0] block[]);
  integer i;
  begin
    for (i = 0; i < len; i = i + 1) begin
      // Print the value before writing
    //   $display("Writing to address %h: block[%0d] = %h", addr + 4 * i, i, block[len-1-i]);
      write_a_full_word(addr + 4 * i, block[len-1-i]);
    end
  end
endtask // write_block


task write_bytes;
   input [1:0] block;
   input [7:0] bytes;
   input [pADDR_WIDTH-pBYTECNT_SIZE-1:0] address;
   input [255:0] data;
   int subbyte;
   for (subbyte = 0; subbyte < bytes; subbyte = subbyte + 1)
      write_byte(block, address, subbyte, data[subbyte*8 +: 8]);
   if (pVERBOSE)
      $display("Write %0h", data);
endtask

task read_a_word(input [31 : 0]  address, output [31 : 0]  read_data);
   begin
   for (int i=0; i<4; i++)
      begin
         read_byte(0, address, i, read_data[8*i +: 8]);
      end
   end
endtask // read_word_ahb

task read_a_dword(input [11 : 0]  address, output [63 : 0]  read_data);
   begin
   for (int i=0; i<8; i++)
      begin
         read_byte(0, address, i, read_data[8*i +: 8]);
      end
   end
endtask // read_dword_ahb

task read_a_full_word(input [31 : 0]  address, output [31 : 0]  read_data);
   begin
      write_a_word(REG_CRYPT_ADDR, address);
      @(posedge usb_clk);
      @(posedge usb_clk);
      write_byte(0, REG_CRYPT_CTRL, 0, 8'h2);
      @(posedge usb_clk);
      @(posedge usb_clk);
      read_a_word(REG_CRYPT_RD, read_data);
   end
endtask // read_word

task read_a_full_dword(input [11 : 0]  address, output [63 : 0]  read_data);
   begin
      write_a_word(REG_CRYPT_ADDR, address);
      @(posedge usb_clk);
      @(posedge usb_clk);
      write_byte(0, REG_CRYPT_CTRL, 0, 8'h2);
      @(posedge usb_clk);
      @(posedge usb_clk);
      read_a_dword(REG_CRYPT_RD, read_data);
   end
endtask // read_word

task read_bytes;
   input [1:0] block;
   input [7:0] bytes;
   input [pADDR_WIDTH-pBYTECNT_SIZE-1:0] address;
   output [255:0] data;
   int subbyte;
   for (subbyte = 0; subbyte < bytes; subbyte = subbyte + 1)
      read_byte(block, address, subbyte, data[subbyte*8 +: 8]);
   if (pVERBOSE)
      $display("Read %0h", data);
endtask



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
      read_a_full_word(addr + 4 * i, block[i]);
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
      read_a_full_word(addr + 4 * i, block[i]);
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
endtask // read_block_SIG


task trig_IP(input [2 : 0] cmd);
begin
    write_a_full_word(ADDR_CTRL, cmd);
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

    wait_ready();
    
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
    #400;
    wait_ready();
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


task wait_ready;
   bit [31:0] status_check; 
    begin
      status_check = 0;
      read_a_full_word(ADDR_STATUS, status_check);
      while (status_check == 0)
      begin
        read_a_full_word(ADDR_STATUS, status_check);
      end
      $display("The design is ready %h", status_check);
    end
endtask // wait_ready

task ntt_wait_ready;
  bit [63:0] status_check;

  status_check = 0;
  $display("Waiting for NTT to be ready...");
  read_a_full_dword(NTT_STATUS_REG, status_check);
  while (status_check == 0) begin
    read_a_full_dword(NTT_STATUS_REG, status_check);
  end
  $display("NTT is ready with status: %h", status_check);
endtask

task init_mem_with_coeffs;
  $display("Initializing memory with coefficients...");
  for (int i = 0; i < 256; i++) begin
    write_a_full_dword(NTT_SRC_BASE_ADDR+i, i);
    write_a_full_dword((NTT_INTERIM_BASE_ADDR*4)+i, i*10);
    // $display("Writing coefficient %0d to address %h", i, NTT_SRC_BASE_ADDR+i);
  end
endtask

task init_mem_with_8_coeffs;
  $display("Initializing memory with coefficients...");
  for (int i = 0; i < 8; i++) begin
    write_a_full_dword(NTT_SRC_BASE_ADDR+i, i);
    write_a_full_dword((NTT_INTERIM_BASE_ADDR*4)+i, i*10);
    // $display("Writing coefficient %0d to address %h", i, NTT_SRC_BASE_ADDR+i);
  end
endtask

  //----------------------------------------------------------------
  // Program base address
  //----------------------------------------------------------------
  task pgm_base_addr(input logic [13:0] pwm_src_b, input logic [13:0] src, input logic [13:0] interim, input logic [13:0] dst);
    $display("Programming base address...");
    write_a_full_dword(NTT_BASE_ADDR_REG, {8'h0, 14'(pwm_src_b), 14'(src), 14'(interim), 14'(dst)});
  endtask

  //----------------------------------------------------------------
  // Start LFSR
  //----------------------------------------------------------------
  task start_lfsr();
    $display("Starting LFSR...");
    write_a_full_dword(NTT_LFSR_SEED0_0_REG, {$urandom(), $urandom()});
    write_a_full_dword(NTT_LFSR_SEED0_1_REG, {$urandom(), $urandom()});
    write_a_full_dword(NTT_LFSR_SEED1_0_REG, {$urandom(), $urandom()});
    write_a_full_dword(NTT_LFSR_SEED1_1_REG, {$urandom(), $urandom()});
    write_a_full_dword(NTT_LFSR_EN_REG, 1); // Enable LFSR
    $display("LFSR started.");
  endtask

  //----------------------------------------------------------------
  // Zeroize dut
  //----------------------------------------------------------------
  task zeroize_dut();
    $display("Zeroizing DUT...");
    write_a_full_dword(NTT_CTRL_REG, {56'h0, 1'b1, 7'h0}); // Zeroize command
  endtask

  //----------------------------------------------------------------
  // NTT mode
  //----------------------------------------------------------------

task ct_test (input logic shuf_en, input logic [2:0] mode);
  $display("Starting CT test with shuf_en = %0d", shuf_en);

  $display("Writing control register with shuf_en = %0d", shuf_en);
  write_a_full_dword(NTT_CTRL_REG, {56'h0, 1'b0, shuf_en, 1'b0, 1'b1, 1'b0, mode});

  $display("Triggering NTT operation");
  write_a_full_dword(NTT_ENABLE_REG, {63'h0, 1'b1});

  $display("Waiting for NTT to complete");
  ntt_wait_ready();

  $display("CT test completed");
endtask

  //----------------------------------------------------------------
  // INTT mode
  //----------------------------------------------------------------
task gs_test (input logic shuf_en, input logic mask_en, input logic check_en, input logic [2:0] mode);
  logic [63:0] read_data, read_share0, read_share1;
  int error_ctr = 0;
  logic [63:0] test_vector_mem [255:0];
  logic [63:0] masked_test_vector_mem [511:0];

  $display("Initializing memory with coefficients from ct...");

  if (mask_en) begin
    $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/gs_masked_input.hex", masked_test_vector_mem);
    for (int i = 0; i < 512; i++) begin
      write_a_full_dword(NTT_SRC_BASE_ADDR+i, masked_test_vector_mem[i]);
      // $display("Writing coefficient %0d to address %h", i, NTT_SRC_BASE_ADDR+i);
    end

  end
  else begin
    $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/gs_unmasked_input.hex", test_vector_mem);
    for (int i = 0; i < 256; i++) begin
      write_a_full_dword(NTT_SRC_BASE_ADDR+i, test_vector_mem[i]);
      // $display("Writing coefficient %0d to address %h", i, NTT_SRC_BASE_ADDR+i);
    end

  end
  
  $display("Starting GS test with shuf_en = %0d, mask_en = %0d, check_en = %0d", shuf_en, mask_en, check_en);

  // Write control register
  write_a_full_dword(NTT_CTRL_REG, {56'h0, 1'b0, shuf_en, mask_en, 1'b1, 1'b0, mode});

  // Trigger NTT operation
  write_a_full_dword(NTT_ENABLE_REG, {63'h0, 1'b1});

  // Wait for NTT to complete
  ntt_wait_ready();

  $display("GS done");

  if (check_en) begin
      for (int i = 0; i < 256; i++) begin
        read_a_full_dword((NTT_DST_BASE_ADDR*4)+i, read_data);
        if (read_data != i) begin
          $display("Mismatch at index %0d: Expected %h, got %h", i, i, read_data);
          error_ctr = error_ctr + 1;
        end 
        // else begin
        //   $display("Index %0d: Passed with value %h", i, read_data);
        // end
      end

    if (error_ctr == 0) begin
      $display("GS test passed with no errors.");
    end else begin
      $display("GS test completed with %0d errors.", error_ctr);
    end

  end
endtask

  //----------------------------------------------------------------
  // PWM mode
  //----------------------------------------------------------------
task pwm_test (input logic mlkem, input logic shuf_en, input logic mask_en, input acc_en, input logic check_en, input logic [2:0] mode);
  logic [63:0] read_data, exp_data, mlkem_exp_data;
  logic [63:0] read_share0, read_share1;
  logic [23:0] test_vector_mem [255:0];
  int error_ctr = 0;

  $display("Starting PWM test with shuf_en = %0d, mask_en = %0d, acc_en = %0d, check_en = %0d", shuf_en, mask_en, acc_en, check_en);

  // Write control register
  write_a_full_dword(NTT_CTRL_REG, {54'h0, mlkem, 1'b0, 1'b0, shuf_en, mask_en, 1'b1, acc_en, mode});

  // Trigger NTT operation
  write_a_full_dword(NTT_ENABLE_REG, {63'h0, 1'b1});

  // Wait for NTT to complete
  ntt_wait_ready();

  $display("PWM done");

  if (check_en) begin
    if (!shuf_en & mask_en) begin
      if (acc_en)
        $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/pwm_masked_acc_output.hex", test_vector_mem);
      else
        $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/pwm_masked_output.hex", test_vector_mem);

      for (int i = 0; i < 256; i++) begin
        read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2), read_share0);
        read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2)+1, read_share1);
        read_data = (read_share0 + read_share1);
        if (read_data[23:0] != test_vector_mem[i]) begin
          $display("Mismatch at index %0d: Expected %h, got %h", i, test_vector_mem[i], read_data[23:0]);
          error_ctr = error_ctr + 1;
        end
      end  
    end
    else begin
      for (int i = 0; i < 256; i++) begin
        if (mask_en) begin
          read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2), read_share0);
          read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2)+1, read_share1);
          read_data = (read_share0 + read_share1);
        end
        else begin
          read_a_full_dword((NTT_DST_BASE_ADDR*4)+i, read_data);
        end

        if (acc_en)
          exp_data = (((i*(i*10))%MLDSA_Q)+((i*(i*10))%MLDSA_Q))%MLDSA_Q;
        else
          exp_data = (i*(i*10)) % MLDSA_Q;

        if (read_data[23:0] != exp_data) begin
          $display("Mismatch at index %0d: Expected %h, got %h", i, exp_data, read_data[23:0]);
          error_ctr = error_ctr + 1;
        end
      end
    end

    if (error_ctr == 0) begin
      $display("PWM test passed with no errors.");
    end else begin
      $display("PWM test completed with %0d errors.", error_ctr);
    end
  end
endtask

  //----------------------------------------------------------------
  // PWM Sampler mode
  //----------------------------------------------------------------
task pwm_sampler_test (input logic mask_en, input logic acc_en, input logic check_en, input logic [2:0] mode);
  logic [63:0] read_data, read_share0, read_share1;
  int error_ctr = 0;
  logic rand_svalid;
  logic [63:0] test_vector_mem [255:0];
  int count;
  logic [383:0] sampler_input;
  $display("Starting PWM sampler test with mask_en = %0d, acc_en = %0d", mask_en, acc_en);

  $display("Writing control register with mask_en = %0d, acc_en = %0d", mask_en, acc_en);
  write_a_full_dword(NTT_CTRL_REG, {55'h0, 1'b1, 1'b0, 1'b0, mask_en, 1'b0, acc_en, mode});

  count = 0;

  $display("Writing enable register to trigger PWM sampler mode");
  write_a_full_dword(NTT_ENABLE_REG, {63'h0, 1'b1});

  $display("Writing sampler data to dut");

  while (count < 12) begin
    rand_svalid = $urandom_range(0, 1);
    if (rand_svalid) begin
      sampler_input = {24'((count*4)+3), 24'((count*4)+2), 24'((count*4)+1), 24'((count*4))};

      count++;
      write_a_full_dword(NTT_SAMPLER_INPUT_0_REG, sampler_input[23:0]);
      write_a_full_dword(NTT_SAMPLER_INPUT_1_REG, sampler_input[47:24]);
      write_a_full_dword(NTT_SAMPLER_INPUT_2_REG, sampler_input[71:48]);
      write_a_full_dword(NTT_SAMPLER_INPUT_3_REG, sampler_input[95:72]);
    end
    write_a_full_dword(NTT_CTRL_REG, {55'h0, 1'b1, 1'b0, 1'b0, mask_en, rand_svalid,acc_en,3'h2} );
  end

  $display("Waiting for PWM sampler to complete");
  ntt_wait_ready();
  $display("PWM sampler done");

  if (check_en) begin
      if (acc_en)
        $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/pwm_sampler_acc_output.hex", test_vector_mem);
      else
        $readmemh("/home/ws/caliptra/kupadhyayula/ws_may12025/pwm_sampler_output.hex", test_vector_mem);

    for (int i = 0; i < 256; i++) begin
        if (mask_en) begin
          read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2), read_share0);
          read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2)+1, read_share1);
          read_data = (read_share0 + read_share1);
        end
        else begin
          read_a_full_dword((NTT_DST_BASE_ADDR*4)+i, read_data);
        end

        if (read_data[23:0] != test_vector_mem[i]) begin
          $display("Mismatch at index %0d: Expected %h, got %h", i, test_vector_mem[i], read_data[23:0]);
          error_ctr = error_ctr + 1;
        end
    end

    if (error_ctr == 0) begin
      $display("PWM sampler test passed with no errors.");
    end else begin
      $display("PWM sampler test completed with %0d errors.", error_ctr);
    end
  end
endtask


//----------------------------------------------------------------

task pwm_test_simple_test (input logic mlkem, input logic  mask_en, input logic shuf_en, input acc_en, input logic check_en, input logic [2:0] mode);
  logic [63:0] read_data, exp_data, mlkem_exp_data;
  logic [63:0] read_share0, read_share1;
  logic [23:0] test_vector_mem [255:0];
  int error_ctr;
 
  $display("Starting PWM test with mlkem = %0d, shuf_en = %0d, mask_en = %0d, acc_en = %0d, check_en = %0d", mlkem, shuf_en, mask_en, acc_en, check_en);
  error_ctr = 0;
  // Write control register
  write_a_full_dword(NTT_CTRL_REG, {55'h0, mlkem, 1'b0, 1'b0, shuf_en, mask_en, 1'b1, acc_en, mode});
 
  // Trigger NTT operation
  write_a_full_dword(NTT_ENABLE_REG, {63'h0, 1'b1});
 
  // Wait for NTT to complete
  ntt_wait_ready();
 
  $display("PWM done");
  for (int i = 0; i < 16; i++) begin
    if (mask_en) begin
      read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2), read_share0);
      read_a_full_dword((NTT_DST_BASE_ADDR*8)+(i*2)+1, read_share1);
      read_data = (read_share0 + read_share1);
    end
    else begin
      read_a_full_dword((NTT_DST_BASE_ADDR*4)+i, read_data);
    end
    $display("Index %0d: got %h", i, read_data[23:0]);
  end
 
endtask
