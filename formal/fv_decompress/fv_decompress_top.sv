// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------


module fv_decompress_top
    //#$imports
    import abr_params_pkg::*;
    import decompress_defines_pkg::*;
    //$#//
#(
    //#$localparams
    //$#//
    parameter int ABR_NUM_NTT = 1
) (
    //#$ports
    input logic                                        pi_clk,
    input logic                                        pi_reset_n,
    input logic                                        pi_zeroize,
    input logic                                        pi_decompress_enable,
    input decompress_mode_t                            pi_mode,
    input logic [2:0]                                  pi_num_poly,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_src_base_addr,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               pi_dest_base_addr,
    input logic                                        pi_split_en_i,
    input logic [ABR_MEM_DATA_WIDTH-1:0]               pi_rand_i,
    input mem_if_t                                     po_mem_wr_req,
    //input logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] po_mem_wr_data,
    input logic [ABR_NUM_NTT-1:0][ABR_MEM_DATA_WIDTH-1:0] po_mem_wr_data,
    input logic                                        po_api_rd_en,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]               po_api_rd_addr,
    input logic [1:0][ABR_REG_WIDTH-1:0]               pi_api_rd_data, //DATA_WIDTH
    input logic                                        pi_api_rd_data_valid,
    input logic                                        po_decompress_done
    //$#//
);
    default clocking default_clk @(posedge pi_clk); endclocking

    localparam FV_PISO_BUFFER_W = 104;
    localparam FV_MIN_PISO_SPACE = 64;
    localparam FV_PISO_NO_READ_THRESH = FV_PISO_BUFFER_W - FV_MIN_PISO_SPACE;
    //localparam MEM_OUTPUT_RATE = (MLKEM_N/4) - 1;

    fv_decompress_constraints #(
        .ABR_NUM_NTT(ABR_NUM_NTT)
    ) fv_decompress_constraints_i (.*);

    logic fv_req_hold;
    logic fv_req_hold_ff;

    logic [7-1:0] fv_piso_used_slots_cntr;
    logic [7-1:0] fv_piso_used_slots_cntr_ff;

    // Once decompress enable is high, it means that decompression started and we should see requests to the api memory starting at base address
    logic fv_decompress_ongoing;
    logic fv_decompress_ongoing_ff;

    logic fv_api_mem_rd_req_valid;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_api_mem_rd_req_addr;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_api_mem_rd_req_addr_ff;

    // Every polynomial can cause up to 48 requests depending on the mode, and we can receive up to 8 polynomials in every decompression request
    // decompress 1 -> 4 requests
    // decompress 5 -> 20 requests
    // decompress 11 -> 44 requests
    // decompress 12 -> 48 requests
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_api_rd_req_cntr;
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_api_rd_req_cntr_ff;

    // The rate at which we write to the memory.
    // 48 -> decompress_12
    // 44 -> decompress_11
    // 20 -> decompress_20
    // 4  -> decmompress_1
    logic [6:0] fv_output_rate;

    // Free variable to select a single compression to check, there is no need to check every single compression
    logic fv_arbit_window;

    logic fv_api_req_tracking_started;
    logic fv_api_req_tracking_started_ff;

    logic fv_api_req_tracking_done;
    logic fv_api_req_tracking_done_ff;

    logic fv_api_req_decompression_done;
    logic fv_api_req_decompression_done_ff;
    logic fv_piso_is_reading; //new
    logic fv_read_done;//new
    logic [ABR_NUM_NTT-1:0][ABR_MEM_DATA_WIDTH-1:0]fv_mem_wr_data; //new

    always_comb begin
        fv_decompress_ongoing           = fv_decompress_ongoing_ff;
        fv_api_mem_rd_req_addr          = fv_api_mem_rd_req_addr_ff;
        fv_api_rd_req_cntr                    = fv_api_rd_req_cntr_ff;
        fv_piso_used_slots_cntr         = fv_piso_used_slots_cntr_ff;
        fv_req_hold                     = fv_req_hold_ff;
        fv_api_req_tracking_started     = fv_api_req_tracking_started_ff;
        fv_api_req_tracking_done        = fv_api_req_tracking_done_ff;
        fv_api_req_decompression_done   = fv_api_req_decompression_done_ff;
        fv_output_rate                  = '0;
        fv_api_mem_rd_req_valid         = '0;

        unique case (pi_mode)
            DECOMPRESS1: begin
                fv_output_rate = (1 * MLKEM_N)/64;
            end
            DECOMPRESS5: begin
                fv_output_rate = (5 * MLKEM_N)/64;
            end
            DECOMPRESS11: begin
                fv_output_rate = (11 * MLKEM_N)/64;
            end
            DECOMPRESS12: begin
                fv_output_rate = (12 * MLKEM_N)/64;
            end
            default: begin
                // Do nothing
            end
        endcase
        // read pointer is greater than or equal to the output rate, then we are reading from the piso
        fv_piso_is_reading = (fv_piso_used_slots_cntr_ff >= fv_output_rate);


        // Check if there is space in the piso based on the mode
        if((fv_api_rd_req_cntr != (pi_num_poly * fv_output_rate))) begin
           //fv_req_hold = ((FV_PISO_BUFFER_W - fv_piso_used_slots_cntr) < FV_MIN_PISO_SPACE);
            fv_req_hold = fv_piso_is_reading
                ? (fv_piso_used_slots_cntr > (FV_PISO_BUFFER_W- 7'd64 + fv_output_rate))
                : ((FV_PISO_BUFFER_W - fv_piso_used_slots_cntr) < FV_MIN_PISO_SPACE);
        end else begin
           fv_req_hold = 1'b0;
        end

        // Increment the number of taken slots every cycle during decompression based on the decompression type
        //api_rd_data_valid is high and fv_req_hold is low, then we are receiving data from the api memory and we should increment the number of taken slots in the piso
        if(pi_api_rd_data_valid && !fv_req_hold) begin //fv_decompress_ongoing
            fv_piso_used_slots_cntr = fv_piso_used_slots_cntr + 7'd64;
        end

        if(fv_decompress_ongoing && (fv_api_rd_req_cntr == (pi_num_poly * fv_output_rate)) && !fv_req_hold && !fv_req_hold_ff) begin
            fv_decompress_ongoing       = '0;
            fv_api_mem_rd_req_addr      = '0;
            fv_api_rd_req_cntr          = '0;
            fv_piso_used_slots_cntr     = '0;
            fv_api_req_tracking_done    = 1'b1;
        end
        fv_read_done = (fv_api_rd_req_cntr == (pi_num_poly * fv_output_rate));
        //mem_rd_pace is also used to pace the requests to the memory, so we should only send requests to the memory when mem_rd_pace is high
        if(decompress_top.mem_rd_pace[0] && fv_decompress_ongoing && !fv_read_done) begin //fv_decompress_ongoing && !fv_req_hold
            // send requests to the memory
            fv_api_mem_rd_req_valid = 1'b1;
            fv_api_mem_rd_req_addr++;
            fv_api_rd_req_cntr++;
        end

        if(pi_decompress_enable  &&  fv_arbit_window && !fv_api_req_tracking_started) begin
            // Decompression started
            fv_decompress_ongoing   = 1'b1;
            // Tracked decompression started
            fv_api_req_tracking_started = 1'b1;
            // Send the first request
            fv_api_mem_rd_req_valid = 1'b1;
            fv_api_mem_rd_req_addr  = pi_src_base_addr;
            fv_api_rd_req_cntr++;
        end

        //if(fv_decompress_ongoing) begin
            // Decrement the number of taken slots in the piso with every write to the memory
        if(fv_piso_is_reading) begin //(fv_piso_used_slots_cntr_ff >= fv_output_rate)
                fv_piso_used_slots_cntr = fv_piso_used_slots_cntr - fv_output_rate;
        end
        //end

        if(fv_api_req_tracking_done && po_decompress_done) begin
            fv_api_req_decompression_done = 1'b1;
        end
    end

    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_decompress_ongoing_ff            <= '0;
            fv_api_mem_rd_req_addr_ff           <= '0;
            fv_api_rd_req_cntr_ff               <= '0;
            fv_piso_used_slots_cntr_ff          <= '0;
            fv_req_hold_ff                      <= '0;
            fv_api_req_decompression_done_ff    <= '0;
            fv_api_req_tracking_done_ff         <= '0;
            fv_api_req_tracking_started_ff      <= '0;
        end else begin
            fv_decompress_ongoing_ff            <= fv_decompress_ongoing;
            fv_api_mem_rd_req_addr_ff           <= fv_api_mem_rd_req_addr;
            fv_api_rd_req_cntr_ff               <= fv_api_rd_req_cntr;
            fv_piso_used_slots_cntr_ff          <= fv_piso_used_slots_cntr;
            fv_req_hold_ff                      <= fv_req_hold;
            fv_api_req_decompression_done_ff    <= fv_api_req_decompression_done;
            fv_api_req_tracking_done_ff         <= fv_api_req_tracking_done;
            fv_api_req_tracking_started_ff      <= fv_api_req_tracking_started;
        end
    end

    //////////////////////////////////////////////
    // Scoreboard to check the requests going to
    // the api memory upon enabling decompression
    //////////////////////

    logic fv_decompress_api_mem_req_sb_push;
    assign fv_decompress_api_mem_req_sb_push = fv_api_mem_rd_req_valid;

    logic fv_decompress_api_mem_req_sb_pop;
    assign fv_decompress_api_mem_req_sb_pop = po_api_rd_en && fv_api_req_tracking_started && !fv_api_req_decompression_done_ff;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_api_mem_req_sb_data_in;
    assign fv_decompress_api_mem_req_sb_data_in = fv_api_mem_rd_req_addr;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_api_mem_req_sb_data_out;
    assign fv_decompress_api_mem_req_sb_data_out = po_api_rd_addr;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_api_mem_req_sb_expected_data;


    lubis_scoreboard
    #(
        .DATA_WIDTH             (ABR_MEM_ADDR_WIDTH                         ),
        .DEPTH                  (2                                          )  //1
    ) fv_decompress_api_mem_req_sb (
        .clk                    (pi_clk                                     ),
        .rst                    (!pi_reset_n || pi_zeroize                  ),
        .soft_rst               (1'b0                                       ),
        .push                   (fv_decompress_api_mem_req_sb_push          ),
        .pop                    (fv_decompress_api_mem_req_sb_pop           ),
        .full                   (1'b0                                       ),
        .empty                  (1'b0                                       ),
        .data_in                (fv_decompress_api_mem_req_sb_data_in       ),
        .data_out               (fv_decompress_api_mem_req_sb_data_out      ),
        .expected_data          (fv_decompress_api_mem_req_sb_expected_data ),
        .incr_val               (1'h1                                       ),
        .sampled_in             (                                           ),
        .sampled_in_reg         (                                           ),
        .sampled_out            (                                           ),
        .sampled_out_reg        (                                           ),
        .chosen_symbolic_data   (fv_decompress_api_mem_req_sb_expected_data ),
        .tracking_counter_out   (                                           )
    );

    // Safety property to check that there is a pop for every push for better performance than the liveness
    // This property checks that for every push to the api memory, there is a corresponding pop within 16 cycles
    //16 cycle due to Rtl has already fiexed latency of 16 cycles for the memory read request to be processed and the data to be returned
    assert_decompress_api_mem_req_sb_for_every_push_there_is_pop: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_decompress_api_mem_req_sb_push
                                                                         |->
        ##[0:1] fv_decompress_api_mem_req_sb_pop  //##1
    );

    ////////////////////////////////////////////
    // Scoreboard to check the requests going to
    // the memory upon decompression
    //////////////////////

    logic fv_api_mem_resp_received;

    logic fv_api_mem_req;
    assign fv_api_mem_req = po_api_rd_en;


    // Stores the data to be decompressed
    logic [FV_PISO_BUFFER_W-1:0] fv_api_mem_rd_data;
    logic [FV_PISO_BUFFER_W-1:0] fv_api_mem_rd_data_ff;

    // Incoming data as 64 bits instead of 2 x 32
    logic [2*ABR_REG_WIDTH-1:0] fv_api_rd_data_flat; //DATA_WIDTH

    logic [COEFF_PER_CLK-1:0][ABR_MEM_DATA_WIDTH-1:0] fv_decompressed_data;

    // The rate at which we write to the memory.
    // 48 -> decompress_12
    // 44 -> decompress_11
    // 20 -> decompress_20
    // 4  -> decmompress_1
    logic [6:0] fv_mem_output_rate;

    // Stores the address to the request to the memory where the decompressed data should be stored
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_w_addr;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_w_addr_ff;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_w_addr_expected;

    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_decompressions_cntr;
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_decompressions_cntr_ff;

    logic fv_tracking_started;
    logic fv_tracking_started_ff;

    logic fv_tracking_done;
    logic fv_tracking_done_ff;

    logic fv_decompression_tracking_done;
    logic fv_decompression_tracking_done_ff;

    // Capture the poly num at the start of compression
    logic [2:0] fv_poly_num;
    logic [2:0] fv_poly_num_ff;

    logic fv_decompressed_data_push;

    logic [$clog2(FV_PISO_BUFFER_W+1)-1:0] fv_num_valid;
    logic [$clog2(FV_PISO_BUFFER_W+1)-1:0] fv_num_valid_ff;

    logic fv_num_valid_enough;

    logic fv_piso_full;
    // A flag that is set if the fv piso is full and we need to wait for it to have enough space
    logic fv_buffered_message;
    logic fv_buffered_message_ff;

    // Set to true once the decompression is done then reset, used for safety
    logic fv_decompression_done;

    // Flagging that tracking is ongoing
    logic fv_tracking_active;
    logic fv_piso_hold;

    always_comb begin
        fv_decompressed_data            = '0;
        fv_decompressed_data_push       = '0;
        fv_mem_output_rate              = '0;
        fv_num_valid_enough             = '0;
        fv_api_rd_data_flat             = '0;
        fv_piso_full                    = '0;
        fv_decompression_done           = '0;
        fv_tracking_active              = '0;
        fv_buffered_message             = fv_buffered_message_ff;
        fv_decompressions_cntr          = fv_decompressions_cntr_ff;
        fv_poly_num                     = fv_poly_num_ff;
        fv_api_mem_rd_data              = fv_api_mem_rd_data_ff;
        fv_tracking_started             = fv_tracking_started_ff;
        fv_tracking_done                = fv_tracking_done_ff;
        fv_mem_w_addr                   = fv_mem_w_addr_ff;
        fv_num_valid                    = fv_num_valid_ff;
        fv_decompression_tracking_done  = fv_decompression_tracking_done_ff;

        unique case (pi_mode)
            DECOMPRESS1: begin
                fv_mem_output_rate =  (1*MLKEM_N)/64;
            end
            DECOMPRESS5: begin
                fv_mem_output_rate = (5*MLKEM_N)/64;
            end
            DECOMPRESS11: begin
                fv_mem_output_rate = (11*MLKEM_N)/64;
            end
            DECOMPRESS12: begin
                fv_mem_output_rate = (12*MLKEM_N)/64;
            end
            default: begin
                // Do nothing
            end
        endcase
        //read pointer is greater than or equal to the output rate, then we are reading from the piso
        fv_piso_hold = (fv_num_valid_ff >= fv_output_rate);
        // If the piso is full, then we should not read from the api memory and we should wait for the piso to have enough space
        fv_piso_full = fv_piso_hold ? (fv_num_valid > (FV_PISO_BUFFER_W - 'd64 + fv_output_rate)) : ((FV_PISO_BUFFER_W - fv_num_valid) < 'd64);

        // If compression is enabled and arbitration window is high, then the current compression
        // should be tracked
        if(pi_decompress_enable && fv_arbit_window && !fv_tracking_started && !fv_decompression_tracking_done) begin
            fv_tracking_started         = 1'b1;
            fv_poly_num                 = pi_num_poly;
            fv_mem_w_addr               = pi_dest_base_addr;
            fv_decompressions_cntr      = '0;
            fv_api_mem_rd_data          = '0;
        end

        if(fv_tracking_started && !fv_decompression_tracking_done) begin
            if((fv_decompressions_cntr == (fv_poly_num * fv_mem_output_rate)) && (fv_num_valid == '0)) begin
                fv_mem_w_addr                   = '0;
                fv_decompressions_cntr          = '0;
                fv_decompression_tracking_done  = 1'b1;
                fv_api_mem_rd_data              = '0;
                fv_decompression_done           = 1'b1; // Set to true for one cycle only then released
            end
            //api_rd_data_valid is high and fv_buffered_message is low and fv_piso_full is low, then we are receiving data from the api memory and we should increment the number of taken slots in the piso
            if((pi_api_rd_data_valid  || fv_buffered_message) && !fv_piso_full) begin //fv_api_mem_resp_received
                fv_api_rd_data_flat = pi_api_rd_data;
                fv_api_mem_rd_data  = fv_api_mem_rd_data | (fv_api_rd_data_flat << fv_num_valid);
                fv_num_valid        = fv_num_valid + 'd64;
                fv_decompressions_cntr++;
                fv_buffered_message = 1'b0;
            end else if(pi_api_rd_data_valid && fv_piso_full) begin //fv_api_mem_resp_received
                fv_buffered_message = 1'b1;
            end

            // Check if there are enough bits to decompress and send a write request to the memory
            if(pi_mode == 2'b00) begin : delay_match
                // compress_1 mode
                fv_num_valid_enough = (fv_num_valid >= 'd4);
            end else if(pi_mode == 2'b01) begin
                // compress_5 mode
                fv_num_valid_enough = (fv_num_valid >= 'd20);
            end else if(pi_mode == 2'b10) begin
                // compress_11 mode
                fv_num_valid_enough = (fv_num_valid >= 'd44);
            end else begin
                // pi_mode == 2'b11
                // decompress_12 mode
                fv_num_valid_enough = (fv_num_valid >= 'd48);
            end


            if(fv_num_valid_enough) begin
                for(int i = 0; i < COEFF_PER_CLK; i++) begin
                    if(pi_mode == 2'b00) begin
                        // compress_1 mode
                        fv_decompressed_data[i] = {12'h0, MLKEM_Q_WIDTH'(((MLKEM_Q * fv_api_mem_rd_data[1-1:0]) + 2**(1 - 1)) >> 1)};
                        fv_api_mem_rd_data      = fv_api_mem_rd_data >> 'd1;
                        fv_num_valid            = fv_num_valid - 'd1; // 1 bit processed
                    end else if(pi_mode == 2'b01) begin
                        // compress_5 mode
                        fv_decompressed_data[i] = {12'h0,MLKEM_Q_WIDTH'(((MLKEM_Q * fv_api_mem_rd_data[5-1:0]) + 2**(5 - 1)) >> 5)};
                        fv_api_mem_rd_data      = fv_api_mem_rd_data >> 'd5;
                        fv_num_valid            = fv_num_valid - 'd5; // 5 bits processed
                    end else if(pi_mode == 2'b10) begin
                        // compress_11 mode
                        fv_decompressed_data[i] = {12'h0,MLKEM_Q_WIDTH'(((MLKEM_Q * fv_api_mem_rd_data[11-1:0]) + 2**(11 - 1)) >> 11)};
                        fv_api_mem_rd_data      = fv_api_mem_rd_data >> 'd11;
                        fv_num_valid            = fv_num_valid - 'd11; // 11 bits processed
                    end else begin
                        // pi_mode == 2'b11
                        // decompress_12 mode
                        fv_decompressed_data[i] = {12'h0,fv_api_mem_rd_data[12-1:0] < MLKEM_Q ? fv_api_mem_rd_data[12-1:0] : '0};
                        fv_api_mem_rd_data      = fv_api_mem_rd_data >> 'd12;
                        fv_num_valid            = fv_num_valid - 'd12; // 12 bits processed
                    end
                end
                fv_decompressed_data_push   = 1'b1;
                fv_mem_w_addr               = fv_mem_w_addr + 1'd1;
            end
            fv_tracking_active = 1'b1;
        end else begin
            fv_tracking_active = 1'b0;
        end

        if(fv_decompression_tracking_done && po_decompress_done) begin
            fv_tracking_done = 1'b1;
        end
    end

    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_api_mem_resp_received            <= '0;
            fv_mem_w_addr_ff                    <= '0;
            fv_decompressions_cntr_ff           <= '0;
            fv_tracking_started_ff              <= '0;
            fv_tracking_done_ff                 <= '0;
            fv_poly_num_ff                      <= '0;
            fv_api_mem_rd_data_ff               <= '0;
            fv_num_valid_ff                     <= '0;
            fv_decompression_tracking_done_ff   <= '0;
            fv_buffered_message_ff              <= '0;
        end else begin
            // Memory latency is 1
            fv_api_mem_resp_received            <= fv_api_mem_req;
            fv_mem_w_addr_ff                    <= fv_mem_w_addr;
            fv_decompressions_cntr_ff           <= fv_decompressions_cntr;
            fv_tracking_started_ff              <= fv_tracking_started;
            fv_tracking_done_ff                 <= fv_tracking_done;
            fv_poly_num_ff                      <= fv_poly_num;
            fv_api_mem_rd_data_ff               <= fv_api_mem_rd_data;
            fv_num_valid_ff                     <= fv_num_valid;
            fv_decompression_tracking_done_ff   <= fv_decompression_tracking_done;
            fv_buffered_message_ff              <= fv_buffered_message;
        end
    end

    logic [ABR_MEM_DATA_WIDTH-1:0] fv_splite_share0;
    logic [ABR_MEM_DATA_WIDTH-1:0] fv_splite_share1;
    logic [COEFF_PER_CLK-1:0] [MLDSA_Q_WIDTH-1:0] fv_data_coeff;
    logic [COEFF_PER_CLK-1:0] [MLDSA_Q_WIDTH-1:0] fv_data_coeff_d1;
    logic [COEFF_PER_CLK-1:0] [MLDSA_Q_WIDTH-1:0] fv_rand_coeff;
    logic [COEFF_PER_CLK-1:0] [MLDSA_Q_WIDTH-1:0] fv_rand_raw;
    logic [COEFF_PER_CLK-1:0] [MLDSA_Q_WIDTH-1:0] fv_rand;
    logic [COEFF_PER_CLK-1:0][MLDSA_Q_WIDTH-1:0] fv_share1_coeff;
    //********************************** splitter logic **********************************
    generate
    for (genvar i = 0; i < COEFF_PER_CLK; i++) begin : gen_fv_splitter
        assign fv_data_coeff[i] = fv_decompressed_data[i][MLDSA_Q_WIDTH-1:0];
        assign fv_rand_coeff[i] = pi_rand_i[i*REG_SIZE +: MLDSA_Q_WIDTH];

        //rand_i less then q = 3329
        assign fv_rand_raw[i] = {{(MLDSA_Q_WIDTH-MLKEM_REG_SIZE){1'b0}}, fv_rand_coeff[i][MLKEM_REG_SIZE-1:0]};

        // it should in the range of [0, q-1], so if it is greater than or equal to q, we subtract q from it
        assign fv_rand[i] = (fv_rand_raw[i] >= MLKEM_Q) ? (fv_rand_raw[i] - MLKEM_Q) : fv_rand_raw[i];


        always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_data_coeff_d1[i] <= '0;
        end else begin
            fv_data_coeff_d1[i] <= fv_data_coeff[i];
        end
    end

        // share1 = (data - rand_reduced) mod q, computed via conditional add-back
        // instead of the `%` operator: fv_data_coeff/fv_rand are unsigned MLDSA_Q_WIDTH-bit
        // vectors, so a plain `fv_data_coeff[i] - fv_rand[i]` underflows/wraps to a huge
        // value whenever data < rand, and `% MLKEM_Q` on that wrapped value does NOT equal
        // (data - rand) mod q. The conditional form is the width-safe equivalent.
        assign fv_share1_coeff[i] = (fv_data_coeff_d1[i] >= fv_rand[i]) ?
                                        (fv_data_coeff_d1[i] - fv_rand[i]) :
                                        (fv_data_coeff_d1[i] + MLKEM_Q - fv_rand[i]);

        // Pack back into the flat word.
        assign fv_splite_share0[i*REG_SIZE +: REG_SIZE] = {1'b0, fv_rand[i]};
        assign fv_splite_share1[i*REG_SIZE +: REG_SIZE] = {1'b0, fv_share1_coeff[i]};
    end
    endgenerate

    always_comb begin
        if(!pi_split_en_i) begin
            fv_mem_wr_data[0] = fv_data_coeff;
        end else begin
            fv_mem_wr_data[0] = fv_splite_share0;
        end
    end
    generate if (ABR_NUM_NTT > 1) begin : gen_fv_mem_wr_data_share1
        always_comb begin
            fv_mem_wr_data[1] = pi_split_en_i ? fv_splite_share1 : fv_data_coeff;
        end
    end endgenerate
    //********************************** splitter logic end **********************************
    logic fv_push_d1;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
           fv_push_d1 <= '0;
        end else begin
            fv_push_d1 <= fv_decompressed_data_push;
        end
    end

    logic fv_decompress_mem_write_req_sb_push;
    assign fv_decompress_mem_write_req_sb_push =  fv_decompressed_data_push;
    //logic [COEFF_PER_CLK*MLDSA_Q_WIDTH+ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_mem_write_req_sb_data_in;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_mem_write_req_sb_data_in;
    assign fv_decompress_mem_write_req_sb_data_in = fv_mem_w_addr_ff;

    // Pop the scoreboard for every write to the memory
    logic fv_decompress_mem_write_req_sb_pop;
    assign fv_decompress_mem_write_req_sb_pop = (po_mem_wr_req.rd_wr_en == RW_WRITE) && fv_tracking_started && !fv_tracking_done_ff;

    //logic [COEFF_PER_CLK*MLDSA_Q_WIDTH+ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_mem_write_req_sb_data_out;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_mem_write_req_sb_data_out;
    assign fv_decompress_mem_write_req_sb_data_out = po_mem_wr_req.addr;//{po_mem_wr_req.addr, po_mem_wr_data};

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_decompress_mem_write_req_sb_expected_data;

    logic [2:0]  fv_decompress_mem_write_req_sb_tracking_cntr;

    lubis_scoreboard
    #(
        //.DATA_WIDTH             (COEFF_PER_CLK*MLDSA_Q_WIDTH+ABR_MEM_ADDR_WIDTH ),
        .DATA_WIDTH             (14),
        .DEPTH                  (4                                              )
    ) fv_decompress_mem_write_req_sb (
        .clk                    (pi_clk                                         ),
        .rst                    (!pi_reset_n || pi_zeroize                      ),
        .soft_rst               (1'b0                                           ),
        .push                   (fv_decompress_mem_write_req_sb_push            ),
        .pop                    (fv_decompress_mem_write_req_sb_pop             ),
        .full                   (1'b0                                           ),
        .empty                  (1'b0                                           ),
        .data_in                (fv_decompress_mem_write_req_sb_data_in         ),
        .data_out               (fv_decompress_mem_write_req_sb_data_out        ),
        .expected_data          (fv_decompress_mem_write_req_sb_expected_data   ),
        .incr_val               (1'h1                                           ),
        .sampled_in             (                                               ),
        .sampled_in_reg         (                                               ),
        .sampled_out            (                                               ),
        .sampled_out_reg        (                                               ),
        .chosen_symbolic_data   (fv_decompress_mem_write_req_sb_expected_data   ),
        .tracking_counter_out   ( fv_decompress_mem_write_req_sb_tracking_cntr )
    );

    logic fv_decompress_mem_write_req_sb_push_mem;
    assign fv_decompress_mem_write_req_sb_push_mem =  pi_split_en_i ? fv_push_d1 : fv_decompressed_data_push;

    logic [191:0] fv_decompress_mem_write_req_sb_data_in_mem_data;
    assign fv_decompress_mem_write_req_sb_data_in_mem_data = fv_mem_wr_data;

    logic [191:0] fv_decompress_mem_write_req_sb_data_out_mem_data;
    assign fv_decompress_mem_write_req_sb_data_out_mem_data =  po_mem_wr_data;

    logic [191:0] fv_decompress_mem_write_req_sb_expected_data_mem_data;
    logic [2:0]  fv_decompress_mem_write_req_sb_tracking_cntr_mem_data;

    lubis_scoreboard
    #(
        //.DATA_WIDTH             (COEFF_PER_CLK*MLDSA_Q_WIDTH+ABR_MEM_ADDR_WIDTH ),
        .DATA_WIDTH             (192),
        .DEPTH                  (4                                              )
    ) fv_decompress_mem_write_req_sb_mem (
        .clk                    (pi_clk                                         ),
        .rst                    (!pi_reset_n || pi_zeroize                      ),
        .soft_rst               (1'b0                                           ),
        .push                   (fv_decompress_mem_write_req_sb_push_mem        ),
        .pop                    (fv_decompress_mem_write_req_sb_pop             ),
        .full                   (1'b0                                           ),
        .empty                  (1'b0                                           ),
        .data_in                (fv_decompress_mem_write_req_sb_data_in_mem_data),
        .data_out               (fv_decompress_mem_write_req_sb_data_out_mem_data),
        .expected_data          (fv_decompress_mem_write_req_sb_expected_data_mem_data),
        .incr_val               (1'h1                                           ),
        .sampled_in             (                                               ),
        .sampled_in_reg         (                                               ),
        .sampled_out            (                                               ),
        .sampled_out_reg        (                                               ),
        .chosen_symbolic_data   (fv_decompress_mem_write_req_sb_expected_data_mem_data),
        .tracking_counter_out   ( fv_decompress_mem_write_req_sb_tracking_cntr_mem_data)
    );



    // Safety property to check that there is a pop for every push for better performance than the liveness
    // This is done using the tracking counter of the scoreboard, such that if the decompression is done, then the
    // tracking counter must be zero, which meeans all pops already took place
    assert_decompress_mem_write_req_sb_for_every_push_there_is_pop: assert property(disable iff(!pi_reset_n || pi_zeroize)
        po_decompress_done
                                                                           |->
        fv_decompress_mem_write_req_sb_tracking_cntr == 0
    );

    assert_decompress_mem_write_req_sb_for_every_push_there_is_pop_mem: assert property(disable iff(!pi_reset_n || pi_zeroize)
        po_decompress_done
                                                                               |->
        fv_decompress_mem_write_req_sb_tracking_cntr_mem_data == 0
    );

    // Safety properties to check that for every decompress_enable, there is a done

    // If the tracking counter of the decompression scoreboard is zero, and formal tracking is done
    // then decompression_done should be raised, this can happen one cycle, or two cycle later depending on the mode
    assert_decompress_done_high_safety: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_decompression_done
                                               |->
        ##[1:4] po_decompress_done
    );

    assert_decompress_done_low_safety: assert property(disable iff(!pi_reset_n || pi_zeroize)
        !fv_decompression_done &&
        fv_tracking_active
                                              |->
        !po_decompress_done
    );

    // For every decompression_enable, the formal decompression done is raised
    assert_forward_progress_formal_signal: assert property(disable iff(!pi_reset_n || pi_zeroize)
        pi_decompress_enable &&
        fv_tracking_active
                                                  |->
        s_eventually(fv_decompression_done)
    );

    // For every decompression_enable,  decompress_done is raised
    assert_forward_progress_design_signal: assert property(disable iff(!pi_reset_n || pi_zeroize)
        pi_decompress_enable &&
        fv_tracking_active
                                                  |->
        s_eventually(po_decompress_done)
    );

    logic fv_decompression_active;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_decompression_active <= 1'b0;
        end else begin
            if(pi_decompress_enable) begin
                fv_decompression_active <= 1'b1;
            end else if(po_decompress_done) begin
                fv_decompression_active <= 1'b0;
            end
        end
    end

    // If there is no active decompression, the design should not send out anything
    assert_no_activities: assert property(disable iff(!pi_reset_n || pi_zeroize)
        !fv_decompression_active
                                 |->
        (po_mem_wr_req.rd_wr_en == RW_IDLE) &&
        !po_api_rd_en &&
        !po_decompress_done
    );
    // Cover to detect the bound of two decompressions
    cover_two_decompressions_done: cover property(disable iff(!pi_reset_n || pi_zeroize)
        po_decompress_done [->2]
    );

    cover_two_decompressions_done_00: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_decompress_done && pi_mode == 2'b00) [->2]
    );

    cover_two_decompressions_done_01: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_decompress_done && pi_mode == 2'b01) [->2]
    );

    cover_two_decompressions_done_10: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_decompress_done && pi_mode == 2'b10) [->2]
    );

    cover_two_decompressions_done_11: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_decompress_done && pi_mode == 2'b11) [->2]
    );

    // Covers to detect the bound of the second decompression starting
    cover_second_decompression_start_00: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_decompress_enable && pi_mode == 2'b00) [->2]
    );

    cover_second_decompression_start_01: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_decompress_enable && pi_mode == 2'b01) [->2]
    );

    cover_second_decompression_start_10: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_decompress_enable && pi_mode == 2'b10) [->2]
    );

    cover_second_decompression_start_11: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_decompress_enable && pi_mode == 2'b11) [->2]
    );


endmodule


bind decompress_top fv_decompress_top #(
    //#$bind
    .ABR_NUM_NTT(ABR_NUM_NTT)
    //$#//
) fv_decompress_top_i (
    .pi_clk              (clk),
    .pi_reset_n          (reset_n),
    .pi_zeroize          (zeroize),
    .pi_decompress_enable(decompress_enable),
    .pi_mode             (mode),
    .pi_num_poly         (num_poly),
    .pi_src_base_addr    (src_base_addr),
    .pi_dest_base_addr   (dest_base_addr),
    .pi_split_en_i       (split_en_i),    // NEW
    .pi_rand_i           (rand_i),         // NEW
    .po_mem_wr_req       (mem_wr_req),
    .po_mem_wr_data      (mem_wr_data),    // type now matches
    .po_api_rd_en        (api_rd_en),
    .po_api_rd_addr      (api_rd_addr),
    .pi_api_rd_data      (api_rd_data),
    .pi_api_rd_data_valid (api_rd_data_valid), // NEW
    .po_decompress_done  (decompress_done)
);

