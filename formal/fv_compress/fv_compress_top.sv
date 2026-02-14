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


module fv_compress_top
    import abr_params_pkg::*;
    import compress_defines_pkg::*;
#(
    //#$localparams
    localparam COMP_DATA_W = 12
    //$#//
) (
    //#$ports
    input                                   pi_clk,
    input                                   pi_reset_n,
    input                                   pi_zeroize,
    input                                   pi_compress_enable,
    input compress_mode_t                   pi_mode,
    input logic                             pi_compare_mode,
    input [2:0]                             pi_num_poly,
    input [ABR_MEM_ADDR_WIDTH-1:0]          pi_src_base_addr,
    input [ABR_MEM_ADDR_WIDTH-1:0]          pi_dest_base_addr,
    input mem_if_t                          po_mem_rd_req,
    input [COEFF_PER_CLK-1:0][REG_SIZE-1:0] pi_mem_rd_data,
    input logic [1:0]                       po_api_rw_en,
    input logic [ABR_MEM_ADDR_WIDTH-1:0]    po_api_rw_addr,
    input logic [DATA_WIDTH-1:0]            po_api_wr_data,
    input logic [DATA_WIDTH-1:0]            pi_api_rd_data,
    input logic                             po_compare_failed,
    input logic                             po_compress_done
    //$#//
);

    default clocking default_clk @(posedge pi_clk); endclocking

    // The number of 4-bit packets sent to the api memory
    localparam FV_NUM_PKTS_TO_MEM = 8;
    localparam FV_MIN_BUF_SPACE = 12;
    localparam FV_TOTAL_BUF_SLOTS = 20;
    
    //#$instances
    fv_compress_constraints #(
    ) fv_compress_constraints_i (.*);
    
    fv_compress_scenarios #(
    ) fv_compress_scenarios_i (.*);
    
    //$#//
    
    // Free variable to select a single compression to check, there is no need to check every single compression
    logic fv_arbit_window;

    logic fv_req_hold;
    logic fv_req_hold_ff;

    logic [5-1:0] fv_buffer_slots_cntr;
    logic [5-1:0] fv_buffer_slots_cntr_ff;

    // Once compress enable is high, it means that compression started and we should see requests to the memory starting at base address
    logic fv_compress_ongoing;
    logic fv_compress_ongoing_ff;

    logic fv_mem_rd_req_valid;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_rd_req_addr;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_rd_req_addr_ff;

    // Every polynomial can cause up to 64 requests, and we can receive up to 8 polynomials in every compression request
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_mem_rd_req_cntr;
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_mem_rd_req_cntr_ff;

    logic fv_mem_req_tracking_started;
    logic fv_mem_req_tracking_started_ff;
    
    logic fv_mem_req_tracking_done;
    logic fv_mem_req_tracking_done_ff;

    logic fv_mem_req_compression_done;
    logic fv_mem_req_compression_done_ff;

    always_comb begin
        fv_compress_ongoing         = fv_compress_ongoing_ff;
        fv_mem_rd_req_addr          = fv_mem_rd_req_addr_ff;
        fv_mem_rd_req_cntr          = fv_mem_rd_req_cntr_ff;
        fv_buffer_slots_cntr        = fv_buffer_slots_cntr_ff;
        fv_req_hold                 = fv_req_hold_ff;
        fv_mem_req_tracking_started = fv_mem_req_tracking_started_ff;
        fv_mem_req_tracking_done    = fv_mem_req_tracking_done_ff;
        fv_mem_req_compression_done = fv_mem_req_compression_done_ff;
        fv_mem_rd_req_valid         = '0;

        // Check if there is space in the buffer based on the mode
        if((fv_mem_rd_req_cntr != (pi_num_poly * 64))) begin
            // In case of performance enhancement done on allowing the buffer to take in 11 4-bits message in
            // case there is only space for 11 instead of 12, the commented part should be activated and the
            // fv_req_hold = ((20 - fv_buffer_slots_cntr) < 12); should be removed
            // If not all polynomials are compressed yet, check if a hold is required
            // unique case (pi_mode)
            //     compress1: begin
            //         fv_req_hold = ((20 - fv_buffer_slots_cntr) < 1);
            //     end
            //     compress5: begin
            //         fv_req_hold = ((20 - fv_buffer_slots_cntr) < 5);
            //     end
            //     compress11: begin
            //         fv_req_hold = ((20 - fv_buffer_slots_cntr) < 11);
            //     end
            //     compress12: begin
            //         fv_req_hold = ((20 - fv_buffer_slots_cntr) < 12);
            //     end
            //     default: begin
            //         // Do nothing
            //     end
            // endcase
            fv_req_hold = ((FV_TOTAL_BUF_SLOTS - fv_buffer_slots_cntr) < FV_MIN_BUF_SPACE);
        end else begin
            fv_req_hold = 1'b0;
        end
        
        // Increment the number of taken slots every cycle during compression based on the compression type
        if(fv_compress_ongoing && !fv_req_hold) begin
            unique case (pi_mode)
                compress1: begin
                    fv_buffer_slots_cntr = fv_buffer_slots_cntr + 1'd1;
                end
                compress5: begin
                    fv_buffer_slots_cntr = fv_buffer_slots_cntr + 3'd5;
                end
                compress11: begin
                    fv_buffer_slots_cntr = fv_buffer_slots_cntr + 4'd11;
                end
                compress12: begin
                    fv_buffer_slots_cntr = fv_buffer_slots_cntr + 4'd12;
                end
                default: begin
                    // Do nothing
                end
            endcase
        end

        if(fv_compress_ongoing && (fv_mem_rd_req_cntr == (pi_num_poly * 64)) && !fv_req_hold && !fv_req_hold_ff) begin
            // The sent polynomials reached the limit
            fv_compress_ongoing = '0;
            fv_mem_rd_req_addr = '0;
            fv_mem_rd_req_cntr = '0;
            fv_buffer_slots_cntr = '0;
            fv_mem_req_tracking_done = 1'b1;
        end

        if(fv_compress_ongoing) begin
            // send requests to the memory
            fv_mem_rd_req_valid = 1'b1;
            if(!fv_req_hold_ff) begin
                fv_mem_rd_req_addr++;
                fv_mem_rd_req_cntr++;
            end
        end

        if(pi_compress_enable && fv_arbit_window && !fv_mem_req_tracking_started) begin
            // Compression started
            fv_compress_ongoing = 1'b1;
            // Tracked compression started
            fv_mem_req_tracking_started = 1'b1;
            // Send the first request
            fv_mem_rd_req_valid = 1'b1;
            fv_mem_rd_req_addr = pi_src_base_addr;
            fv_mem_rd_req_cntr++;
        end

        if(fv_compress_ongoing) begin
            // Decrement the number of taken slots in the buffer with every write to the api memory
            if(fv_buffer_slots_cntr >= FV_NUM_PKTS_TO_MEM) begin
                fv_buffer_slots_cntr = fv_buffer_slots_cntr - FV_NUM_PKTS_TO_MEM;
            end
        end

        if(fv_mem_req_tracking_done && po_compress_done) begin
            fv_mem_req_compression_done = 1'b1;
        end
    end

    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_compress_ongoing_ff          <= '0;
            fv_mem_rd_req_addr_ff           <= '0;
            fv_mem_rd_req_cntr_ff           <= '0;
            fv_buffer_slots_cntr_ff         <= '0;
            fv_req_hold_ff                  <= '0;
            fv_mem_req_tracking_started_ff  <= '0;
            fv_mem_req_tracking_done_ff     <= '0;
            fv_mem_req_compression_done_ff  <= '0;
        end else begin
            fv_compress_ongoing_ff          <= fv_compress_ongoing;
            fv_mem_rd_req_addr_ff           <= fv_mem_rd_req_addr;
            fv_mem_rd_req_cntr_ff           <= fv_mem_rd_req_cntr;
            fv_buffer_slots_cntr_ff         <= fv_buffer_slots_cntr;
            fv_req_hold_ff                  <= fv_req_hold;
            fv_mem_req_tracking_started_ff  <= fv_mem_req_tracking_started;
            fv_mem_req_tracking_done_ff     <= fv_mem_req_tracking_done;
            fv_mem_req_compression_done_ff  <= fv_mem_req_compression_done;
        end
    end

    ////////////////////////////////////////////
    // Scoreboard to check the requests going to
    // the memory upon enabling compression
    //////////////////////

    logic fv_compress_mem_req_sb_push;
    assign fv_compress_mem_req_sb_push = fv_mem_rd_req_valid;

    // Pop the scoreboard as long as the fv compression is ongoing, no more popping if fv_compress_ongoing is low, because these writes belong to an untracked compression
    // fv_compress_ongoing_ff is high for one cycle after the last push, which is enough to pop the scoreboard one last time
    logic fv_compress_mem_req_sb_pop;
    assign fv_compress_mem_req_sb_pop = (po_mem_rd_req.rd_wr_en == RW_READ) && fv_mem_req_tracking_started && !fv_mem_req_compression_done_ff;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_mem_req_sb_data_in;
    assign fv_compress_mem_req_sb_data_in = fv_mem_rd_req_addr;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_mem_req_sb_data_out;
    assign fv_compress_mem_req_sb_data_out = po_mem_rd_req.addr;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_mem_req_sb_expected_data;

    lubis_scoreboard
    #( 	
        .DATA_WIDTH             (ABR_MEM_ADDR_WIDTH                     ),
    	.DEPTH                  (1                                      )
    ) fv_compress_mem_req_sb (
        .clk                    (pi_clk                                 ),
    	.rst                    (!pi_reset_n || pi_zeroize              ),
        .soft_rst               (1'b0                                   ),
        .push                   (fv_compress_mem_req_sb_push            ),
    	.pop                    (fv_compress_mem_req_sb_pop             ),
    	.full                   (1'b0                                   ),
    	.empty                  (1'b0                                   ),
    	.data_in                (fv_compress_mem_req_sb_data_in         ),
        .data_out               (fv_compress_mem_req_sb_data_out        ),
        .expected_data          (fv_compress_mem_req_sb_expected_data   ),
        .incr_val               (1'h1                                   ),
        .sampled_in             (                                       ),
        .sampled_in_reg         (                                       ),
        .sampled_out            (                                       ),
        .sampled_out_reg        (                                       ),
        .chosen_symbolic_data   (fv_compress_mem_req_sb_expected_data   ),
        .tracking_counter_out   (                                       )        
    );

    // Safety property to check that there is a pop for every push for better performance than the liveness
    assert_compress_mem_req_sb_for_every_push_there_is_pop: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_compress_mem_req_sb_push
    |->
        ##1 fv_compress_mem_req_sb_pop
    );

    ////////////////////////////////////////////
    // Scoreboard to check the requests going to
    // the api memory upon after compression
    //////////////////////
    
    // Compression logic

    logic fv_mem_resp_received;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_mem_req_addr;

    logic fv_mem_req;
    assign fv_mem_req = (po_mem_rd_req.rd_wr_en == RW_READ);

    // Stores the data to be compressed without padding
    logic [MLKEM_Q_WIDTH-1:0] fv_mem_rd_data;
    logic [MLKEM_Q_WIDTH-1:0] fv_mem_rd_data_compressed;

    logic [95:0] fv_compressed_data_flat;
    logic [95:0] fv_compressed_data_flat_ff;

    // Has the number of valid bits after compression of each coefficient
    logic [6:0] fv_num_valid;
    logic [6:0] fv_num_valid_ff;

    // Stores the 32-bit compressed data and controls when to push to the scoreboard
    logic fv_compressed_word_push;
    logic [DATA_WIDTH-1:0] fv_compressed_word;

    // Stores the address to the request to the api memory where the compressed data should be stored
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_api_rw_addr;
    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_api_rw_addr_ff;

    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_compressions_cntr;
    logic [$clog2((MLKEM_N/4)*8+1)-1:0] fv_compressions_cntr_ff;

    logic fv_tracking_started;
    logic fv_tracking_started_ff;

    logic fv_compression_tracking_done;
    logic fv_compression_tracking_done_ff;

    logic fv_tracking_done;
    logic fv_tracking_done_ff;

    // Capture the poly num at the start of compression
    logic [2:0] fv_poly_num;
    logic [2:0] fv_poly_num_ff;

    // Capture the compare mode flag
    logic fv_compare_mode;
    logic fv_compare_mode_ff;

    // Set to true once the compression is done then reset, used for safety
    logic fv_compression_done;

    // Flagging that tracking is ongoing
    logic fv_tracking_active;

    always_comb begin
        fv_compressed_word_push         = '0;
        fv_compressed_word              = '0;
        fv_mem_rd_data                  = '0;
        fv_mem_rd_data_compressed       = '0;
        fv_compression_done             = '0;
        fv_tracking_active              = '0;
        fv_num_valid                    = fv_num_valid_ff;
        fv_api_rw_addr                  = fv_api_rw_addr_ff;
        fv_compressions_cntr            = fv_compressions_cntr_ff;
        fv_compressed_data_flat         = fv_compressed_data_flat_ff;
        fv_tracking_started             = fv_tracking_started_ff;
        fv_compression_tracking_done    = fv_compression_tracking_done_ff;
        fv_tracking_done                = fv_tracking_done_ff;
        fv_poly_num                     = fv_poly_num_ff;
        fv_compare_mode                 = fv_compare_mode_ff;

        // If compression is enabled and arbitration window is high, then the current compression
        // should be tracked
        if(pi_compress_enable && fv_arbit_window && !fv_tracking_started) begin
            fv_tracking_started     = 1'b1;
            fv_poly_num             = pi_num_poly;
            fv_api_rw_addr          = pi_dest_base_addr;
            fv_compare_mode         = pi_compare_mode;
            fv_compressions_cntr    = '0;
            fv_compressed_data_flat = '0;
            fv_num_valid            = '0;
            fv_compressions_cntr    = '0;
        end

        if(fv_tracking_started && !fv_compression_tracking_done) begin
            if((fv_compressions_cntr == (fv_poly_num * 64)) && fv_num_valid == '0) begin
                fv_compressed_data_flat         = '0;
                fv_api_rw_addr                  = '0;
                fv_num_valid                    = '0;
                fv_compressions_cntr            = '0;
                fv_compression_tracking_done    = 1'b1;
                fv_compression_done             = 1'b1; // Set to true for one cycle only then released
            end

            if(fv_mem_resp_received) begin
                // Detect double requests and discard the first one
                // If the address of the current request is equal to the address of the previous request,
                // then a hold has happened and the current response should be discarded
                if((fv_mem_req_addr != po_mem_rd_req.addr) && fv_mem_req || !fv_mem_req) begin
                    for(int i = 0; i < COEFF_PER_CLK; i++) begin
                        fv_mem_rd_data = pi_mem_rd_data[i][MLKEM_Q_WIDTH-1:0];
                        if(pi_mode == 2'b00) begin
                            // compress_1 mode
                            fv_mem_rd_data_compressed       = ((2*MLKEM_Q_WIDTH)'(fv_mem_rd_data[MLKEM_Q_WIDTH-1:0] << 1'd1) + MLKEM_Q/2'd2) / MLKEM_Q;
                            fv_mem_rd_data_compressed[11:1] = 11'h0;
                            fv_compressed_data_flat         = fv_compressed_data_flat | (fv_mem_rd_data_compressed << fv_num_valid);
                            fv_num_valid                    = fv_num_valid + 1'd1;
                        end else if(pi_mode == 2'b01) begin
                            // compress_5 mode
                            fv_mem_rd_data_compressed       = ((2*MLKEM_Q_WIDTH)'(fv_mem_rd_data[MLKEM_Q_WIDTH-1:0] << 3'd5) + MLKEM_Q/2'd2) / MLKEM_Q;
                            fv_mem_rd_data_compressed[11:5] = 7'h0;
                            fv_compressed_data_flat         = fv_compressed_data_flat | (fv_mem_rd_data_compressed << fv_num_valid);
                            fv_num_valid                    = fv_num_valid + 3'd5;
                        end else if(pi_mode == 2'b10) begin
                            // compress_11 mode
                            fv_mem_rd_data_compressed       = ((2*MLKEM_Q_WIDTH)'(fv_mem_rd_data[MLKEM_Q_WIDTH-1:0] << 4'd11) + MLKEM_Q/2'd2) / MLKEM_Q;
                            fv_mem_rd_data_compressed[11]   = 1'b0;
                            
                            fv_compressed_data_flat         = fv_compressed_data_flat | (fv_mem_rd_data_compressed << fv_num_valid);
                            fv_num_valid                    = fv_num_valid + 4'd11;
                        end else begin
                            // pi_mode == 2'b11
                            // compress_12 mode
                            fv_compressed_data_flat         = fv_compressed_data_flat | (fv_mem_rd_data << fv_num_valid);
                            fv_num_valid                    = fv_num_valid + 4'd12;
                        end
                    end
                    fv_compressions_cntr++;
                end else begin
                    // Response discarded
                end
            end

            if(fv_num_valid >= DATA_WIDTH) begin
                // Enough data for a scoreboard push, which are 32 bits
                fv_compressed_word_push = 1'b1;
                fv_compressed_word      = fv_compressed_data_flat[31:0];
                fv_compressed_data_flat = fv_compressed_data_flat >> DATA_WIDTH;
                fv_api_rw_addr          = fv_api_rw_addr + 1'd1;
                fv_num_valid            = fv_num_valid - DATA_WIDTH;
            end

            fv_tracking_active = 1'b1;
        end else begin
            fv_tracking_active = 1'b0;
        end

        if(fv_compression_tracking_done && po_compress_done) begin
            fv_tracking_done = 1'b1;
        end
    end

    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_mem_resp_received            <= '0;
            fv_mem_req_addr                 <= '0;
            fv_api_rw_addr_ff               <= '0;
            fv_compressed_data_flat_ff      <= '0;
            fv_num_valid_ff                 <= '0;
            fv_compressions_cntr_ff         <= '0;
            fv_tracking_started_ff          <= '0;
            fv_compression_tracking_done_ff <= '0;
            fv_poly_num_ff                  <= '0;
            fv_compare_mode_ff              <= '0;
            fv_tracking_done_ff             <= '0;
        end else begin
            // Memory latency is 1
            fv_mem_resp_received            <= fv_mem_req;
            fv_mem_req_addr                 <= po_mem_rd_req.addr;
            fv_api_rw_addr_ff               <= fv_api_rw_addr;
            fv_compressed_data_flat_ff      <= fv_compressed_data_flat;
            fv_num_valid_ff                 <= fv_num_valid;
            fv_compressions_cntr_ff         <= fv_compressions_cntr;
            fv_tracking_started_ff          <= fv_tracking_started;
            fv_compression_tracking_done_ff <= fv_compression_tracking_done;
            fv_poly_num_ff                  <= fv_poly_num;
            fv_compare_mode_ff              <= fv_compare_mode;
            fv_tracking_done_ff             <= fv_tracking_done;
        end
    end

    logic fv_compress_api_mem_write_req_sb_push;
    assign fv_compress_api_mem_write_req_sb_push = fv_compressed_word_push && !fv_compare_mode;

    logic [ABR_MEM_ADDR_WIDTH+DATA_WIDTH-1:0] fv_compress_api_mem_write_req_sb_data_in;
    assign fv_compress_api_mem_write_req_sb_data_in = {fv_api_rw_addr_ff, fv_compressed_word};

    // Pop the scoreboard for every write to the api memory that is not part of the compare mode
    logic fv_compress_api_mem_write_req_sb_pop;
    assign fv_compress_api_mem_write_req_sb_pop = (po_api_rw_en == 2'b01) && fv_tracking_started && !fv_tracking_done_ff;

    logic [ABR_MEM_ADDR_WIDTH+DATA_WIDTH-1:0] fv_compress_api_mem_write_req_sb_data_out;
    assign fv_compress_api_mem_write_req_sb_data_out = {po_api_rw_addr, po_api_wr_data};

    logic [ABR_MEM_ADDR_WIDTH+DATA_WIDTH-1:0] fv_compress_api_mem_write_req_sb_expected_data;

    lubis_scoreboard
    #( 	
        .DATA_WIDTH             (ABR_MEM_ADDR_WIDTH+DATA_WIDTH                  ),
    	.DEPTH                  (1                                              )
    ) fv_compress_api_mem_write_req_sb (
        .clk                    (pi_clk                                         ),
    	.rst                    (!pi_reset_n || pi_zeroize                      ),
        .soft_rst               (1'b0                                           ),
        .push                   (fv_compress_api_mem_write_req_sb_push          ),
    	.pop                    (fv_compress_api_mem_write_req_sb_pop           ),
    	.full                   (1'b0                                           ),
    	.empty                  (1'b0                                           ),
    	.data_in                (fv_compress_api_mem_write_req_sb_data_in       ),
        .data_out               (fv_compress_api_mem_write_req_sb_data_out      ),
        .expected_data          (fv_compress_api_mem_write_req_sb_expected_data ),
        .incr_val               (1'h1                                           ),
        .sampled_in             (                                               ),
        .sampled_in_reg         (                                               ),
        .sampled_out            (                                               ),
        .sampled_out_reg        (                                               ),
        .chosen_symbolic_data   (fv_compress_api_mem_write_req_sb_expected_data ),
        .tracking_counter_out   (                                               )        
    );

    // Safety property to check that there is a pop for every push for better performance than the liveness
    assert_compress_api_mem_write_req_sb_for_every_push_there_is_pop: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_compress_api_mem_write_req_sb_push
    |->
        ##1 fv_compress_api_mem_write_req_sb_pop
    );

    // Safety properties to check that for every compress_enable, there is a done

    logic fv_compression_active;
    always_ff @(posedge pi_clk or negedge pi_reset_n) begin
        if(!pi_reset_n || pi_zeroize) begin
            fv_compression_active <= 1'b0;
        end else begin
            if(pi_compress_enable) begin
                fv_compression_active <= 1'b1;
            end else if(po_compress_done) begin
                fv_compression_active <= 1'b0;
            end
        end
    end

    // If the formal compression is done, then the compress_done signal should be raised after 2 cycles
    assert_compress_done_safety_high: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_compression_done
    |->
        ##0 !po_compress_done
        ##1 !po_compress_done
        ##1 po_compress_done
        ##1 !po_compress_done
    );

    // If there is no compression active, or a compression is ongoing, but not done, then compress_done should stay low
    assert_compress_done_after_low: assert property(disable iff(!pi_reset_n || pi_zeroize)
        !fv_compression_active ||
        fv_tracking_active &&
        !fv_compression_done
    |->
        !po_compress_done
    );

    // If there is no active compression, the design should not send out anything
    assert_no_activities: assert property(disable iff(!pi_reset_n || pi_zeroize)
        !fv_compression_active
    |->
        (po_mem_rd_req.rd_wr_en == RW_IDLE) &&
        (po_api_rw_en == 2'b00) &&
        !po_compare_failed &&
        !po_compress_done
    );

    /////////////////////////////////////////////////////////////////////////
    // Scoreboard to check that for every compressed word during compare mode
    // there is a read request to the api memory
    ////////////

    logic fv_compress_api_mem_read_req_sb_push;
    assign fv_compress_api_mem_read_req_sb_push = fv_compressed_word_push && fv_compare_mode;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_api_mem_read_req_sb_data_in;
    assign fv_compress_api_mem_read_req_sb_data_in = {fv_api_rw_addr_ff};

    // Pop the scoreboard for every write to the api memory that is not part of the compare mode
    logic fv_compress_api_mem_read_req_sb_pop;
    assign fv_compress_api_mem_read_req_sb_pop = (po_api_rw_en == 2'b10) && fv_tracking_started && !fv_tracking_done_ff;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_api_mem_read_req_sb_data_out;
    assign fv_compress_api_mem_read_req_sb_data_out = po_api_rw_addr;

    logic [ABR_MEM_ADDR_WIDTH-1:0] fv_compress_api_mem_read_req_sb_expected_data;

    lubis_scoreboard
    #( 	
        .DATA_WIDTH             (ABR_MEM_ADDR_WIDTH                             ),
    	.DEPTH                  (1                                              )
    ) fv_compress_api_mem_read_req_sb (
        .clk                    (pi_clk                                         ),
    	.rst                    (!pi_reset_n || pi_zeroize                      ),
        .soft_rst               (1'b0                                           ),
        .push                   (fv_compress_api_mem_read_req_sb_push           ),
    	.pop                    (fv_compress_api_mem_read_req_sb_pop            ),
    	.full                   (1'b0                                           ),
    	.empty                  (1'b0                                           ),
    	.data_in                (fv_compress_api_mem_read_req_sb_data_in        ),
        .data_out               (fv_compress_api_mem_read_req_sb_data_out       ),
        .expected_data          (fv_compress_api_mem_read_req_sb_expected_data  ),
        .incr_val               (1'h1                                           ),
        .sampled_in             (                                               ),
        .sampled_in_reg         (                                               ),
        .sampled_out            (                                               ),
        .sampled_out_reg        (                                               ),
        .chosen_symbolic_data   (fv_compress_api_mem_read_req_sb_expected_data  ),
        .tracking_counter_out   (                                               )        
    );

    // Safety property to check that there is a pop for every push for better performance than the liveness
    assert_compress_api_mem_read_req_sb_for_every_push_there_is_pop: assert property(disable iff(!pi_reset_n || pi_zeroize)
        fv_compress_api_mem_read_req_sb_push
    |->
        ##1 fv_compress_api_mem_read_req_sb_pop
    );
    
    // compare_failed is raised if there was a read request to the api memory in the previous cycle and the received data from the api memory doesn't equal the compressed data
    assert_compare_failed: assert property(disable iff(!pi_reset_n || pi_zeroize)
        (po_api_rw_en == 2'b10)
    |->
        ##1 po_compare_failed == (pi_api_rd_data != $past(po_api_wr_data))
    );

    property assert_compare_failed_v2_p;
        logic [DATA_WIDTH-1:0] fv_compressed_word_stored;
        (fv_compress_api_mem_read_req_sb_push, fv_compressed_word_stored = fv_compressed_word)
        ##1 po_api_rw_en == (2'b10)
    |->
        ##1 po_compare_failed == (pi_api_rd_data != fv_compressed_word_stored)
    ;endproperty
    assert_compare_failed_v2: assert property(disable iff(!pi_reset_n || pi_zeroize) assert_compare_failed_v2_p);

    // Cover to detect the bound of two compressions
    cover_two_compressions_done: cover property(disable iff(!pi_reset_n || pi_zeroize)
        po_compress_done [->2]
    );

    cover_two_compressions_done_00: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_compress_done && pi_mode == 2'b00) [->2]
    );

    cover_two_compressions_done_01: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_compress_done && pi_mode == 2'b01) [->2]
    );

    cover_two_compressions_done_10: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_compress_done && pi_mode == 2'b10) [->2]
    );

    cover_two_compressions_done_11: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (po_compress_done && pi_mode == 2'b11) [->2]
    );

    // Covers to detect the bound of the second compression starting   
    cover_second_compression_start_00: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_compress_enable && pi_mode == 2'b00) [->2]
    );

    cover_second_compression_start_01: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_compress_enable && pi_mode == 2'b01) [->2]
    );

    cover_second_compression_start_10: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_compress_enable && pi_mode == 2'b10) [->2]
    );

    cover_second_compression_start_11: cover property(disable iff(!pi_reset_n || pi_zeroize)
        (pi_compress_enable && pi_mode == 2'b11) [->2]
    );
endmodule


bind compress_top fv_compress_top #(
    //#$bind
) fv_compress_top_i (
    .pi_clk (clk),
    .pi_reset_n (reset_n),
    .pi_zeroize (zeroize),
    .pi_compress_enable (compress_enable),
    .pi_mode (mode),
    .pi_compare_mode (compare_mode),
    .pi_num_poly (num_poly),
    .pi_src_base_addr (src_base_addr),
    .pi_dest_base_addr (dest_base_addr),
    .po_mem_rd_req (mem_rd_req),
    .pi_mem_rd_data (mem_rd_data),
    .po_api_rw_en (api_rw_en),
    .po_api_rw_addr (api_rw_addr),
    .po_api_wr_data (api_wr_data),
    .pi_api_rd_data (api_rd_data),
    .po_compare_failed (compare_failed),
    .po_compress_done (compress_done)
    //$#//
);
