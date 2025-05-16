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
//======================================================================
//
// sigdecode_h_ctrl.sv
// -----------
// Manages memory writes and read pointer for encoded_h array. 
// Keeps track of indices and polynomial count

module sigdecode_h_ctrl
    import abr_params_pkg::*;
    import sigdecode_h_defines_pkg::*;
    #(
        parameter MLDSA_N = 256,
        parameter MLDSA_K = 8
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire sigdecode_h_enable,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr,
        input wire [7:0] hintsum_i, //points to hintsum of i_th poly shown by poly_count
        input wire sigdecode_h_error,

        output mem_if_t mem_wr_req,
        output logic sigdecode_h_done,
        output logic [3:0] poly_count, //can be used to pass in hintsum
        output logic [6:0] rd_ptr,
        output logic rst_bitmap, 
        output logic [3:0] curr_poly_map,
        output logic [$clog2(MLDSA_N)-1:0] bitmap_ptr,
        output logic hint_rd_en
    );

    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr, mem_wr_addr_nxt;
    logic incr_wr_addr, rst_wr_addr;
    logic last_poly_last_addr_wr, last_poly;
    logic incr_poly;
    mem_rw_mode_e rd_wr_en;
    // logic [3:0] poly_count;
    //poly_done_rd is asserted when all indices of curr poly are processed, i.e. rem_hintsum reaches 0
    //poly_done_wr is asserted when all 256 coeffs have been written for that poly to mem (equivalent to incr_poly if incr_poly is trigd by write fsm)
    logic hint_rd_en_f;
    logic poly_done_rd, poly_done_wr;
    logic sigdecode_h_busy;

    //read pointer
    logic incr_rd_ptr;
    logic [7:0] rem_hintsum, hintsum_mux_sel;
    logic [3:0] curr_poly_mux;
    logic latch_hintsum, decr_rem_hintsum;

    sdh_read_state_e  read_fsm_state_ps, read_fsm_state_ns;
    sdh_write_state_e write_fsm_state_ps, write_fsm_state_ns;

    //Read fsm arcs
    logic arc_SDH_RD_EXEC_SDH_RD_IDLE;
    logic arc_SDH_RD_IDLE_SDH_RD_INIT;
    logic arc_SDH_RD_INIT_SDH_RD_IDLE;
    logic arc_SDH_RD_INIT_SDH_RD_HINTSUM;
    logic arc_SDH_RD_EXEC_SDH_RD_INIT;
    // logic arc_SDH_RD_INIT_SDH_RD_IDLE;

    //Write fsm arcs
    logic arc_SDH_WR_IDLE_SDH_WR_INIT;
    logic arc_SDH_WR_INIT_SDH_WR_MEM;
    logic arc_SDH_WR_MEM_SDH_WR_INIT;
    logic arc_SDH_WR_MEM_SDH_WR_IDLE;
    logic arc_SDH_WR_INIT_SDH_WR_IDLE;

    //Write addr counter
    always_comb mem_wr_addr_nxt = mem_wr_addr + 'h1;
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_wr_addr <= 'h0;
        end
        else if (zeroize) begin
            mem_wr_addr <= 'h0;
        end
        else if (rst_wr_addr) begin
            mem_wr_addr <= dest_base_addr;
        end
        else if (incr_wr_addr) begin
            mem_wr_addr <= last_poly_last_addr_wr ? 'h0 : mem_wr_addr_nxt;
        end
    end

    always_comb poly_done_wr = (mem_wr_addr[5:0] == ((MLDSA_N/4 - 1)));

    //Poly counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            poly_count <= 'h0;
        end
        else if (zeroize) begin
            poly_count <= 'h0;
        end
        else if (incr_poly)
            poly_count <= (poly_count == MLDSA_K) ? 'h0 : poly_count + 'h1;
    end

    //bitmap ptr counter
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            bitmap_ptr <= 'h0;
        end
        else if (zeroize) begin
            bitmap_ptr <= 'h0;
        end
        else if (incr_wr_addr)
            bitmap_ptr <= poly_done_wr ? 'h0 : bitmap_ptr + 'h4;
    end

    //Flags
    always_comb begin
        last_poly_last_addr_wr  = (mem_wr_addr == dest_base_addr + (MLDSA_K * (MLDSA_N/4))-1);
        last_poly               = (poly_count == MLDSA_K-1);
        sigdecode_h_busy        = (write_fsm_state_ps != SDH_WR_IDLE); //writes follow reads, so using that for busy
        sigdecode_h_done        = (read_fsm_state_ps == SDH_RD_IDLE) & (write_fsm_state_ps == SDH_WR_IDLE);
    end

    //Curr poly mux
    //We read 1 dword (4 bytes) from reg API by default every cycle. If hintsum >= 4, all four we read belong to curr poly
    //If hintsum < 4, only a few of the bytes belong to curr poly. This mux decodes that.
    //rd_ptr always starts reading from a curr poly index, so valid hints start from lsb. Meaning, there is no chance
    //that there is a hint in the lsb side that belongs to next poly and a hint that belongs to curr poly on the msb side 
    always_comb begin
        hintsum_mux_sel = latch_hintsum ? hintsum_i : rem_hintsum; //in the first cycle, take hintsum //TODO: move to reg?
        case(hintsum_mux_sel)
            'h0: curr_poly_mux = 'b0000;
            'h1: curr_poly_mux = 'b0001;
            'h2: curr_poly_mux = 'b0011;
            'h3: curr_poly_mux = 'b0111;
            default: curr_poly_mux = 'b0000;
        endcase
    end
    
    //Hintsum logic
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rem_hintsum     <= 'h0;
            curr_poly_map   <= 'h0;
        end
        else if (zeroize) begin
            rem_hintsum     <= 'h0;
            curr_poly_map   <= 'h0;
        end
        else if (latch_hintsum) begin
            rem_hintsum     <= hintsum_i;
            curr_poly_map   <= 'h0;
        end
        else if (poly_done_rd) begin
            rem_hintsum     <= 'h0;
            curr_poly_map   <= 'h0;
        end
        else if (decr_rem_hintsum) begin
            rem_hintsum     <= (rem_hintsum >= 'h4) ? rem_hintsum - 'h4 : 'h0; //If rem_hintsum < 4, it indicates last cycle of that poly, and we have read all locations of y for that poly, so reset to 0
            curr_poly_map   <= (rem_hintsum >= 'h4) ? 'b1111 : curr_poly_mux;
        end
    end

    always_comb poly_done_rd = (read_fsm_state_ps == SDH_RD_EXEC) & (rem_hintsum == 'h0);

    //Rd ptr logic
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            rd_ptr <= 'h0;
        end
        else if (zeroize) begin
            rd_ptr <= 'h0;
        end
        else if (incr_rd_ptr) begin
            rd_ptr <= (rem_hintsum >= 'h4) ? rd_ptr + 'h4 : 7'(rd_ptr + rem_hintsum);
        end
    end

    //-----------------
    //Read fsm
    //-----------------
    always_comb begin
        arc_SDH_RD_IDLE_SDH_RD_INIT     = (read_fsm_state_ps == SDH_RD_IDLE) & sigdecode_h_enable;
        arc_SDH_RD_INIT_SDH_RD_HINTSUM  = (read_fsm_state_ps == SDH_RD_INIT) & (write_fsm_state_ps == SDH_WR_INIT);
        arc_SDH_RD_INIT_SDH_RD_IDLE     = (read_fsm_state_ps == SDH_RD_INIT) & sigdecode_h_error;
        arc_SDH_RD_EXEC_SDH_RD_INIT     = (read_fsm_state_ps == SDH_RD_EXEC) & ~last_poly & poly_done_rd;
        arc_SDH_RD_EXEC_SDH_RD_IDLE     = (read_fsm_state_ps == SDH_RD_EXEC) & ((last_poly & poly_done_rd) | sigdecode_h_error);
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= SDH_RD_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= SDH_RD_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end


    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            hint_rd_en_f <= '0;
        else if (zeroize)
            hint_rd_en_f <= '0;
        else
            hint_rd_en_f <= hint_rd_en;
    end

    always_comb begin
        incr_rd_ptr         = 'b0;
        read_fsm_state_ns   = read_fsm_state_ps;
        latch_hintsum       = 'b0;
        decr_rem_hintsum    = 'b0;
        hint_rd_en          = 'b0;

        case(read_fsm_state_ps)
            SDH_RD_IDLE: begin
                read_fsm_state_ns   = arc_SDH_RD_IDLE_SDH_RD_INIT ? SDH_RD_INIT : SDH_RD_IDLE;
            end
            SDH_RD_INIT: begin
                read_fsm_state_ns   = arc_SDH_RD_INIT_SDH_RD_IDLE ? SDH_RD_IDLE :
                                      arc_SDH_RD_INIT_SDH_RD_HINTSUM ? SDH_RD_HINTSUM : SDH_RD_INIT;
            end
            SDH_RD_HINTSUM: begin
                read_fsm_state_ns   = SDH_RD_EXEC;
                latch_hintsum       = 'b1;
            end
            SDH_RD_EXEC: begin
                read_fsm_state_ns   = arc_SDH_RD_EXEC_SDH_RD_IDLE ? SDH_RD_IDLE :
                                      arc_SDH_RD_EXEC_SDH_RD_INIT ? SDH_RD_INIT :
                                      SDH_RD_EXEC;
                incr_rd_ptr         = (~poly_done_rd);
                decr_rem_hintsum    = 'b1;
                hint_rd_en          = ~arc_SDH_RD_EXEC_SDH_RD_INIT & ~arc_SDH_RD_EXEC_SDH_RD_IDLE;
            end
        endcase
    end

    //-----------------
    //Write fsm
    //-----------------
    always_comb begin
        arc_SDH_WR_IDLE_SDH_WR_INIT = (write_fsm_state_ps == SDH_WR_IDLE) & sigdecode_h_enable;
        arc_SDH_WR_INIT_SDH_WR_MEM  = (write_fsm_state_ps == SDH_WR_INIT) & (hint_rd_en_f | poly_done_rd); //hint_rd_en indicates bitmap is going to be constructed, so we can move to WR MEM state
        arc_SDH_WR_INIT_SDH_WR_IDLE = (write_fsm_state_ps == SDH_WR_INIT) & sigdecode_h_error;
        arc_SDH_WR_MEM_SDH_WR_INIT  = (write_fsm_state_ps == SDH_WR_MEM) & ~last_poly & poly_done_wr;
        arc_SDH_WR_MEM_SDH_WR_IDLE  = (write_fsm_state_ps == SDH_WR_MEM) & ((last_poly & poly_done_wr) | sigdecode_h_error);
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            write_fsm_state_ps <= SDH_WR_IDLE;
        else if (zeroize)
            write_fsm_state_ps <= SDH_WR_IDLE;
        else
            write_fsm_state_ps <= write_fsm_state_ns;
    end

    always_comb begin
        incr_wr_addr        = 'b0;
        rst_wr_addr         = 'b0;
        incr_poly           = 'b0;
        rst_bitmap          = 'b0;
        rd_wr_en            = RW_IDLE;
        write_fsm_state_ns  = write_fsm_state_ps;

        case(write_fsm_state_ps)
            SDH_WR_IDLE: begin
                write_fsm_state_ns  = arc_SDH_WR_IDLE_SDH_WR_INIT ? SDH_WR_INIT : SDH_WR_IDLE;
                rst_wr_addr         = 'b1;
            end
            SDH_WR_INIT: begin
                write_fsm_state_ns  = arc_SDH_WR_INIT_SDH_WR_IDLE ? SDH_WR_IDLE :
                                      arc_SDH_WR_INIT_SDH_WR_MEM ? SDH_WR_MEM :
                                      SDH_WR_INIT;
            end
            SDH_WR_MEM: begin
                write_fsm_state_ns  = arc_SDH_WR_MEM_SDH_WR_IDLE ? SDH_WR_IDLE :
                                      arc_SDH_WR_MEM_SDH_WR_INIT ? SDH_WR_INIT :
                                      SDH_WR_MEM;
                incr_wr_addr        = 'b1;
                incr_poly           = poly_done_wr; 
                rd_wr_en            = RW_WRITE;
                rst_bitmap          = arc_SDH_WR_MEM_SDH_WR_INIT | arc_SDH_WR_MEM_SDH_WR_IDLE;
            end
            default: begin
                
            end
        endcase
    end

    //Assign outputs
    always_comb begin
        mem_wr_req.addr     = mem_wr_addr;
        mem_wr_req.rd_wr_en = rd_wr_en;
    end


endmodule
