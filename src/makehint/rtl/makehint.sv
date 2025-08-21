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
// makehint.sv
// --------
// Processes (r, z) inputs and produces a 4-bit hint vector per coefficient
// of a given polynomial. The hint is then checked and the index corresponding
// to 1 in the hint vector is captured in the sample buffer. 1 dword at a time
// is written to reg API
// 1. For the last poly, buffer data_o is written irrespective of number of index
// 2. If only a few indices were captured, we still need to fill rest of bytes of
// 'h' component of signature with 0s. (Length of h is 84 bytes).
// So, we need a check to see how many dwords were written and fill in rest with 0s
// 3. At the end of all polys, another write is required to 83rd byte with max index
// vector
// 4. Generate an invalid flag if any of the max indices is > 75 and keep it set until
// a zeroize or restart is given (TODO: check how restart is given - in the form of a zeroize? Or do we keep track here)
// TODO: we need a separate restart bit that is HW driven while zeroize is SW driven
// Restart bit is asserted for every signing iteration to reset sensitive flops
//======================================================================

module makehint
    import abr_params_pkg::*;
    import makehint_defines_pkg::*;
    #(
        parameter REG_SIZE = 24,
        parameter MLDSA_Q = 23'd8380417,
        parameter MLDSA_N = 256,
        parameter MLDSA_K = 8,
        parameter OMEGA = 75,
        parameter BUFFER_DATA_W = 8
    )
    (
        input wire clk,
        input wire reset_n,
        input wire zeroize,

        input wire makehint_enable,
        input wire [(4*REG_SIZE)-1:0] r,
        input wire [3:0] z,
        input wire [ABR_MEM_ADDR_WIDTH-1:0] mem_base_addr,
        output logic invalid_h,
        output mem_if_t mem_rd_req,
        output mem_if_t z_rd_req,
        output logic makehint_done,
        output logic reg_wren,
        output logic [3:0][7:0] reg_wrdata,
        output logic [ABR_MEM_ADDR_WIDTH-1:0] reg_wr_addr
    );

    //Internal wires
    logic hintgen_enable, hintgen_enable_reg;
    logic [3:0] hint;
    logic [MLDSA_K-1:0][7:0] max_index_buffer;
    logic [31:0] max_index_buffer_data;
    logic max_index_buffer_rd_lo, max_index_buffer_rd_mid, max_index_buffer_rd_hi;  
    logic max_index_buffer_rd;

    //Sample buffer wires
    //Flush buffer will perform last write of last polynomial irrespective of data_valid from sample buffer.
    //This will take care of the case where at the end of index count, if buffer has < NUM_WR values, we still want to capture into reg API, padded with 0s
    //For each poly_done, sample_buffer continues to capture values as they come in and this extra write is not required until the end
    logic flush_buffer, flush_buffer_reg;
    logic sample_valid;
    logic [3:0][BUFFER_DATA_W-1:0] sample_data;

    //Index counter
    logic [3:0][7:0] index;
    logic [7:0] index_count;
    logic incr_index, incr_index_d1, incr_index_d2;

    //Polynomial counter
    logic [$clog2(MLDSA_K)-1:0] poly_count;
    logic incr_poly;
    logic poly_done;
    logic poly_last, poly_last_reg;

    //Read addr counter
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr, reg_wr_addr_nxt, z_rd_addr;
    logic incr_mem_rd_addr;
    logic rst_rd_addr;
    logic last_addr_read;

    //Read fsm
    mh_read_state_e read_fsm_state_ps, read_fsm_state_ns;
    logic arc_MH_IDLE_MH_RD_MEM;
    logic arc_MH_RD_MEM_MH_WAIT1;
    logic arc_MH_WAIT2_MH_IDLE;
    // logic arc_MH_WAIT_MH_RD_MEM; //TODO don't need wait if we do all polys back to back? check this later
    logic arc_MH_WAIT2_MH_FLUSH;

    //Hint sum
    logic [7:0] hintsum;
    logic busy_reg;
    logic latch_hintsum_addr;

    //Busy flag
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            busy_reg <= 'b0;
        else if (zeroize)
            busy_reg <= 'b0;
        else
            busy_reg <= (read_fsm_state_ps != MH_IDLE);
    end

    //Delay adjustment
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            hintgen_enable_reg <= 'b0;
        else if (zeroize)
            hintgen_enable_reg <= 'b0;
        else
            hintgen_enable_reg <= hintgen_enable;
    end

    //Keep count of index. Input is 4 coeffs per cycle. Have a vector that counts
    //(0, 1, 2, 3), (4, 5, 6, 7), etc
    //Flop incr_index twice to account for 1 cycle of mem read latency + 1 cycle of hintgen latency
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            incr_index_d1 <= 'h0;
            incr_index_d2 <= 'h0;
        end
        else if (zeroize | makehint_done) begin
            incr_index_d1 <= 'h0;
            incr_index_d2 <= 'h0;
        end
        else begin
            incr_index_d1 <= incr_index;
            incr_index_d2 <= incr_index_d1;
        end
    end
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            index_count <= 'h0;
        end
        else if (zeroize | makehint_done) begin
            index_count <= 'h0;
        end
        else if (incr_index_d1) begin
            index_count <= index_count + 'h4;
        end
    end

    always_comb begin
        index[0] = incr_index_d1 ? index_count       : 'h0;
        index[1] = incr_index_d1 ? index_count + 'h1 : 'h0;
        index[2] = incr_index_d1 ? index_count + 'h2 : 'h0;
        index[3] = incr_index_d1 ? index_count + 'h3 : 'h0;
    end

    //Keep count of polynomial. 1 polynomial needs 64 memory addr accesses == 256 index count (0 to 255)
    //After each poly_done, record the last index into max_index_buffer
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            poly_count <= 'h0;
        else if (zeroize | makehint_done)
            poly_count <= 'h0;
        else if (incr_poly)
            poly_count <= poly_count + 'h1;
    end

    always_comb begin
        poly_done = incr_poly; //last_addr_read;
        poly_last = (poly_count == 'h7);
        flush_buffer = (read_fsm_state_ps == MH_FLUSH_SBUF); //poly_last & poly_done; //TODO: check to make sure all indexes have been processed before this flag goes high
    end

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            poly_last_reg <= 'b0;
            flush_buffer_reg <= 'b0;
        end
        else if (zeroize | makehint_done) begin
            poly_last_reg <= 'b0;
            flush_buffer_reg <= 'b0;
        end
        else begin
            poly_last_reg <= poly_last;
            flush_buffer_reg <= flush_buffer;
        end
    end
    
    //-----------------------
    //Count number of 1s in each poly
    //-----------------------
    //Sample_data from sample buffer also gives this, but we don't know where the last index would be in the 4 bytes of data received from the buffer
    //Instead count 1s manually and store sum into max_index_buffer for every poly_done
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            hintsum <= 'h0;
        else if (zeroize | makehint_done)
            hintsum <= 'h0;
        else
            hintsum <= hintsum + hint[3] + hint[2] + hint[1] + hint[0];
    end


    //-----------------------
    //Populate max_index_buffer
    //-----------------------
    always_comb max_index_buffer_rd = max_index_buffer_rd_lo | max_index_buffer_rd_mid | max_index_buffer_rd_hi;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            max_index_buffer <= 'h0;
        else if (zeroize | makehint_done)
            max_index_buffer <= 'h0;
        else if (poly_done)
            max_index_buffer <= {hintsum, max_index_buffer[MLDSA_K-1:1]};
    end
    assign max_index_buffer_data = max_index_buffer_rd_lo ? {max_index_buffer[0], 24'h0} : 
                                   max_index_buffer_rd_mid ? max_index_buffer[4:1] :
                                   max_index_buffer_rd_hi ? {8'h0, max_index_buffer[7:5]} : 'h0;

    //Reg API
    //Write from sample buffer for each dword captured per polynomial.
    //If last poly is done, flush buffer and write to reg API
    //After that, write the max_index_buffer contents to reg API - using delayed poly_last as the wren in this case
    assign reg_wren = sample_valid | flush_buffer | max_index_buffer_rd;
    assign reg_wrdata = max_index_buffer_rd ? max_index_buffer_data : (sample_valid | flush_buffer) ? sample_data : 'h0;

    always_comb reg_wr_addr_nxt = latch_hintsum_addr ? (OMEGA/4) : reg_wr_addr + 'h1; //Latch hintsum dword addr at the end of hint processing

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_wr_addr <= 'h0;
        end
        else if (zeroize | makehint_done) begin
            reg_wr_addr <= 'h0;
        end
        else if (sample_valid | flush_buffer | max_index_buffer_rd) begin
            reg_wr_addr <= reg_wr_addr_nxt;
        end
    end

    assign invalid_h = (hintsum > OMEGA);

    //----------------------------
    //Read addr counter
    //----------------------------
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_addr <= 'h0;
            z_rd_addr <= 'h0;
        end
        else if (zeroize) begin
            mem_rd_addr <= 'h0;
            z_rd_addr <= 'h0;
        end
        else if (rst_rd_addr) begin
            mem_rd_addr <= mem_base_addr;
            z_rd_addr <= 'h0;
        end
        else if (incr_mem_rd_addr) begin
            mem_rd_addr <= (poly_last && last_addr_read) ? mem_base_addr : mem_rd_addr + 'h1;
            z_rd_addr <= (poly_last && last_addr_read) ? 'h0 : z_rd_addr + 'h1;
        end
    end

    assign last_addr_read = (mem_rd_addr == mem_base_addr + ABR_MEM_ADDR_WIDTH'(((poly_count+1) * (MLDSA_N/4))-1));

    //----------------------------
    //Read fsm
    //----------------------------
    //State machine to control memory rd addr/en and buffer read
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            read_fsm_state_ps <= MH_IDLE;
        else if (zeroize)
            read_fsm_state_ps <= MH_IDLE;
        else
            read_fsm_state_ps <= read_fsm_state_ns;
    end

    //Arc assignment
    always_comb begin
        //Start makehint upon seeing enable trigger
        arc_MH_IDLE_MH_RD_MEM = (read_fsm_state_ps == MH_IDLE) && makehint_enable;
        //When any poly is done (last or not), wait for 1 cyc to give time for sample buffer to process last coeffs
        arc_MH_RD_MEM_MH_WAIT1 = (read_fsm_state_ps == MH_RD_MEM) && last_addr_read;
        //When non-last poly is done, move to IDLE and wait for next enable. Opt - if we know all 8 poly will be back to back, we can remain in RD_MEM and wrap addr around + take new base addr if needed, calc hints and continue execution without waiting in IDLE for HLC to give enable
        arc_MH_WAIT2_MH_IDLE = (read_fsm_state_ps == MH_WAIT2) && !poly_last;
        //When non-last poly is done, go back to RD_MEM and continue executing
        arc_MH_WAIT2_MH_FLUSH = (read_fsm_state_ps == MH_WAIT2) && (poly_count == MLDSA_K-1);
    end

    always_comb begin
        read_fsm_state_ns = read_fsm_state_ps;
        incr_mem_rd_addr  = 'b0;
        incr_index        = 'b0;
        rst_rd_addr       = 'b0;
        hintgen_enable    = 'b0;
        max_index_buffer_rd_lo = 'b0;
        max_index_buffer_rd_mid = 'b0;
        max_index_buffer_rd_hi = 'b0;
        incr_poly         = 'b0;
        latch_hintsum_addr = 'b0;
        unique case(read_fsm_state_ps)
            MH_IDLE: begin
                read_fsm_state_ns   = arc_MH_IDLE_MH_RD_MEM ? MH_RD_MEM : MH_IDLE;
                rst_rd_addr         = 'b1;
            end
            MH_RD_MEM: begin
                //Read memory and produce hints for (r,z)
                read_fsm_state_ns   = arc_MH_RD_MEM_MH_WAIT1 ? MH_WAIT1 : MH_RD_MEM;
                incr_mem_rd_addr    = 'b1;
                incr_index          = 'b1;
                hintgen_enable      = 'b1;
            end
            MH_WAIT1: begin
                read_fsm_state_ns = MH_WAIT2;
            end
            MH_WAIT2: begin
                //After all 64 addr are done, wait for 1 clk to let sample buffer finish last coeff
                read_fsm_state_ns   = arc_MH_WAIT2_MH_FLUSH ? MH_FLUSH_SBUF : MH_RD_MEM; //arc_MH_WAIT2_MH_RD_MEM ? MH_RD_MEM : MH_FLUSH_SBUF_LOW;
                incr_poly           = 'b1;
            end
            MH_FLUSH_SBUF: begin
                //If last poly, flush sample buffer
                read_fsm_state_ns   = MH_RD_IBUF_LOW;
                latch_hintsum_addr  = 'b1; //prepare for next state
            end
            MH_RD_IBUF_LOW: begin
                //last poly, write lower dword of max idx buf to reg API
                read_fsm_state_ns   = MH_RD_IBUF_MID;
                max_index_buffer_rd_lo = 'b1;
            end
            MH_RD_IBUF_MID: begin
                read_fsm_state_ns   = MH_RD_IBUF_HIGH;
                max_index_buffer_rd_mid = 'b1;
            end
            MH_RD_IBUF_HIGH: begin
                //last poly, write higher dword of max idx buf to reg API
                read_fsm_state_ns   = MH_IDLE;
                max_index_buffer_rd_hi = 'b1;
            end
            default: begin
                read_fsm_state_ns   = MH_IDLE;
            end
        endcase
    end

    //Assign output
    assign mem_rd_req.rd_wr_en = (read_fsm_state_ps == MH_RD_MEM) ? RW_READ : RW_IDLE;
    assign mem_rd_req.addr     = mem_rd_addr;
    assign z_rd_req.rd_wr_en   = (read_fsm_state_ps == MH_RD_MEM) ? RW_READ : RW_IDLE;
    assign z_rd_req.addr       = z_rd_addr;
    assign makehint_done       = (read_fsm_state_ps == MH_IDLE);

    generate
        for (genvar i = 0; i < 4; i++) begin : gen_hint
            hintgen #(
                .REG_SIZE(REG_SIZE-1)
            )
            hint_inst (
                .clk(clk),
                .reset_n(reset_n),
                .zeroize(zeroize),
                .enable(hintgen_enable_reg),
                .r(r[(REG_SIZE*i)+(REG_SIZE-2):(REG_SIZE*i)]), //remove MSB 0 since coeff coming from memory is 24 bit
                .z_neq_z(z[i]),
                .h(hint[i])
            );
        end
    endgenerate

    abr_sample_buffer #(
        .NUM_WR(4),
        .NUM_RD(4),
        .BUFFER_DATA_W(BUFFER_DATA_W)
    )
    hint_index_buffer_inst (
        .clk(clk),
        .rst_b(reset_n),
        .zeroize(zeroize | flush_buffer),
        .data_valid_i(hint),
        .data_i(index),
        .buffer_full_o(),
        .data_valid_o(sample_valid),
        .data_o(sample_data)
    );


    
endmodule
