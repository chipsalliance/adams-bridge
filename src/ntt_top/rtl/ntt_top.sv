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
//
//======================================================================
//
// ntt_top.sv
// --------
// This block does multiple things:
// 1. Keeps track of stages of bf2x2 operation
// 2. Reads appropriate addr of ROM and passes w input to bf2x2
// 3. Orchestrates memory writes and reads and passes u and v inputs to bf2x2
// 4. Controls direct PWM inputs to bf2x2 in pwm mode
// 5. Maintains mode input to bf2x2 and related input/output muxes
// 6. Aligns data and control delays associated with bf2x2 module
//    The design accounts for 1 cycle read latency from memory
//    and adds flops to inputs of the bf2x2 (data and enable)
//    In addition to this, data inputs are flopped internal to bf2x2 to balance
//    delays between both paths and maintain constant time
//======================================================================

module ntt_top
    import abr_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter SRAM_LATENCY = 1
)
(
    //Clock and reset
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    //Ctrl signal ports
    input mode_t mode,
    input wire ntt_enable,
    input wire mlkem,

    //NTT base addr ports
    input ntt_mem_addr_t ntt_mem_base_addr,

    //PWM base addr ports
    input pwo_mem_addr_t pwo_mem_base_addr,

    //PWM control
    input wire accumulate,

    //Sampler IF
    input wire sampler_valid,

    input wire shuffle_en,
    input wire [5:0] random,

    //Memory if
    //Reuse between pwm c, ntt
    output mem_if_t mem_wr_req,
    output mem_if_t mem_rd_req,
    output logic [ABR_MEM_DATA_WIDTH-1:0] mem_wr_data,
    input logic mem_rd_data_valid,
    input  wire  [ABR_MEM_DATA_WIDTH-1:0] mem_rd_data,

    //Memory IF for PWM
    output mem_if_t pwm_a_rd_req,
    output mem_if_t pwm_b_rd_req,
    input logic pwm_a_rd_data_valid,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pwm_a_rd_data,
    //Reuse between pwm mem data or sampler data (mux should be outside)
    input logic pwm_b_rd_data_valid,
    input wire [ABR_MEM_DATA_WIDTH-1:0] pwm_b_rd_data,

    output logic ntt_busy,
    output logic ntt_done

);
    // //NTT mem signals

    //Write IF
    logic mem_wren, mem_wren_reg, mem_wren_mux;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr, mem_wr_addr_reg, mem_wr_addr_mux;
    logic [ABR_MEM_DATA_WIDTH-1:0] mem_wr_data_int, mem_wr_data_reg;
    
    //Read IF
    logic mem_rden;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr;
    logic [ABR_MEM_DATA_WIDTH-1:0] mem_rd_data_reg;

    //Butterfly IF signals
    bf_uvwi_t uvw_i;
    bf_uvo_t  uv_o, uv_o_reg;
    logic bf_enable, bf_enable_mux;
    logic [2:0] bf_enable_reg;
    logic bf_ready;
    logic buf0_valid;

    //Internal
    logic [6:0] twiddle_addr;
    logic buf_wren;
    logic buf_rden;
    logic buf_wr_rst_count, buf_rd_rst_count;

    //buffer IF
    logic [(ABR_MEM_DATA_WIDTH)-1:0] buf_data_i, buf_data_o;
    logic [(3*NTT_REG_SIZE)-1:0] twiddle_factor, twiddle_factor_reg;
    logic [NTT_REG_SIZE-1:0] w10_reg, w11_reg;
    logic [1:0] buf_wrptr, buf_rdptr;

    //PWM mem IF
    pwo_uvwi_t pw_uvw_i; //Used for PWM, PWMA
    pwo_t pwo_uv_o;
    logic pw_wren, pw_wren_reg;
    logic pw_rden, pw_rden_dest_mem, pw_rden_reg;
    logic sampler_valid_reg;
    logic [ABR_MEM_DATA_WIDTH-1:0] pwm_b_rd_data_reg;
    
    //Flop ntt_ctrl pwm output wr addr to align with BFU output flop
    logic [ABR_MEM_ADDR_WIDTH-1:0] pwm_wr_addr_c_reg;
    logic [(ABR_MEM_DATA_WIDTH)-1:0] pwm_wr_data_reg;

    //ntt_ctrl output connections
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_wr_addr_c;
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_c, pw_mem_rd_addr_a, pw_mem_rd_addr_b;
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_a_reg, pw_mem_rd_addr_b_reg;
    logic ntt_done_int;

    //pwm mem data_out connections
    logic [(ABR_MEM_DATA_WIDTH)-1:0] pwm_rd_data_a, pwm_rd_data_b; 
    logic [ABR_MEM_DATA_WIDTH-1:0] pwm_rd_data_c; 

    //Flop pwm mem data_out before sending to BFU
    logic [(ABR_MEM_DATA_WIDTH)-1:0] pwm_rd_data_a_reg, pwm_rd_data_b_reg, pwm_rd_data_c_reg;

    //PairWM
    mlkem_pairwm_zeta_t mlkem_pairwm_zeta13_i;

    //Modes
    logic ct_mode;
    logic gs_mode;
    logic pwo_mode;
    logic pwm_mode, pwa_mode, pws_mode;
    logic pairwm_mode;
    mode_t opcode;

    logic ntt_passthrough, intt_passthrough;

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            ct_mode <= 0;
            gs_mode <= 0;
            pwo_mode <= 0;
            pwm_mode <= 0;
            pwa_mode <= 0;
            pws_mode <= 0;
            pairwm_mode <= 0;
        end
        else if (zeroize) begin
            ct_mode <= 0;
            gs_mode <= 0;
            pwo_mode <= 0;
            pwm_mode <= 0;
            pwa_mode <= 0;
            pws_mode <= 0;
            pairwm_mode <= 0;
        end
        else begin
            ct_mode <= (mode == ct);
            gs_mode <= (mode == gs);
            pwo_mode <= (mode inside {pwm, pwa, pws}) | (mlkem & (mode == pairwm));
            pwm_mode <= (mode == pwm);
            pwa_mode <= (mode == pwa);
            pws_mode <= (mode == pws);
            pairwm_mode <= mlkem & (mode == pairwm);
        end
    end

    //Mem IF assignments:
    //mem wr - NTT/INTT mode, write ntt data. PWO mode, write pwm/a/s data
    assign mem_wr_req.rd_wr_en = !pwo_mode ? (mem_wren_mux ? RW_WRITE : RW_IDLE) //TODO convert mem_wren_mux to rw enum
                                           : (pw_wren_reg ? RW_WRITE : RW_IDLE); 
    assign mem_wr_req.addr  = !pwo_mode ? mem_wr_addr_mux : pwm_wr_addr_c_reg;
    assign mem_wr_data_int  = !pwo_mode ? (ct_mode ? {1'b0, uv_o_reg.v21_o, 1'b0, uv_o_reg.u21_o, 1'b0, uv_o_reg.v20_o, 1'b0, uv_o_reg.u20_o} : buf_data_o)
                                        : pwm_wr_data_reg;

    always_comb begin 
            mem_wr_data      = shuffle_en ? (pwm_mode | pairwm_mode) ? ABR_MEM_DATA_WIDTH'(mem_wr_data_reg)
                                                     : (pwa_mode | pws_mode) ? ABR_MEM_DATA_WIDTH'(mem_wr_data_reg) : ABR_MEM_DATA_WIDTH'(mem_wr_data_int)
                                          : ABR_MEM_DATA_WIDTH'(mem_wr_data_int);
    end

    //mem rd - NTT/INTT mode, read ntt data. PWM mode, read accumulate data from c mem. PWA/S mode, unused
    assign mem_rd_req.rd_wr_en = (ct_mode | (gs_mode)) ? (mem_rden ? RW_READ : RW_IDLE) : (pwm_mode | pairwm_mode) ? (pw_rden_dest_mem ? RW_READ : RW_IDLE) : RW_IDLE;
    assign mem_rd_req.addr     = (ct_mode | (gs_mode)) ? mem_rd_addr                    : (pwm_mode | pairwm_mode) ? pw_mem_rd_addr_c : 'h0;
    assign pwm_rd_data_c       = ((pwm_mode | pairwm_mode) & accumulate) ? mem_rd_data : 'h0;


    //pwm rd a - PWO mode - read a operand from mem. NTT/INTT mode, not used
    assign pwm_a_rd_req.rd_wr_en = pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE;
    assign pwm_a_rd_req.addr     = pwo_mode ? pw_mem_rd_addr_a : 'h0;
    assign pwm_rd_data_a         = pwo_mode ? pwm_a_rd_data[ABR_MEM_DATA_WIDTH-1:0] : 'h0;

    //pwm rd b - PWO mode - read b operand from mem. Or operand b can also be connected directly to sampler, so in that case, addr/rden are not used
    always_comb begin
        if (shuffle_en) begin
            pwm_b_rd_req.rd_wr_en = sampler_valid_reg & pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE; //pw_rden is delayed a clk due to shuffling, so use delayed sampler_valid to line it up
            pwm_b_rd_req.addr     = sampler_valid_reg & pwo_mode ? pw_mem_rd_addr_b : 'h0;
            pwm_rd_data_b         = pwm_b_rd_data_reg;
        end
        else begin
            pwm_b_rd_req.rd_wr_en = sampler_valid & pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE;
            pwm_b_rd_req.addr     = sampler_valid & pwo_mode ? pw_mem_rd_addr_b : 'h0;
            pwm_rd_data_b         = pwm_b_rd_data[ABR_MEM_DATA_WIDTH-1:0];
        end
    end

    
    ntt_ctrl #(
        .SRAM_LATENCY(SRAM_LATENCY)
    )
    ntt_ctrl_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .ntt_mode(mode),
        .ntt_enable(ntt_enable),
        .butterfly_ready(bf_ready),
        .buf0_valid(buf0_valid),
        .sampler_valid(sampler_valid),
        .shuffle_en(shuffle_en),
        .random(random),
        .mlkem(mlkem),
        .mem_rd_data_valid(mem_rd_data_valid),

        .ntt_mem_base_addr(ntt_mem_base_addr),
        .pwo_mem_base_addr(pwo_mem_base_addr),
        .accumulate(accumulate),

        .bf_enable(bf_enable),
        .opcode(opcode),
        .buf_wren(buf_wren),
        .buf_rden(buf_rden),
        .buf_wrptr(buf_wrptr),
        .buf_rdptr(buf_rdptr),
        .twiddle_addr(twiddle_addr),

        .mem_rd_addr(mem_rd_addr),
        .mem_wr_addr(mem_wr_addr),
        .mem_rd_en(mem_rden),
        .mem_wr_en(mem_wren),
        .buf_wr_rst_count(buf_wr_rst_count),
        .buf_rd_rst_count(buf_rd_rst_count),

        .pw_mem_rd_addr_a(pw_mem_rd_addr_a),
        .pw_mem_rd_addr_b(pw_mem_rd_addr_b),
        .pw_mem_rd_addr_c(pw_mem_rd_addr_c),
        .pw_mem_wr_addr_c(pw_mem_wr_addr_c),
        .pw_rden(pw_rden),
        .pw_rden_dest_mem(pw_rden_dest_mem),
        .pw_wren(pw_wren),
        .busy(ntt_busy),
        .done(ntt_done_int),
        .ntt_passthrough(ntt_passthrough),
        .intt_passthrough(intt_passthrough)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            ntt_done <= 'b0;
        else if (zeroize)
            ntt_done <= 'b0;
        else
            ntt_done <= ntt_done_int;
    end

    //Twiddle lookup
    ntt_twiddle_lookup #(
        .ADDR_WIDTH(7),
        .DATA_WIDTH(NTT_REG_SIZE)
    ) w_rom (
        .mode(mode),
        .mlkem(mlkem),
        .raddr(twiddle_addr),
        .rdata(twiddle_factor)
    );

    always_comb begin
        unique case(mode)
            ct: begin
                uvw_i.w00_i = mlkem ? {12'h0, twiddle_factor[MLKEM_REG_SIZE-1:0]}                       : twiddle_factor[NTT_REG_SIZE-1:0];
                uvw_i.w01_i = mlkem ? {12'h0, twiddle_factor[MLKEM_REG_SIZE-1:0]}                       : twiddle_factor[NTT_REG_SIZE-1:0];
                uvw_i.w10_i = mlkem ? {12'h0, twiddle_factor[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]}      : twiddle_factor[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE];
                uvw_i.w11_i = mlkem ? {12'h0, twiddle_factor[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]}  : twiddle_factor[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
            end
            gs: begin
                if (shuffle_en) begin
                    uvw_i.w11_i = mlkem ? {12'h0, twiddle_factor[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : twiddle_factor[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                    uvw_i.w10_i = mlkem ? {12'h0, twiddle_factor[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : twiddle_factor[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                    uvw_i.w01_i = mlkem ? {12'h0, twiddle_factor[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]}     : twiddle_factor[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE];
                    uvw_i.w00_i = mlkem ? {12'h0, twiddle_factor[MLKEM_REG_SIZE-1:0]}                      : twiddle_factor[NTT_REG_SIZE-1:0];
                end
                else begin
                    uvw_i.w11_i = mlkem ? {12'h0, twiddle_factor_reg[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : twiddle_factor_reg[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                    uvw_i.w10_i = mlkem ? {12'h0, twiddle_factor_reg[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)]} : twiddle_factor_reg[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                    uvw_i.w01_i = mlkem ? {12'h0, twiddle_factor_reg[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]}     : twiddle_factor_reg[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE];
                    uvw_i.w00_i = mlkem ? {12'h0, twiddle_factor_reg[MLKEM_REG_SIZE-1:0]}                      : twiddle_factor_reg[NTT_REG_SIZE-1:0];
                end
            end
            default: begin
                uvw_i.w11_i = 'h0;
                uvw_i.w10_i = 'h0;
                uvw_i.w01_i = 'h0;
                uvw_i.w00_i = 'h0;
            end
        endcase
    end

    always_comb begin
        if (mlkem & (mode == pairwm)) begin
                mlkem_pairwm_zeta13_i.z0_i = twiddle_factor_reg[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]; // twiddle addr increments 1 clk before 2x2 receives enable, hence use flopped twiddle_factor
                mlkem_pairwm_zeta13_i.z1_i = twiddle_factor_reg[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)];
        end
        else begin
            mlkem_pairwm_zeta13_i = '0;
        end
    end

    ntt_hybrid_butterfly_2x2 hybrid_bf2x2 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(opcode),
        .enable(bf_enable_mux),
        .shuffle_en(shuffle_en),
        .mlkem(mlkem),
        .uvw_i(uvw_i),
        .pw_uvw_i(pw_uvw_i),
        .accumulate(accumulate),
        .mlkem_pairwm_zeta13_i(mlkem_pairwm_zeta13_i),
        .ntt_passthrough(ntt_passthrough),
        .intt_passthrough(intt_passthrough),
        .uv_o(uv_o),
        .pwo_uv_o(pwo_uv_o),
        .ready_o(bf_ready)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_data_reg     <= 'h0;
            bf_enable_reg       <= 'b0;
            twiddle_factor_reg  <= 'h0;

            uv_o_reg            <= 'h0;
            mem_wren_reg        <= 'b0;
            mem_wr_addr_reg     <= 'h0;

            //pwm
            pwm_rd_data_a_reg   <= 'h0;
            pwm_rd_data_b_reg   <= 'h0;
            pwm_rd_data_c_reg   <= 'h0;
            pwm_wr_data_reg     <= 'h0;

            pwm_wr_addr_c_reg   <= 'h0;

            pw_wren_reg         <= 'b0;
            mem_wr_data_reg     <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;

            pw_rden_reg          <= '0;
            pw_mem_rd_addr_a_reg <= '0;
            pw_mem_rd_addr_b_reg <= '0;

            w10_reg <= '0;
            w11_reg <= '0;
            
        end
        else if (zeroize) begin
            mem_rd_data_reg     <= 'h0;
            bf_enable_reg       <= 'b0;
            twiddle_factor_reg  <= 'h0;

            uv_o_reg            <= 'h0;
            mem_wren_reg        <= 'b0;
            mem_wr_addr_reg     <= 'h0;

            pwm_rd_data_a_reg   <= 'h0;
            pwm_rd_data_b_reg   <= 'h0;
            pwm_rd_data_c_reg   <= 'h0;
            pwm_wr_data_reg     <= 'h0;

            pwm_wr_addr_c_reg   <= 'h0;

            pw_wren_reg         <= 'b0;
            mem_wr_data_reg     <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;

            pw_rden_reg          <= '0;
            pw_mem_rd_addr_a_reg <= '0;
            pw_mem_rd_addr_b_reg <= '0;

            w10_reg <= '0;
            w11_reg <= '0;
        end
        else begin
            mem_rd_data_reg     <= mem_rd_data[ABR_MEM_DATA_WIDTH-1:0];
            bf_enable_reg       <= {bf_enable_reg[1:0], bf_enable};
            twiddle_factor_reg  <= twiddle_factor;

            uv_o_reg            <= uv_o;
            mem_wren_reg        <= mem_wren;
            mem_wr_addr_reg     <= mem_wr_addr;

            //pwm
            pwm_wr_addr_c_reg   <= pw_mem_wr_addr_c;
            
            pwm_rd_data_a_reg   <= pwm_rd_data_a;
            pwm_rd_data_b_reg   <= pwm_rd_data_b;
            pwm_rd_data_c_reg   <= pwm_rd_data_c[ABR_MEM_DATA_WIDTH-1:0];
            pwm_wr_data_reg     <= {1'b0, pwo_uv_o.uv3, 1'b0, pwo_uv_o.uv2, 1'b0, pwo_uv_o.uv1, 1'b0, pwo_uv_o.uv0};

            pw_wren_reg         <= pw_wren;
            mem_wr_data_reg     <= mem_wr_data_int;
            sampler_valid_reg   <= sampler_valid;
            pwm_b_rd_data_reg   <= pwm_b_rd_data[ABR_MEM_DATA_WIDTH-1:0];

            pw_rden_reg          <= pw_rden;
            pw_mem_rd_addr_a_reg <= pw_mem_rd_addr_a;
            pw_mem_rd_addr_b_reg <= pw_mem_rd_addr_b;

            w10_reg <= uvw_i.w10_i;
            w11_reg <= uvw_i.w11_i;
            
        end
    end

    //Buffer (input or output side)
    assign buf_data_i = ct_mode ? mem_rd_data[ABR_MEM_DATA_WIDTH-1:0] : 
                        shuffle_en ? {1'b0, uv_o_reg.v21_o, 1'b0, uv_o_reg.v20_o, 1'b0, uv_o_reg.u21_o, 1'b0, uv_o_reg.u20_o} : 
                                     {1'b0, uv_o.v21_o, 1'b0, uv_o.v20_o, 1'b0, uv_o.u21_o, 1'b0, uv_o.u20_o};

    always_comb begin
        unique case(opcode)
        ct: begin
            uvw_i.u00_i      = buf_data_o[REG_SIZE-2:0] ; 
            uvw_i.u01_i      = buf_data_o[(2*REG_SIZE)-2:REG_SIZE] ; 
            uvw_i.v00_i      = buf_data_o[(3*REG_SIZE)-2:(2*REG_SIZE)] ; 
            uvw_i.v01_i      = buf_data_o[(4*REG_SIZE)-2:(3*REG_SIZE)] ;

            pw_uvw_i         = 'h0;
        end
        gs: begin
            uvw_i.u00_i      = mem_rd_data_reg[REG_SIZE-2:0];
            uvw_i.u01_i      = mem_rd_data_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
            uvw_i.v00_i      = mem_rd_data_reg[(2*REG_SIZE)-2:REG_SIZE];
            uvw_i.v01_i      = mem_rd_data_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

            pw_uvw_i         = 'h0;
        end
        pwm, pairwm: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

                pw_uvw_i.u0_i    = pwm_rd_data_a_reg[REG_SIZE-2:0];
                pw_uvw_i.u1_i    = pwm_rd_data_a_reg[(2*REG_SIZE)-2:REG_SIZE];
                pw_uvw_i.u2_i    = pwm_rd_data_a_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
                pw_uvw_i.u3_i    = pwm_rd_data_a_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

                if (shuffle_en) begin
                    pw_uvw_i.v0_i    = pwm_rd_data_b[REG_SIZE-2:0];
                    pw_uvw_i.v1_i    = pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE];
                    pw_uvw_i.v2_i    = pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)];
                    pw_uvw_i.v3_i    = pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)];
                end
                else begin
                    pw_uvw_i.v0_i    = pwm_rd_data_b_reg[REG_SIZE-2:0];
                    pw_uvw_i.v1_i    = pwm_rd_data_b_reg[(2*REG_SIZE)-2:REG_SIZE];
                    pw_uvw_i.v2_i    = pwm_rd_data_b_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
                    pw_uvw_i.v3_i    = pwm_rd_data_b_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];
                end

                pw_uvw_i.w0_i    = pwm_rd_data_c_reg[REG_SIZE-2:0];
                pw_uvw_i.w1_i    = pwm_rd_data_c_reg[(2*REG_SIZE)-2:REG_SIZE];
                pw_uvw_i.w2_i    = pwm_rd_data_c_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
                pw_uvw_i.w3_i    = pwm_rd_data_c_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];
        end
        pwa, pws: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

                pw_uvw_i.u0_i    = pwm_rd_data_a_reg[REG_SIZE-2:0];
                pw_uvw_i.u1_i    = pwm_rd_data_a_reg[(2*REG_SIZE)-2:REG_SIZE];
                pw_uvw_i.u2_i    = pwm_rd_data_a_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
                pw_uvw_i.u3_i    = pwm_rd_data_a_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

                if (shuffle_en) begin
                    pw_uvw_i.v0_i    = pwm_rd_data_b/*_reg*/[REG_SIZE-2:0];
                    pw_uvw_i.v1_i    = pwm_rd_data_b/*_reg*/[(2*REG_SIZE)-2:REG_SIZE];
                    pw_uvw_i.v2_i    = pwm_rd_data_b/*_reg*/[(3*REG_SIZE)-2:(2*REG_SIZE)];
                    pw_uvw_i.v3_i    = pwm_rd_data_b/*_reg*/[(4*REG_SIZE)-2:(3*REG_SIZE)];
                end
                else begin
                    pw_uvw_i.v0_i    = pwm_rd_data_b_reg[REG_SIZE-2:0];
                    pw_uvw_i.v1_i    = pwm_rd_data_b_reg[(2*REG_SIZE)-2:REG_SIZE];
                    pw_uvw_i.v2_i    = pwm_rd_data_b_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
                    pw_uvw_i.v3_i    = pwm_rd_data_b_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];
                end

            pw_uvw_i.w0_i    = 'h0;
            pw_uvw_i.w1_i    = 'h0;
            pw_uvw_i.w2_i    = 'h0;
            pw_uvw_i.w3_i    = 'h0;
        end
        default: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

            pw_uvw_i = '0;
        end
        endcase
    end

    assign bf_enable_mux    = ct_mode ? bf_enable       
                                      : bf_enable_reg[0];
    assign mem_wren_mux     = ~shuffle_en & ct_mode ? mem_wren_reg    : mem_wren;
    assign mem_wr_addr_mux  = ~shuffle_en & ct_mode ? mem_wr_addr_reg : mem_wr_addr;


    ntt_shuffle_buffer #(
        .REG_SIZE(REG_SIZE)
    ) buffer_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .shuffle_en(shuffle_en),
        .wren(buf_wren),
        .rden(buf_rden),
        .wrptr(buf_wrptr),
        .rdptr(buf_rdptr),
        .wr_rst_count(buf_wr_rst_count),
        .data_i(buf_data_i),
        .buf_valid(buf0_valid),
        .data_o(buf_data_o)
    );

endmodule
