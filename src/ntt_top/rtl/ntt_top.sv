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
    parameter REG_SIZE = 24,
    parameter NTT_REG_SIZE = REG_SIZE-1,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q + 1) / 2,
    parameter MLDSA_N = 256,
    parameter MLDSA_LOGN = $clog2(MLDSA_N),
    parameter MEM_ADDR_WIDTH = 15,
    parameter MEM_DATA_WIDTH = 4*REG_SIZE,
    parameter WIDTH = 46
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
    input wire masking_en,
    input wire [5:0] random,
    input wire [4:0][WIDTH-1:0] rnd_i,

    //Memory if
    //Reuse between pwm c, ntt
    output mem_if_t mem_wr_req,
    output mem_if_t mem_rd_req,
    output logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] mem_wr_data,
    input  wire  [ABR_MEM_MASKED_DATA_WIDTH-1:0] mem_rd_data,

    //Memory IF for PWM
    output mem_if_t pwm_a_rd_req,
    output mem_if_t pwm_b_rd_req,
    input wire [ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_a_rd_data,
    //Reuse between pwm mem data or sampler data (mux should be outside)
    input wire [ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_b_rd_data,

    output logic ntt_busy,
    output logic ntt_done

);
    //NTT mem signals
    //Masking internal - TODO: remove and merge with mem_wr/rd interface after testing
    mem_if_t share_mem_wr_req, share_mem_rd_req, share_mem_rd_req_reg;
    logic [3:0][1:0][MLDSA_SHARE_WIDTH-1:0] share_mem_rd_data, share_mem_wr_data, share_mem_wr_data_reg, share_mem_wr_data_comb;
    logic [(MLKEM_NUM_SHARES*COEFF_PER_CLK)-1:0][MLDSA_SHARE_WIDTH-1:0] mlkem_share_mem_rd_data; //Used for mlkem masking

    //Write IF
    logic mem_wren, mem_wren_reg, mem_wren_mux;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_wr_addr, mem_wr_addr_reg, mem_wr_addr_mux;
    logic [MEM_DATA_WIDTH-1:0] mem_wr_data_int, mem_wr_data_reg, mem_wr_data_reg_d2;
    
    //Read IF
    logic mem_rden;
    logic [ABR_MEM_ADDR_WIDTH-1:0] mem_rd_addr;
    logic [(4*REG_SIZE)-1:0] mem_rd_data_reg;

    //Butterfly IF signals
    bf_uvwi_t uvw_i;
    bf_uvo_t  uv_o, uv_o_reg;
    logic bf_enable, bf_enable_mux;
    logic [2:0] bf_enable_reg;
    logic bf_ready;
    logic buf0_valid;

    //Internal
    logic [6:0] twiddle_addr, twiddle_addr_reg;
    logic buf_wren;
    logic buf_rden;
    logic buf_wr_rst_count, buf_rd_rst_count;

    //buffer IF
    logic [(4*REG_SIZE)-1:0] buf_data_i, buf_data_o;
    logic [(3*NTT_REG_SIZE)-1:0] twiddle_factor, twiddle_factor_reg;
    logic [NTT_REG_SIZE-1:0] w10_reg, w11_reg;
    logic [1:0] buf_wrptr, buf_rdptr;

    //PWM mem IF
    pwo_uvwi_t pw_uvw_i; //Used for unmasked PWM, PWMA and masked PWM ops. Masked PWMA will use shares struct
    pwo_t pwo_uv_o;
    logic pw_wren, pw_wren_reg, pw_wren_reg_d1;
    logic pw_rden, pw_rden_dest_mem, pw_rden_reg;
    logic sampler_valid_reg;
    logic [MEM_DATA_WIDTH-1:0] pwm_b_rd_data_reg;
    //PWM+INTT IF - masking
    hybrid_bf_uvwi_t hybrid_pw_uvw_i;

    //PWM, INTT masking
    masked_intt_uvwi_t bf_shares_uvw_i; //Used for masked INTT op
    pwm_shares_uvwi_t pwm_shares_uvw_i; //Used for masked PWM op
    logic [3:0][1:0][MASKED_WIDTH-1:0] share_mem_rd_data_reg, share_mem_rd_data_reg_d1;

    //Flop ntt_ctrl pwm output wr addr to align with BFU output flop
    logic [ABR_MEM_ADDR_WIDTH-1:0] pwm_wr_addr_c_reg, pwm_wr_addr_c_reg_d2;
    logic [(4*REG_SIZE)-1:0] pwm_wr_data_reg;

    //ntt_ctrl output connections
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_wr_addr_c;
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_c, pw_mem_rd_addr_a, pw_mem_rd_addr_b;
    logic [ABR_MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_a_reg, pw_mem_rd_addr_b_reg;
    logic ntt_done_int;

    //pwm mem data_out connections
    logic [(4*REG_SIZE)-1:0] pwm_rd_data_a, pwm_rd_data_b; 
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] pwm_rd_data_c; 

    //Flop pwm mem data_out before sending to BFU
    logic [(4*REG_SIZE)-1:0] pwm_rd_data_a_reg, pwm_rd_data_b_reg, pwm_rd_data_c_reg;

    //PWM input shares
    logic [3:0][1:0][MASKED_WIDTH-1:0] pwm_rd_data_a_shares_reg, pwm_rd_data_b_shares_reg;
    logic [3:0][1:0][MASKED_WIDTH-1:0] pwm_rd_data_a_shares_reg_d1, pwm_rd_data_b_shares_reg_d1; //delayed by a cycle
    logic [1:0][1:0][MASKED_WIDTH-1:0] twiddle_factor_shares_reg, twiddle_factor_shares_reg_d1, twiddle_factor_shares_reg_d2; //only 2 required since only 1st stage of INTT is masked and needs this
    //PWM output shares
    pwm_shares_uvo_t pwm_shares_uvo, pwm_shares_uvo_reg;

    //PairWM
    mlkem_pairwm_zeta_t mlkem_pairwm_zeta13_i;
    mlkem_masked_pairwm_zeta_shares_t mlkem_shares_pairwm_zeta13_i;

    //Modes
    logic ct_mode;
    logic gs_mode;
    logic pwo_mode;
    logic pwm_mode, pwa_mode, pws_mode;
    logic pairwm_mode;
    mode_t opcode;
    logic masking_en_ctrl;

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

    //Share mem: TODO: mlkem
    assign share_mem_wr_req.rd_wr_en = ((pwm_mode | pairwm_mode) & masking_en) ? ((accumulate ? pw_wren_reg_d1 : pw_wren_reg) ? RW_WRITE : RW_IDLE) : RW_IDLE;
    assign share_mem_wr_req.addr     = ((pwm_mode | pairwm_mode) & masking_en) ? accumulate ? pwm_wr_addr_c_reg_d2 : pwm_wr_addr_c_reg : 'h0; //TODO: why is d2 required for accumulate case?
    assign share_mem_rd_req.rd_wr_en = masking_en ? ((pwm_mode | pairwm_mode) & accumulate) ? (pw_rden_dest_mem ? RW_READ : RW_IDLE) 
                                                                            : (gs_mode & masking_en_ctrl) ? (mem_rden ? RW_READ : RW_IDLE)
                                                                                      : RW_IDLE
                                                  : RW_IDLE;
    assign share_mem_rd_req.addr     = masking_en ? ((pwm_mode | pairwm_mode) & accumulate) ? pw_mem_rd_addr_c 
                                                                            : (gs_mode & masking_en_ctrl) ? mem_rd_addr : 'h0
                                                  : 'h0;
    always_comb begin 
        if (!masking_en) //TODO: use flopped masking_en?
            mem_wr_data      = shuffle_en ? (pwm_mode | pairwm_mode) ? ABR_MEM_MASKED_DATA_WIDTH'(mem_wr_data_reg)
                                                     : (pwa_mode | pws_mode) ? ABR_MEM_MASKED_DATA_WIDTH'(mem_wr_data_reg) : ABR_MEM_MASKED_DATA_WIDTH'(mem_wr_data_int)
                                          : ABR_MEM_MASKED_DATA_WIDTH'(mem_wr_data_int);
        else
            mem_wr_data      = gs_mode ? ABR_MEM_MASKED_DATA_WIDTH'(mem_wr_data_int) : (pwm_mode | pairwm_mode) ? shuffle_en ? share_mem_wr_data : share_mem_wr_data_comb : '0; //In masking, only gs_mode will have mem wr data. PWM mode will write only shares
    end
    
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            share_mem_wr_data <= '0;
            share_mem_wr_data_reg <= '0;
        end
        else if (zeroize) begin
            share_mem_wr_data <= '0;
            share_mem_wr_data_reg <= '0;
        end
        else if (masking_en & (pwm_mode | pairwm_mode)) begin
            //Pad with 0s to match port width
            share_mem_wr_data[0] <= {2'b0, pwm_shares_uvo_reg.uv0[1], 2'b0, pwm_shares_uvo_reg.uv0[0]};
            share_mem_wr_data[1] <= {2'b0, pwm_shares_uvo_reg.uv1[1], 2'b0, pwm_shares_uvo_reg.uv1[0]};
            share_mem_wr_data[2] <= {2'b0, pwm_shares_uvo_reg.uv2[1], 2'b0, pwm_shares_uvo_reg.uv2[0]};
            share_mem_wr_data[3] <= {2'b0, pwm_shares_uvo_reg.uv3[1], 2'b0, pwm_shares_uvo_reg.uv3[0]};

            share_mem_wr_data_reg <= share_mem_wr_data;
        end
        else begin
            share_mem_wr_data <= '0;
            share_mem_wr_data_reg <= '0;
        end
            
    end

    always_comb begin
        share_mem_wr_data_comb[0] = {2'b0, pwm_shares_uvo_reg.uv0[1], 2'b0, pwm_shares_uvo_reg.uv0[0]};
        share_mem_wr_data_comb[1] = {2'b0, pwm_shares_uvo_reg.uv1[1], 2'b0, pwm_shares_uvo_reg.uv1[0]};
        share_mem_wr_data_comb[2] = {2'b0, pwm_shares_uvo_reg.uv2[1], 2'b0, pwm_shares_uvo_reg.uv2[0]};
        share_mem_wr_data_comb[3] = {2'b0, pwm_shares_uvo_reg.uv3[1], 2'b0, pwm_shares_uvo_reg.uv3[0]}; 
    end

    //mem rd - NTT/INTT mode, read ntt data. PWM mode, read accumulate data from c mem. PWA/S mode, unused
    assign mem_rd_req.rd_wr_en = (ct_mode | (gs_mode & ~masking_en_ctrl)) ? (mem_rden ? RW_READ : RW_IDLE) : (gs_mode & masking_en_ctrl) ? share_mem_rd_req.rd_wr_en : (pwm_mode | pairwm_mode) ? masking_en ? share_mem_rd_req.rd_wr_en : (pw_rden_dest_mem ? RW_READ : RW_IDLE) : RW_IDLE;
    assign mem_rd_req.addr     = (ct_mode | (gs_mode & ~masking_en_ctrl)) ? mem_rd_addr : (gs_mode & masking_en_ctrl) ? share_mem_rd_req.addr : (pwm_mode | pairwm_mode) ? masking_en ? share_mem_rd_req.addr : pw_mem_rd_addr_c : 'h0;
    assign pwm_rd_data_c       = ((pwm_mode | pairwm_mode) & accumulate) ? mem_rd_data : 'h0;

    always_comb begin
        for (int i = 0; i < 8; i++) begin
            mlkem_share_mem_rd_data[i] = MLDSA_SHARE_WIDTH'(mem_rd_data[(i*48) +: 47]);
        end
    end

    assign share_mem_rd_data   = (gs_mode & masking_en_ctrl) ? (mlkem ? mlkem_share_mem_rd_data : mem_rd_data) 
                                                             : ABR_MEM_MASKED_DATA_WIDTH'(pwm_rd_data_c);

    //pwm rd a - PWO mode - read a operand from mem. NTT/INTT mode, not used
    assign pwm_a_rd_req.rd_wr_en = pwo_mode ? (masking_en & ~shuffle_en) ? (pw_rden_reg ? RW_READ : RW_IDLE) : (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE;
    assign pwm_a_rd_req.addr     = pwo_mode ? (masking_en & ~shuffle_en) ? pw_mem_rd_addr_a_reg : pw_mem_rd_addr_a : 'h0;
    assign pwm_rd_data_a         = pwo_mode ? pwm_a_rd_data[MEM_DATA_WIDTH-1:0] : 'h0;

    //pwm rd b - PWO mode - read b operand from mem. Or operand b can also be connected directly to sampler, so in that case, addr/rden are not used
    always_comb begin
        if (shuffle_en) begin
            pwm_b_rd_req.rd_wr_en = sampler_valid_reg & pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE; //pw_rden is delayed a clk due to shuffling, so use delayed sampler_valid to line it up
            pwm_b_rd_req.addr     = sampler_valid_reg & pwo_mode ? pw_mem_rd_addr_b : 'h0;
            pwm_rd_data_b         = pwm_b_rd_data_reg;
        end
        else begin
            pwm_b_rd_req.rd_wr_en = sampler_valid & pwo_mode ? masking_en ? (pw_rden_reg ? RW_READ : RW_IDLE) : (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE;
            pwm_b_rd_req.addr     = sampler_valid & pwo_mode ? masking_en ? pw_mem_rd_addr_b_reg : pw_mem_rd_addr_b : 'h0;
            pwm_rd_data_b         = ((pwm_mode | pairwm_mode) & masking_en & ~shuffle_en) ? pwm_b_rd_data_reg : pwm_b_rd_data[MEM_DATA_WIDTH-1:0];
        end
    end

    
    ntt_ctrl #(
        .MEM_ADDR_WIDTH(ABR_MEM_ADDR_WIDTH)
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

        .ntt_mem_base_addr(ntt_mem_base_addr),
        .pwo_mem_base_addr(pwo_mem_base_addr),
        .accumulate(accumulate),

        .bf_enable(bf_enable),
        .opcode(opcode),
        .masking_en(masking_en),
        .masking_en_ctrl(masking_en_ctrl),
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
        .pw_share_mem_rden(pw_rden_dest_mem),
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
            if (masking_en) begin
                mlkem_shares_pairwm_zeta13_i.z0_i[0] = shuffle_en ? (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d1[0][0]) : (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d2[0][0]); //In masked + shuffled mode, twiddle addr increments 2 clks before 2x2 receives enable. Using d1 version ensures additional 2 clk delay to match latency of a/b inputs to pairwm modules. (a/b require 4 cycles from incr_rd_addr to shares going to pairwm inputs)
                mlkem_shares_pairwm_zeta13_i.z0_i[1] = shuffle_en ? (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d1[0][1]) : (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d2[0][1]); //In masked only mode, twiddle addr increments 3 clks before 2x2 receives enable, hence use d2 version
                
                mlkem_shares_pairwm_zeta13_i.z1_i[0] = shuffle_en ? (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d1[1][0]) : (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d2[1][0]);
                mlkem_shares_pairwm_zeta13_i.z1_i[1] = shuffle_en ? (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d1[1][1]) : (MLKEM_MASKED_WIDTH)'(twiddle_factor_shares_reg_d2[1][1]); 
                
                mlkem_pairwm_zeta13_i = '0;
            end
            else begin
                mlkem_pairwm_zeta13_i.z0_i = twiddle_factor_reg[(2*MLKEM_REG_SIZE)-1:MLKEM_REG_SIZE]; // In non-masking mode, twiddle addr increments 1 clk before 2x2 receives enable, hence use flopped twiddle_factor
                mlkem_pairwm_zeta13_i.z1_i = twiddle_factor_reg[(3*MLKEM_REG_SIZE)-1:(2*MLKEM_REG_SIZE)];
                mlkem_shares_pairwm_zeta13_i = '0;
            end
        end
        else begin
            mlkem_pairwm_zeta13_i = '0;
            mlkem_shares_pairwm_zeta13_i = '0;
        end
    end

    ntt_hybrid_butterfly_2x2 #(
        .WIDTH(WIDTH)
    )
    hybrid_bf2x2 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(opcode),
        .enable(bf_enable_mux),
        .masking_en(gs_mode ? masking_en_ctrl : masking_en),
        .shuffle_en(shuffle_en),
        .mlkem(mlkem),
        .uvw_i(uvw_i),
        .pw_uvw_i(pw_uvw_i),
        .pwm_shares_uvw_i(pwm_shares_uvw_i),
        .rnd_i(rnd_i),
        .accumulate(accumulate),
        .bf_shares_uvw_i(bf_shares_uvw_i),
        .mlkem_pairwm_zeta13_i(mlkem_pairwm_zeta13_i),
        .mlkem_shares_pairwm_zeta13_i(mlkem_shares_pairwm_zeta13_i),
        .ntt_passthrough(ntt_passthrough),
        .intt_passthrough(intt_passthrough),
        .uv_o(uv_o),
        .pwo_uv_o(pwo_uv_o),
        .pwm_shares_uvo(pwm_shares_uvo),
        .ready_o(bf_ready)
    );

    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            mem_rd_data_reg     <= 'h0;
            bf_enable_reg       <= 'b0;
            twiddle_addr_reg    <= 'h0;
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
            pwm_wr_addr_c_reg_d2 <= 'h0;

            pw_wren_reg         <= 'b0;
            pw_wren_reg_d1      <= 'b0;
            mem_wr_data_reg     <= 'h0;
            mem_wr_data_reg_d2  <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;

            share_mem_rd_data_reg <= 'h0;
            share_mem_rd_data_reg_d1 <= '0;
            pwm_shares_uvo_reg <= '{uv0: '0, uv1: '0, uv2: '0, uv3: '0};

            //PWM shares
            for (int i = 0; i < 4; i++) begin
                for (int j = 0; j < 2; j++) begin
                    pwm_rd_data_a_shares_reg[i][j] <= '0;
                    pwm_rd_data_b_shares_reg[i][j] <= '0;
                end
            end
            pwm_rd_data_a_shares_reg_d1 <= '0;
            pwm_rd_data_b_shares_reg_d1 <= '0;

            //INTT twiddle shares
            for (int i = 0; i < 2; i++) begin
                for (int j = 0; j < 2; j++) begin
                    twiddle_factor_shares_reg[i][j] <= '0;
                end
            end

            pw_rden_reg          <= '0;
            pw_mem_rd_addr_a_reg <= '0;
            pw_mem_rd_addr_b_reg <= '0;
            share_mem_rd_req_reg <= '{rd_wr_en: RW_IDLE, addr: '0};

            w10_reg <= '0;
            w11_reg <= '0;
            twiddle_factor_shares_reg_d1 <= '0;
            twiddle_factor_shares_reg_d2 <= '0;
            
        end
        else if (zeroize) begin
            mem_rd_data_reg     <= 'h0;
            bf_enable_reg       <= 'b0;
            twiddle_addr_reg    <= 'h0;
            twiddle_factor_reg  <= 'h0;

            uv_o_reg            <= 'h0;
            mem_wren_reg        <= 'b0;
            mem_wr_addr_reg     <= 'h0;

            pwm_rd_data_a_reg   <= 'h0;
            pwm_rd_data_b_reg   <= 'h0;
            pwm_rd_data_c_reg   <= 'h0;
            pwm_wr_data_reg     <= 'h0;

            pwm_wr_addr_c_reg   <= 'h0;
            pwm_wr_addr_c_reg_d2 <= 'h0;

            pw_wren_reg         <= 'b0;
            pw_wren_reg_d1      <= 'b0;
            mem_wr_data_reg     <= 'h0;
            mem_wr_data_reg_d2  <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;

            share_mem_rd_data_reg <= 'h0;
            share_mem_rd_data_reg_d1 <= '0;
            pwm_shares_uvo_reg <= '{uv0: '0, uv1: '0, uv2: '0, uv3: '0};

            //PWM shares
            for (int i = 0; i < 4; i++) begin
                for (int j = 0; j < 2; j++) begin
                    pwm_rd_data_a_shares_reg[i][j] <= '0;
                    pwm_rd_data_b_shares_reg[i][j] <= '0;
                end
            end
            pwm_rd_data_a_shares_reg_d1 <= '0;
            pwm_rd_data_b_shares_reg_d1 <= '0;

            //INTT twiddle shares
            for (int i = 0; i < 2; i++) begin
                for (int j = 0; j < 2; j++) begin
                    twiddle_factor_shares_reg[i][j] <= '0;
                end
            end

            pw_rden_reg          <= '0;
            pw_mem_rd_addr_a_reg <= '0;
            pw_mem_rd_addr_b_reg <= '0;
            share_mem_rd_req_reg <= '{rd_wr_en: RW_IDLE, addr: '0};

            w10_reg <= '0;
            w11_reg <= '0;
            twiddle_factor_shares_reg_d1 <= '0;
            twiddle_factor_shares_reg_d2 <= '0;
        end
        else begin
            mem_rd_data_reg     <= mem_rd_data[MEM_DATA_WIDTH-1:0];
            bf_enable_reg       <= {bf_enable_reg[1:0], bf_enable};
            twiddle_addr_reg    <= twiddle_addr;
            twiddle_factor_reg  <= twiddle_factor;

            uv_o_reg            <= uv_o;
            mem_wren_reg        <= mem_wren;
            mem_wr_addr_reg     <= mem_wr_addr;

            //pwm
            pwm_wr_addr_c_reg   <= pw_mem_wr_addr_c;
            pwm_wr_addr_c_reg_d2 <= pwm_wr_addr_c_reg;
            
            pwm_rd_data_a_reg   <= pwm_rd_data_a;
            pwm_rd_data_b_reg   <= pwm_rd_data_b;
            pwm_rd_data_c_reg   <= pwm_rd_data_c[MEM_DATA_WIDTH-1:0]; //used in non-masking mode
            pwm_wr_data_reg     <= {1'b0, pwo_uv_o.uv3, 1'b0, pwo_uv_o.uv2, 1'b0, pwo_uv_o.uv1, 1'b0, pwo_uv_o.uv0};

            pw_wren_reg         <= pw_wren;
            pw_wren_reg_d1      <= pw_wren_reg;
            mem_wr_data_reg     <= mem_wr_data_int;
            mem_wr_data_reg_d2  <= mem_wr_data_reg;
            sampler_valid_reg   <= sampler_valid;
            pwm_b_rd_data_reg   <= pwm_b_rd_data[MEM_DATA_WIDTH-1:0];

            //Re-organize mem rd data since incoming shares are 48-bits. Internally we need 46-bit shares
            for (int i = 0; i < 4; i++) begin
                for (int j = 0; j < 2; j++) begin
                    share_mem_rd_data_reg[i][j] <= share_mem_rd_data[i][j][(MLDSA_SHARE_WIDTH-1)-2:0];
                end
            end
            
            share_mem_rd_data_reg_d1 <= share_mem_rd_data_reg;

            //PWM shares
            pwm_rd_data_a_shares_reg[0][0] <= MASKED_WIDTH'(pwm_rd_data_a[REG_SIZE-2:0]) - rnd_i[0];
            pwm_rd_data_b_shares_reg[0][0] <= MASKED_WIDTH'(pwm_rd_data_b[REG_SIZE-2:0]) - rnd_i[1];
            pwm_rd_data_a_shares_reg[0][1] <= rnd_i[0];
            pwm_rd_data_b_shares_reg[0][1] <= rnd_i[1];

            pwm_rd_data_a_shares_reg[1][0] <= MASKED_WIDTH'(pwm_rd_data_a[(2*REG_SIZE)-2:REG_SIZE]) - rnd_i[0];
            pwm_rd_data_b_shares_reg[1][0] <= MASKED_WIDTH'(pwm_rd_data_b[(2*REG_SIZE)-2:REG_SIZE]) - rnd_i[1];
            pwm_rd_data_a_shares_reg[1][1] <= rnd_i[0];
            pwm_rd_data_b_shares_reg[1][1] <= rnd_i[1];

            pwm_rd_data_a_shares_reg[2][0] <= MASKED_WIDTH'(pwm_rd_data_a[(3*REG_SIZE)-2:(2*REG_SIZE)]) - rnd_i[0];
            pwm_rd_data_b_shares_reg[2][0] <= MASKED_WIDTH'(pwm_rd_data_b[(3*REG_SIZE)-2:(2*REG_SIZE)]) - rnd_i[1];
            pwm_rd_data_a_shares_reg[2][1] <= rnd_i[0];
            pwm_rd_data_b_shares_reg[2][1] <= rnd_i[1];

            pwm_rd_data_a_shares_reg[3][0] <= MASKED_WIDTH'(pwm_rd_data_a[(4*REG_SIZE)-2:(3*REG_SIZE)]) - rnd_i[0];
            pwm_rd_data_b_shares_reg[3][0] <= MASKED_WIDTH'(pwm_rd_data_b[(4*REG_SIZE)-2:(3*REG_SIZE)]) - rnd_i[1];
            pwm_rd_data_a_shares_reg[3][1] <= rnd_i[0];
            pwm_rd_data_b_shares_reg[3][1] <= rnd_i[1];

            pwm_rd_data_a_shares_reg_d1    <= pwm_rd_data_a_shares_reg;
            pwm_rd_data_b_shares_reg_d1    <= pwm_rd_data_b_shares_reg;

            pwm_shares_uvo_reg <= pwm_shares_uvo;

            //INTT shares
            twiddle_factor_shares_reg[0][0] <= mlkem ? (MASKED_WIDTH)'((2*MLKEM_Q_WIDTH)'(twiddle_factor[(2*MLKEM_Q_WIDTH)-1:MLKEM_Q_WIDTH]) - (rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0])) : MASKED_WIDTH'(twiddle_factor[NTT_REG_SIZE-1:0]) - rnd_i[2];
            twiddle_factor_shares_reg[0][1] <= mlkem ? (MASKED_WIDTH)'(rnd_i[2][(2*MLKEM_Q_WIDTH)-1:0]) : rnd_i[2];

            twiddle_factor_shares_reg[1][0] <= mlkem ? (MASKED_WIDTH)'((2*MLKEM_Q_WIDTH)'(twiddle_factor[(3*MLKEM_Q_WIDTH)-1:(2*MLKEM_Q_WIDTH)]) - (rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0])) : MASKED_WIDTH'(twiddle_factor[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE]) - rnd_i[3];
            twiddle_factor_shares_reg[1][1] <= mlkem ? (MASKED_WIDTH)'(rnd_i[3][(2*MLKEM_Q_WIDTH)-1:0]) : rnd_i[3];

            pw_rden_reg          <= pw_rden;
            pw_mem_rd_addr_a_reg <= pw_mem_rd_addr_a;
            pw_mem_rd_addr_b_reg <= pw_mem_rd_addr_b;
            share_mem_rd_req_reg <= share_mem_rd_req;

            w10_reg <= uvw_i.w10_i;
            w11_reg <= uvw_i.w11_i;
            twiddle_factor_shares_reg_d1 <= twiddle_factor_shares_reg;
            twiddle_factor_shares_reg_d2 <= twiddle_factor_shares_reg_d1;
            
        end
    end

    //Buffer (input or output side)
    assign buf_data_i = ct_mode ? mem_rd_data[MEM_DATA_WIDTH-1:0] : shuffle_en ? {1'b0, uv_o_reg.v21_o, 1'b0, uv_o_reg.v20_o, 1'b0, uv_o_reg.u21_o, 1'b0, uv_o_reg.u20_o}
                                                            : {1'b0, uv_o.v21_o, 1'b0, uv_o.v20_o, 1'b0, uv_o.u21_o, 1'b0, uv_o.u20_o};

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
            uvw_i.u00_i      = masking_en_ctrl ? '0 : mem_rd_data_reg[REG_SIZE-2:0];
            uvw_i.u01_i      = masking_en_ctrl ? '0 : mem_rd_data_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
            uvw_i.v00_i      = masking_en_ctrl ? '0 : mem_rd_data_reg[(2*REG_SIZE)-2:REG_SIZE];
            uvw_i.v01_i      = masking_en_ctrl ? '0 : mem_rd_data_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

            pw_uvw_i         = 'h0;
        end
        pwm, pairwm: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

            if (~masking_en) begin
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
            else begin
                pw_uvw_i = '0;
            end
        end
        pwa, pws: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

            if (~masking_en) begin
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
            end
            else begin
                pw_uvw_i = '0;
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

    always_comb begin
        //Assign masked INTT input shares coming from share mem
        if (gs_mode & masking_en_ctrl) begin
            bf_shares_uvw_i  = '{u00_i: share_mem_rd_data_reg_d1[0],
                                 u01_i: share_mem_rd_data_reg_d1[2], 
                                 v00_i: share_mem_rd_data_reg_d1[1], 
                                 v01_i: share_mem_rd_data_reg_d1[3], 
                                 w00_i: shuffle_en ? twiddle_factor_shares_reg[0] : twiddle_factor_shares_reg_d1[0], // shuffle mode needs twiddle to be delayed by a cycle. But here, non-shuffle mode is also delayed due to splitting. Hence other inputs are adjusted to match latency
                                 w01_i: shuffle_en ? twiddle_factor_shares_reg[1] : twiddle_factor_shares_reg_d1[1],
                                 w10_i: w10_reg,
                                 w11_i: w11_reg};
        end
        else begin
            bf_shares_uvw_i  = '{u00_i: '0, u01_i: '0, v00_i: '0, v01_i: '0, w00_i: '0, w01_i: '0, w10_i: '0, w11_i: '0};
        end
    end

    always_comb begin
        //Assign masked PWM input shares. a, b come from mem/sampler. c comes from share mem. In first round, accumulate = 0, c input should be 0
        if ((pwm_mode | pairwm_mode) & masking_en) begin
                if (shuffle_en) begin
                    pwm_shares_uvw_i.u0_i = pwm_rd_data_a_shares_reg_d1[0]; 
                    pwm_shares_uvw_i.u1_i = pwm_rd_data_a_shares_reg_d1[1];
                    pwm_shares_uvw_i.u2_i = pwm_rd_data_a_shares_reg_d1[2];
                    pwm_shares_uvw_i.u3_i = pwm_rd_data_a_shares_reg_d1[3];

                    pwm_shares_uvw_i.w0_i = accumulate ? share_mem_rd_data_reg[0] : '0;
                    pwm_shares_uvw_i.w1_i = accumulate ? share_mem_rd_data_reg[1] : '0;
                    pwm_shares_uvw_i.w2_i = accumulate ? share_mem_rd_data_reg[2] : '0;
                    pwm_shares_uvw_i.w3_i = accumulate ? share_mem_rd_data_reg[3] : '0;

                    //In shuffle mode, the b input needs to be 1 cycle earlier. But here, non_shuffle mode is also delayed due to splitting. Hence other inputs are adjusted to match latency
                    pwm_shares_uvw_i.v0_i = pwm_rd_data_b_shares_reg[0];
                    pwm_shares_uvw_i.v1_i = pwm_rd_data_b_shares_reg[1]; 
                    pwm_shares_uvw_i.v2_i = pwm_rd_data_b_shares_reg[2]; 
                    pwm_shares_uvw_i.v3_i = pwm_rd_data_b_shares_reg[3];
                end
                else begin
                    pwm_shares_uvw_i.u0_i = pwm_rd_data_a_shares_reg_d1[0]; 
                    pwm_shares_uvw_i.u1_i = pwm_rd_data_a_shares_reg_d1[1];
                    pwm_shares_uvw_i.u2_i = pwm_rd_data_a_shares_reg_d1[2];
                    pwm_shares_uvw_i.u3_i = pwm_rd_data_a_shares_reg_d1[3];

                    pwm_shares_uvw_i.w0_i = accumulate ? pairwm_mode ? share_mem_rd_data_reg[0] /*TODO: why not d1?*/ : share_mem_rd_data_reg_d1[0] : '0;
                    pwm_shares_uvw_i.w1_i = accumulate ? pairwm_mode ? share_mem_rd_data_reg[1] : share_mem_rd_data_reg_d1[1] : '0;
                    pwm_shares_uvw_i.w2_i = accumulate ? pairwm_mode ? share_mem_rd_data_reg[2] : share_mem_rd_data_reg_d1[2] : '0;
                    pwm_shares_uvw_i.w3_i = accumulate ? pairwm_mode ? share_mem_rd_data_reg[3] : share_mem_rd_data_reg_d1[3] : '0;

                    pwm_shares_uvw_i.v0_i = pwm_rd_data_b_shares_reg_d1[0];
                    pwm_shares_uvw_i.v1_i = pwm_rd_data_b_shares_reg_d1[1]; 
                    pwm_shares_uvw_i.v2_i = pwm_rd_data_b_shares_reg_d1[2]; 
                    pwm_shares_uvw_i.v3_i = pwm_rd_data_b_shares_reg_d1[3];
                end
                

        end
        else begin
            pwm_shares_uvw_i = '{u0_i: '0, u1_i: '0, u2_i: '0, u3_i: '0, v0_i: '0, v1_i: '0, v2_i: '0, v3_i: '0, w0_i: '0, w1_i: '0, w2_i: '0, w3_i: '0};
        end
    end

    always_comb hybrid_pw_uvw_i = {pw_uvw_i, uvw_i.w00_i, uvw_i.w01_i, uvw_i.w10_i, uvw_i.w11_i};

    assign bf_enable_mux    = ct_mode ? bf_enable       
                                      : gs_mode ? (masking_en_ctrl ? bf_enable_reg[1] : bf_enable_reg[0]) 
                                                :  ((pwm_mode | pairwm_mode) & masking_en & ~shuffle_en) ? bf_enable_reg[2] : bf_enable_reg[0];
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

    `ABR_ASSERT_NEVER(ASSERT_MASKING_EN, (masking_en & (mode inside {ct, pwa, pws})), clk, reset_n, masking_en);

endmodule
