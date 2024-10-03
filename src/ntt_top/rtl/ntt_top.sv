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
    import mldsa_params_pkg::*;
    import ntt_defines_pkg::*;
#(
    parameter REG_SIZE = 24,
    parameter NTT_REG_SIZE = REG_SIZE-1,
    parameter MLDSA_Q = 23'd8380417,
    parameter MLDSA_Q_DIV2_ODD = (MLDSA_Q + 1) / 2,
    parameter MLDSA_N = 256,
    parameter MLDSA_LOGN = $clog2(MLDSA_N),
    parameter MEM_ADDR_WIDTH = 15,
    parameter MEM_DATA_WIDTH = 4*REG_SIZE
)
(
    //Clock and reset
    input wire clk,
    input wire reset_n,
    input wire zeroize,

    //Ctrl signal ports
    input mode_t mode,
    input wire ntt_enable,
    //TB purpose - remove and refine tb
    // input wire load_tb_values,
    // input wire [5:0] load_tb_addr,

    //NTT base addr ports
    // input wire [MEM_ADDR_WIDTH-1:0] src_base_addr,
    // input wire [MEM_ADDR_WIDTH-1:0] interim_base_addr,
    // input wire [MEM_ADDR_WIDTH-1:0] dest_base_addr,
    input ntt_mem_addr_t ntt_mem_base_addr,

    //PWM base addr ports
    // input wire [MEM_ADDR_WIDTH-1:0] pw_base_addr_a,
    // input wire [MEM_ADDR_WIDTH-1:0] pw_base_addr_b,
    // input wire [MEM_ADDR_WIDTH-1:0] pw_base_addr_c,
    input pwo_mem_addr_t pwo_mem_base_addr,

    //PWM control
    input wire accumulate,

    //Sampler IF
    input wire sampler_valid,

    input wire [5:0] random,

    //Memory if
    //Reuse between pwm c, ntt
    output mem_if_t mem_wr_req,
    output mem_if_t mem_rd_req,
    output logic [MEM_DATA_WIDTH-1:0] mem_wr_data,
    input  wire  [MEM_DATA_WIDTH-1:0] mem_rd_data,

    //Memory IF for PWM
    output mem_if_t pwm_a_rd_req,
    output mem_if_t pwm_b_rd_req,
    input wire [MEM_DATA_WIDTH-1:0] pwm_a_rd_data,
    //Reuse between pwm mem data or sampler data (mux should be outside)
    input wire [MEM_DATA_WIDTH-1:0] pwm_b_rd_data,

    output logic ntt_busy,
    output logic ntt_done

);
    //NTT mem signals
    //Write IF
    logic mem_wren, mem_wren_reg, mem_wren_mux;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] mem_wr_addr, mem_wr_addr_reg, mem_wr_addr_mux;
    // logic [(4*REG_SIZE)-1:0] mem_wr_data;
    logic [MEM_DATA_WIDTH-1:0] mem_wr_data_int, mem_wr_data_reg, mem_wr_data_reg_d2;
    
    //Read IF
    logic mem_rden;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] mem_rd_addr;
    logic [(4*REG_SIZE)-1:0] mem_rd_data_reg;

    //Butterfly IF signals
    // logic bf_mode;
    bf_uvwi_t uvw_i;
    bf_uvo_t  uv_o, uv_o_reg;
    logic bf_enable, bf_enable_reg, bf_enable_mux;
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
    logic [1:0] buf_wrptr, buf_rdptr;

    //PWM mem IF
    pwo_uvwi_t pw_uvw_i;
    pwo_t pwo_uv_o;
    logic pw_wren, pw_wren_reg;
    logic pw_rden, pw_rden_dest_mem;
    logic sampler_valid_reg;
    logic [MEM_DATA_WIDTH-1:0] pwm_b_rd_data_reg;

    //Flop ntt_ctrl pwm output wr addr to align with BFU output flop
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pwm_wr_addr_c_reg;
    logic [(4*REG_SIZE)-1:0] pwm_wr_data_reg;

    //ntt_ctrl output connections
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pw_mem_wr_addr_c;
    logic [MLDSA_MEM_ADDR_WIDTH-1:0] pw_mem_rd_addr_c, pw_mem_rd_addr_a, pw_mem_rd_addr_b;

    //pwm mem data_out connections
    logic [(4*REG_SIZE)-1:0] pwm_rd_data_a, pwm_rd_data_b, pwm_rd_data_c; 

    //Flop pwm mem data_out before sending to BFU
    logic [(4*REG_SIZE)-1:0] pwm_rd_data_a_reg, pwm_rd_data_b_reg, pwm_rd_data_c_reg;

    //Modes
    logic ct_mode;
    logic gs_mode;
    logic pwo_mode;
    logic pwm_mode, pwa_mode, pws_mode;

    assign ct_mode = (mode == ct);
    assign gs_mode = (mode == gs);
    assign pwo_mode = (mode inside {pwm, pwa, pws});
    assign pwm_mode = (mode == pwm);
    assign pwa_mode = (mode == pwa);
    assign pws_mode = (mode == pws);
    assign pw_rden_dest_mem = accumulate ? pw_rden : 1'b0;

    //Mem IF assignments:
    //mem wr - NTT/INTT mode, write ntt data. PWO mode, write pwm/a/s data
    assign mem_wr_req.rd_wr_en = !pwo_mode ? (mem_wren_mux ? RW_WRITE : RW_IDLE) //TODO convert mem_wren_mux to rw enum
                                    : (pw_wren_reg ? RW_WRITE : RW_IDLE); 
    assign mem_wr_req.addr  = !pwo_mode ? mem_wr_addr_mux : pwm_wr_addr_c_reg;
    assign mem_wr_data_int  = !pwo_mode ? (ct_mode ? {1'b0, uv_o_reg.v21_o, 1'b0, uv_o_reg.u21_o, 1'b0, uv_o_reg.v20_o, 1'b0, uv_o_reg.u20_o} : buf_data_o)
                                        : pwm_wr_data_reg;
    assign mem_wr_data      = pwm_mode ? mem_wr_data_reg/*_d2*/ : (pwa_mode | pws_mode) ? mem_wr_data_reg : mem_wr_data_int; //ct_mode ? mem_wr_data_reg : mem_wr_data_int; //TODO: gs, pwo modes

    //mem rd - NTT/INTT mode, read ntt data. PWM mode, read accumulate data from c mem. PWA/S mode, unused
    assign mem_rd_req.rd_wr_en = (ct_mode || gs_mode) ? (mem_rden ? RW_READ : RW_IDLE) : pwm_mode ? (pw_rden_dest_mem ? RW_READ : RW_IDLE) : RW_IDLE;
    assign mem_rd_req.addr     = (ct_mode || gs_mode) ? mem_rd_addr : pwm_mode ? pw_mem_rd_addr_c : 'h0;
    assign pwm_rd_data_c       = (pwm_mode && accumulate) ? mem_rd_data : 'h0; //TODO: check if this is supposed to be mem_rd_data_reg

    //pwm rd a - PWO mode - read a operand from mem. NTT/INTT mode, not used
    assign pwm_a_rd_req.rd_wr_en = pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE;
    assign pwm_a_rd_req.addr     = pwo_mode ? pw_mem_rd_addr_a : 'h0;
    assign pwm_rd_data_a         = pwo_mode ? pwm_a_rd_data : 'h0; //TODO: clean up mux. Just connect input directly to logic

    //pwm rd b - PWO mode - read b operand from mem. Or operand b can also be connected directly to sampler, so in that case, addr/rden are not used
    assign pwm_b_rd_req.rd_wr_en = sampler_valid_reg & pwo_mode ? (pw_rden ? RW_READ : RW_IDLE) : RW_IDLE; //pw_rden is delayed a clk due to shuffling, so use delayed sampler_valid to line it up
    assign pwm_b_rd_req.addr     = sampler_valid_reg & pwo_mode ? pw_mem_rd_addr_b : 'h0;
    assign pwm_rd_data_b         = pwm_b_rd_data_reg; //sampler_valid_reg ? pwm_b_rd_data_reg : pwm_b_rd_data;

    
    ntt_ctrl #(
        .MEM_ADDR_WIDTH(MLDSA_MEM_ADDR_WIDTH)
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
        .random(random),

        .ntt_mem_base_addr(ntt_mem_base_addr),
        .pwo_mem_base_addr(pwo_mem_base_addr),
        .accumulate(accumulate),

        .bf_enable(bf_enable),
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
        .pw_wren(pw_wren),
        .busy(ntt_busy),
        .done(ntt_done)
    );

    //Twiddle lookup
    ntt_twiddle_lookup #(
        .ADDR_WIDTH(7),
        .DATA_WIDTH(NTT_REG_SIZE)
    ) w_rom (
        .mode(mode),
        .raddr(twiddle_addr),
        .rdata(twiddle_factor)
    );

    always_comb begin
        unique case(mode)
            ct: begin
                //with shuffling, twiddle factor needs to be delayed
                uvw_i.w00_i = twiddle_factor[NTT_REG_SIZE-1:0];
                uvw_i.w01_i = twiddle_factor[NTT_REG_SIZE-1:0];
                uvw_i.w10_i = twiddle_factor[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE];
                uvw_i.w11_i = twiddle_factor[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
            end
            gs: begin
                uvw_i.w11_i = twiddle_factor/*_reg*/[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                uvw_i.w10_i = twiddle_factor/*_reg*/[(3*NTT_REG_SIZE)-1:(2*NTT_REG_SIZE)];
                uvw_i.w01_i = twiddle_factor/*_reg*/[(2*NTT_REG_SIZE)-1:NTT_REG_SIZE];
                uvw_i.w00_i = twiddle_factor/*_reg*/[NTT_REG_SIZE-1:0];
            end
            default: begin
                uvw_i.w11_i = 'h0;
                uvw_i.w10_i = 'h0;
                uvw_i.w01_i = 'h0;
                uvw_i.w00_i = 'h0;
            end
        endcase
    end


    //Butterfly 2x2
    ntt_butterfly2x2 #(
        .REG_SIZE(NTT_REG_SIZE),
        .MLDSA_Q(MLDSA_Q)
    )
    bf2x2 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
        .enable(bf_enable_mux),
        .uvw_i(uvw_i),
        .uv_o(uv_o),
        .pw_uvw_i(pw_uvw_i),
        .accumulate(accumulate),
        .pwo_uv_o(pwo_uv_o),
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

            pw_wren_reg         <= 'b0;
            mem_wr_data_reg     <= 'h0;
            mem_wr_data_reg_d2  <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;
            
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

            pw_wren_reg         <= 'b0;
            mem_wr_data_reg     <= 'h0;
            mem_wr_data_reg_d2  <= 'h0;
            sampler_valid_reg   <= 'h0;
            pwm_b_rd_data_reg   <= 'h0;
        end
        else begin
            mem_rd_data_reg     <= mem_rd_data;
            bf_enable_reg       <= bf_enable;
            twiddle_addr_reg    <= twiddle_addr;
            twiddle_factor_reg  <= twiddle_factor;

            uv_o_reg            <= uv_o;
            mem_wren_reg        <= mem_wren;
            mem_wr_addr_reg     <= mem_wr_addr;

            //pwm
            pwm_wr_addr_c_reg   <= pw_mem_wr_addr_c;
            
            pwm_rd_data_a_reg   <= pwm_rd_data_a;
            pwm_rd_data_b_reg   <= pwm_rd_data_b;
            pwm_rd_data_c_reg   <= pwm_rd_data_c;
            pwm_wr_data_reg     <= {1'b0, pwo_uv_o.uv3, 1'b0, pwo_uv_o.uv2, 1'b0, pwo_uv_o.uv1, 1'b0, pwo_uv_o.uv0};

            pw_wren_reg         <= pw_wren;
            mem_wr_data_reg     <= mem_wr_data_int;
            mem_wr_data_reg_d2  <= mem_wr_data_reg;
            sampler_valid_reg   <= sampler_valid;
            pwm_b_rd_data_reg   <= pwm_b_rd_data;
        end
    end

    //Buffer (input or output side)
    assign buf_data_i = ct_mode ? mem_rd_data : {1'b0, uv_o_reg.v21_o, 1'b0, uv_o_reg.v20_o, 1'b0, uv_o_reg.u21_o, 1'b0, uv_o_reg.u20_o};

    always_comb begin
        unique case(mode)
        ct: begin
            uvw_i.u00_i      = buf_data_o[REG_SIZE-2:0] ; 
            uvw_i.u01_i      = buf_data_o[(2*REG_SIZE)-2:REG_SIZE] ; 
            uvw_i.v00_i      = buf_data_o[(3*REG_SIZE)-2:(2*REG_SIZE)] ; 
            uvw_i.v01_i      = buf_data_o[(4*REG_SIZE)-2:(3*REG_SIZE)] ;

            pw_uvw_i         = 'h0;
        end
        gs: begin
            uvw_i.u00_i      = mem_rd_data_reg[REG_SIZE-2:0]; //[22:0]
            uvw_i.u01_i      = mem_rd_data_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
            uvw_i.v00_i      = mem_rd_data_reg[(2*REG_SIZE)-2:REG_SIZE];
            uvw_i.v01_i      = mem_rd_data_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

            pw_uvw_i         = 'h0;
        end
        pwm: begin
            uvw_i.u00_i      = 'h0;
            uvw_i.u01_i      = 'h0;
            uvw_i.v00_i      = 'h0;
            uvw_i.v01_i      = 'h0;

            pw_uvw_i.u0_i    = pwm_rd_data_a_reg[REG_SIZE-2:0];
            pw_uvw_i.u1_i    = pwm_rd_data_a_reg[(2*REG_SIZE)-2:REG_SIZE];
            pw_uvw_i.u2_i    = pwm_rd_data_a_reg[(3*REG_SIZE)-2:(2*REG_SIZE)];
            pw_uvw_i.u3_i    = pwm_rd_data_a_reg[(4*REG_SIZE)-2:(3*REG_SIZE)];

            pw_uvw_i.v0_i    = pwm_rd_data_b/*_reg*/[REG_SIZE-2:0];
            pw_uvw_i.v1_i    = pwm_rd_data_b/*_reg*/[(2*REG_SIZE)-2:REG_SIZE];
            pw_uvw_i.v2_i    = pwm_rd_data_b/*_reg*/[(3*REG_SIZE)-2:(2*REG_SIZE)];
            pw_uvw_i.v3_i    = pwm_rd_data_b/*_reg*/[(4*REG_SIZE)-2:(3*REG_SIZE)];

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

            pw_uvw_i.v0_i    = pwm_rd_data_b/*_reg*/[REG_SIZE-2:0];
            pw_uvw_i.v1_i    = pwm_rd_data_b/*_reg*/[(2*REG_SIZE)-2:REG_SIZE];
            pw_uvw_i.v2_i    = pwm_rd_data_b/*_reg*/[(3*REG_SIZE)-2:(2*REG_SIZE)];
            pw_uvw_i.v3_i    = pwm_rd_data_b/*_reg*/[(4*REG_SIZE)-2:(3*REG_SIZE)];

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

            pw_uvw_i.u0_i    = 'h0;
            pw_uvw_i.u1_i    = 'h0;
            pw_uvw_i.u2_i    = 'h0;
            pw_uvw_i.u3_i    = 'h0;

            pw_uvw_i.v0_i    = 'h0;
            pw_uvw_i.v1_i    = 'h0;
            pw_uvw_i.v2_i    = 'h0;
            pw_uvw_i.v3_i    = 'h0;

            pw_uvw_i.w0_i    = 'h0;
            pw_uvw_i.w1_i    = 'h0;
            pw_uvw_i.w2_i    = 'h0;
            pw_uvw_i.w3_i    = 'h0;
        end
        endcase
    end
    assign bf_enable_mux    = ct_mode ? bf_enable       : bf_enable_reg;
    assign mem_wren_mux     = mem_wren; //ct_mode ? mem_wren_reg    : mem_wren;
    assign mem_wr_addr_mux  = mem_wr_addr; //ct_mode ? mem_wr_addr_reg : mem_wr_addr;

    /*
    ntt_buffer #(
        .REG_SIZE(REG_SIZE)
    ) buffer_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .wren(buf_wren), //TODO: review for high-perf mode
        .rden(buf_rden),
        .wr_rst_count(buf_wr_rst_count),
        .rd_rst_count(buf_rd_rst_count),
        .mode(mode),
        .data_i(buf_data_i),
        .buf0_valid(buf0_valid),
        .data_o(buf_data_o)
    );
    */

    ntt_shuffle_buffer #(
        .REG_SIZE(REG_SIZE)
    ) buffer_inst0 (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .mode(mode),
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
