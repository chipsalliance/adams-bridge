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
// ntt_top_tb_new.sv
// --------
//======================================================================

`default_nettype none

module ntt_top_tb_new
    import ntt_defines_pkg::*;
    import abr_params_pkg::*;
();

parameter CLK_HALF_PERIOD = 5; // 100 MHz clock
parameter CLK_PERIOD = 2 * CLK_HALF_PERIOD;
parameter MLDSA_WIDTH = MLDSA_Q_WIDTH-1;
parameter MLKEM_WIDTH = MLKEM_Q_WIDTH;

reg           clk_tb;
reg           reset_n_tb;
reg           zeroize_tb;
mode_t       mode_tb;
logic         enable_tb;
logic         mlkem_tb;
logic         shuffle_en_tb;
logic [5:0] random_tb;
logic masking_en_tb;
ntt_mem_addr_t ntt_mem_base_addr_tb;
pwo_mem_addr_t pwo_mem_base_addr_tb;
logic acc_tb;
logic svalid_tb;
logic sampler_mode_tb;
logic [95:0] sampler_data_tb;
logic ntt_done_tb;
logic load_tb_values_tb;
logic load_random_values_tb;
logic load_pwm_a_values_tb;
logic load_pwm_b_values_tb;
logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] sampler_data;
logic [11:0] kyber_zeta_tb [127 : 0];


ntt_wrapper dut (
    .clk(clk_tb),
    .reset_n(reset_n_tb),
    .zeroize(zeroize_tb),
    .mode(mode_tb),
    .ntt_enable(enable_tb),
    .mlkem(mlkem_tb),
    .load_tb_values(load_tb_values_tb),
    .load_random_values(load_random_values_tb),
    .load_pwm_a_values(load_pwm_a_values_tb),
    .load_pwm_b_values(load_pwm_b_values_tb),
    // .load_tb_addr(),
    .shuffle_en(shuffle_en_tb),
    .random(random_tb),
    .masking_en(masking_en_tb),
    .rnd_i(230'h0),
    .ntt_mem_base_addr(ntt_mem_base_addr_tb),
    .pwo_mem_base_addr(pwo_mem_base_addr_tb),
    .accumulate(acc_tb),
    .sampler_valid(svalid_tb),
    .sampler_mode(sampler_mode_tb),
    .sampler_data(sampler_data_tb),
    .ntt_done(ntt_done_tb),
    .ntt_busy()
);

//----------------------------------------------------------------
// clk_gen
//
// Always running clock generator process.
//----------------------------------------------------------------
always
begin : clk_gen
  #CLK_HALF_PERIOD;
  clk_tb = !clk_tb;
end // clk_gen


//----------------------------------------------------------------
// reset_dut()
//
// Toggle reset to put the DUT into a well known state.
//----------------------------------------------------------------
task reset_dut;
    begin
      $display("*** Toggle reset.");
      reset_n_tb = 0;
    
      #(2 * CLK_PERIOD);
      reset_n_tb = 1;
    
      $display("End of reset");
    end
endtask // reset_dut

//----------------------------------------------------------------
// init_sim()
//
// Initialize all counters and testbed functionality as well
// as setting the DUT inputs to defined values.
//----------------------------------------------------------------
task init_sim;
    int i;
    begin
        $display("Start of init\n");
        clk_tb = 0;
        reset_n_tb = 0;
        zeroize_tb = 0;

        mode_tb = ct;
        enable_tb = 0;
        mlkem_tb = 0;
        shuffle_en_tb = 0;
        random_tb = 0;
        masking_en_tb = 0;
        ntt_mem_base_addr_tb = '0;
        pwo_mem_base_addr_tb = '0;

        acc_tb = 0;
        svalid_tb = 0;
        sampler_mode_tb = 0;
        sampler_data_tb = '0;

        load_tb_values_tb = 0;
        load_random_values_tb = 0;
        load_pwm_a_values_tb = 0;
        load_pwm_b_values_tb = 0;
    end
endtask

//----------------------------------------------------------------
task init_mem_with_coeffs (input logic mlkem);
    begin
        $display("Initializing memory with coefficients\n");
        mlkem_tb = mlkem;
        load_random_values_tb = 1;
        repeat(64) @(posedge clk_tb);
        load_random_values_tb = 0;

        load_pwm_a_values_tb = 1;
        repeat(64) @(posedge clk_tb);
        load_pwm_a_values_tb = 0;

        load_pwm_b_values_tb = 1;
        repeat(64) @(posedge clk_tb);
        load_pwm_b_values_tb = 0;
    end
endtask

task init_por_coeffs;
    begin
        $display("Initializing POR coefficients\n");
        load_tb_values_tb = 1;
        repeat(64) @(posedge clk_tb);
        load_tb_values_tb = 0;
    end
endtask
//----------------------------------------------------------------
task ct_test(input logic mlkem, input logic shuf_en);
    begin
        $display("CT test with mlkem = %0d, shuf_en=%0d", mlkem, shuf_en);
        fork
            begin
                while(1) begin
                    random_tb <= $urandom();
                    @(posedge clk_tb);
                end
            end
            begin
                mode_tb = ct;
                enable_tb = 1;
                mlkem_tb = mlkem;
                shuffle_en_tb = shuf_en;
                masking_en_tb = 0;
                ntt_mem_base_addr_tb = {14'h0, 14'h40, 14'h80};
                pwo_mem_base_addr_tb = '0;

                acc_tb = 0;
                svalid_tb = 1;
                sampler_mode_tb = 0;
                sampler_data_tb = '0;

                @(posedge clk_tb);
                enable_tb = 0;

                $display("Waiting for ntt_done");
                while(!ntt_done_tb)
                    @(posedge clk_tb);
                $display("ntt_done received\n");
            end
        join_any
    end
endtask
//----------------------------------------------------------------
task gs_test(input logic mlkem, input logic shuf_en, input logic mask_en);
    int err_ctr = 0; 
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] expected_data;
    begin
        $display("GS test with mlkem = %0d, shuf_en=%0d, mask_en=%0d", mlkem, shuf_en, mask_en);
        fork
            begin
                while(1) begin
                    random_tb <= $urandom();
                    @(posedge clk_tb);
                end
            end
            begin
                mode_tb = gs;
                enable_tb = 1;
                mlkem_tb = mlkem;
                shuffle_en_tb = shuf_en;
                masking_en_tb = mask_en;
                ntt_mem_base_addr_tb = {14'h80, 14'h40, 14'h80};
                pwo_mem_base_addr_tb = '0;

                acc_tb = 0;
                svalid_tb = 1;
                sampler_mode_tb = 0;
                sampler_data_tb = '0;

                @(posedge clk_tb);
                enable_tb = 0;

                $display("Waiting for ntt_done");
                while(!ntt_done_tb)
                    @(posedge clk_tb);
                $display("ntt_done received");
            end
        join_any

        for (int i = 0; i < 256; i+=4) begin
            if (!mlkem)
                expected_data = ABR_MEM_MASKED_DATA_WIDTH'({1'b0, dut.ntt_mem.mem[i/4][94:72], 1'b0, dut.ntt_mem.mem[i/4][70:48], 1'b0, dut.ntt_mem.mem[i/4][46:24], 1'b0, dut.ntt_mem.mem[i/4][22:0]});
            else
                expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(dut.ntt_mem.mem[i/4][83:72]), 24'(dut.ntt_mem.mem[i/4][59:48]), 24'(dut.ntt_mem.mem[i/4][35:24]), 24'(dut.ntt_mem.mem[i/4][11:0])});

            if (dut.ntt_mem.mem[128+(i/4)] != expected_data) begin //ABR_MEM_MASKED_DATA_WIDTH'({24'(i+3), 24'(i+2), 24'(i+1), 24'(i)})) begin
                $display("Mismatch at index %0d: expected %h, got %h", i, /*{24'(i+3), 24'(i+2), 24'(i+1), 24'(i)}*/expected_data, dut.ntt_mem.mem[128+(i/4)]);
                err_ctr++;
            end
        end
        if (err_ctr == 0) begin
            $display("GS test passed with no errors\n");
        end else begin
            $display("GS test failed with %0d errors\n", err_ctr);
        end
        err_ctr = 0;
    end
endtask
//----------------------------------------------------------------
task pwa_pws_test(input logic mlkem, input logic shuf_en, input logic pwa_mode);
    int err_ctr = 0; 
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] expected_data;
    int Q = mlkem ? MLKEM_Q : MLDSA_Q;
    int WIDTH = mlkem ? MLKEM_Q_WIDTH : MLDSA_Q_WIDTH;
    begin
        $display("PWA/PWS test with mlkem = %0d, shuf_en=%0d, pwa_mode=%0d", mlkem, shuf_en, pwa_mode);
        fork
            begin
                while(1) begin
                    random_tb <= $urandom();
                    @(posedge clk_tb);
                end
            end
            begin
                mode_tb = pwa_mode ? pwa : pws;
                enable_tb = 1;
                mlkem_tb = mlkem;
                shuffle_en_tb = shuf_en;
                masking_en_tb = 0;
                ntt_mem_base_addr_tb = '0;
                pwo_mem_base_addr_tb = {14'h0, 14'h0, 14'h80};

                acc_tb = 0;
                svalid_tb = 1;
                sampler_mode_tb = 0;
                sampler_data_tb = '0;

                @(posedge clk_tb);
                enable_tb = 0;

                $display("Waiting for ntt_done");
                while(!ntt_done_tb)
                    @(posedge clk_tb);
                $display("ntt_done received");
            end
        join_any

        $display("pwa mode = %h", pwa_mode);
        for (int i = 0; i < 256; i+=4) begin
            //expected_data = pwa_mode ? ABR_MEM_MASKED_DATA_WIDTH'({24'((i+3) + (i+3)), 24'((i+2) + (i+2)), 24'((i+1) + (i+1)), 24'(i+i)})
             //                           : ABR_MEM_MASKED_DATA_WIDTH'({24'((i+3) - (i+3)), 24'((i+2) - (i+2)), 24'((i+1) - (i+1)), 24'(i-i)});

            if (mlkem) begin
                expected_data = pwa_mode ? ABR_MEM_MASKED_DATA_WIDTH'({24'((2*dut.pwm_mem_a.mem[i/4][83:72]) % MLKEM_Q), 24'((2*dut.pwm_mem_a.mem[i/4][59:48]) % MLKEM_Q), 24'((2*dut.pwm_mem_a.mem[i/4][35:24]) % MLKEM_Q), 24'((2*dut.pwm_mem_a.mem[i/4][11:0]) % MLKEM_Q)})
                                     : '0;
            end
            else begin
                expected_data = pwa_mode ? ABR_MEM_MASKED_DATA_WIDTH'({24'((2*dut.pwm_mem_a.mem[i/4][94:72]) % MLDSA_Q), 24'((2*dut.pwm_mem_a.mem[i/4][70:48]) % MLDSA_Q), 24'((2*dut.pwm_mem_a.mem[i/4][46:24]) % MLDSA_Q), 24'((2*dut.pwm_mem_a.mem[i/4][22:0]) % MLDSA_Q)})
                                     : '0; //ABR_MEM_MASKED_DATA_WIDTH'({24'(), 24'(), 24'(), 24'()});
            end
            if (dut.ntt_mem.mem[128+(i/4)] != expected_data) begin
                $display("Mismatch at index %0d: expected %h, got %h", i, expected_data, dut.ntt_mem.mem[128+(i/4)]);
                err_ctr++;
            end
        end
        if (err_ctr == 0) begin
            $display("PWA/PWS test passed with no errors\n");
        end else begin
            $display("PWA/PWS test failed with %0d errors\n", err_ctr);
        end
        err_ctr = 0;
    end
endtask
//----------------------------------------------------------------
task pwm_test(input logic mlkem, input logic acc_en, input logic sampler, input logic shuf_en, input logic mask_en);
    logic [ABR_MEM_MASKED_DATA_WIDTH-1:0] expected_data;
    int err_ctr = 0;
    bit svalid;
    int svalid_ctr = 0;
    begin
        if (sampler & shuf_en) begin
            $error("PWM test with sampler_mode=1 and shuf_en=1 is not supported. Skipping this configuration.");
            return;
        end

        if (mask_en & ~shuf_en) begin
            $error("PWM test with mask_en=1 and shuf_en=0 is not supported. Skipping this configuration.");
            return;
        end

        $display("PWM test with mlkem = %0d, shuf_en=%0d, mask_en=%0d, acc_en = %0d, sampler_mode = %0d", mlkem, shuf_en, mask_en, acc_en, sampler);

        if (mlkem) begin
            $display("Loading Kyber zeta values...");
            $readmemh("mlkem_pairwm_zeta.hex", kyber_zeta_tb);
        end
        
        fork
            begin
                while(1) begin
                    random_tb <= $urandom();
                    svalid = $urandom() % 2;
                    @(posedge clk_tb);
                end
            end
            begin
                mode_tb = mlkem ? pairwm : pwm;
                mlkem_tb = mlkem;
                enable_tb = 1;
                shuffle_en_tb = shuf_en;
                masking_en_tb = mask_en;
                ntt_mem_base_addr_tb = '0;
                pwo_mem_base_addr_tb = {14'h0, 14'h0, 14'h80};

                acc_tb = acc_en;
                sampler_mode_tb = sampler;
                if (sampler) begin
                    while (svalid_ctr <= 64) begin
                        svalid_tb = svalid;
                        if (svalid) begin
                            sampler_data_tb = sampler_data; //{24'(svalid_ctr*4+3), 24'(svalid_ctr*4+2), 24'(svalid_ctr*4+1), 24'(svalid_ctr*4)};
                            $display("Driving sampler data at count %0d", svalid_ctr);
                            svalid_ctr++;
                        end
                        @(posedge clk_tb);
                    end
                    svalid_tb = 0;
                end else begin
                    svalid_tb = 1;
                    sampler_data_tb = '0;
                end
                // svalid_tb = 1;
                
                // sampler_data_tb = '0;

                @(posedge clk_tb);
                enable_tb = 0;

                $display("Waiting for ntt_done");
                while(!ntt_done_tb)
                    @(posedge clk_tb);
                $display("ntt_done received");
            end
        join_any

        

        for (int i = 0; i < 256; i+=4) begin
            if (sampler) begin
                if (!acc_en) begin
                    if (mlkem)
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'((((24'((sampler_data[83:72])*(dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q) % MLKEM_Q) + ((24'((dut.pwm_mem_a.mem[i/4][83:72])*sampler_data[59:48]) % MLKEM_Q) % MLKEM_Q)) % MLKEM_Q),
                                                                    24'(((36'((dut.pwm_mem_a.mem[i/4][83:72]) * (sampler_data[83:72]) * (kyber_zeta_tb[(i/2)+1])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][59:48]*sampler_data[59:48])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'((((24'((sampler_data[35:24])*dut.pwm_mem_a.mem[i/4][11:0]) % MLKEM_Q) % MLKEM_Q) + ((24'((dut.pwm_mem_a.mem[i/4][35:24])*sampler_data[11:0]) % MLKEM_Q) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(((36'((dut.pwm_mem_a.mem[i/4][35:24]) * (sampler_data[35:24]) * (kyber_zeta_tb[i/2])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][11:0]*sampler_data[11:0])) % MLKEM_Q)) % MLKEM_Q) 
                                                                });
                    else begin
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'((46'(dut.pwm_mem_a.mem[i/4][94:72]*sampler_data[94:72])) % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][70:48]*sampler_data[70:48])) % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][46:24]*sampler_data[46:24])) % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][22:0]*sampler_data[22:0])) % MLDSA_Q)});
                        //$display("Debug: i=%0d, pwm_mem_a=%h, sampler_data=%h, expected_data=%h", i, dut.pwm_mem_a.mem[i/4][22:0], sampler_data[22:0], 46'(dut.pwm_mem_a.mem[i/4][22:0]*sampler_data[22:0]) % abr_params_pkg::MLDSA_Q);
                    end
                end
                else begin
                    if (mlkem)
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(2*(((24'((sampler_data[83:72])*(dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q) % MLKEM_Q) + ((24'((dut.pwm_mem_a.mem[i/4][83:72])*sampler_data[59:48]) % MLKEM_Q) % MLKEM_Q)) % MLKEM_Q),
                                                                    24'(2*((36'((dut.pwm_mem_a.mem[i/4][83:72]) * (sampler_data[83:72]) * (kyber_zeta_tb[(i/2)+1])) % MLKEM_Q) + (24'((dut.pwm_mem_a.mem[i/4][59:48]) * (sampler_data[59:48])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2*(((24'((sampler_data[35:24])*dut.pwm_mem_a.mem[i/4][11:0]) % MLKEM_Q) % MLKEM_Q) + ((24'((dut.pwm_mem_a.mem[i/4][35:24])*sampler_data[11:0]) % MLKEM_Q) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2*((36'((dut.pwm_mem_a.mem[i/4][35:24]) * (sampler_data[35:24]) * (kyber_zeta_tb[i/2])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][11:0]*sampler_data[11:0])) % MLKEM_Q)) % MLKEM_Q) 
                                                                });
                    else
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'((46'(dut.pwm_mem_a.mem[i/4][94:72]*sampler_data[94:72]) % MLDSA_Q)*2 % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][70:48]*sampler_data[70:48]) % MLDSA_Q)*2 % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][46:24]*sampler_data[46:24]) % MLDSA_Q)*2 % MLDSA_Q), 24'((46'(dut.pwm_mem_a.mem[i/4][22:0]*sampler_data[22:0]) % MLDSA_Q)*2 % MLDSA_Q)});
                end
            end
            else begin
                if (!acc_en) begin
                    if (mlkem)
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(2 * ((24'((dut.pwm_mem_a.mem[i/4][83:72]*dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(((24'((dut.pwm_mem_a.mem[i/4][59:48]*dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q) + (36'((dut.pwm_mem_a.mem[i/4][83:72]) * (dut.pwm_mem_a.mem[i/4][83:72]) * (kyber_zeta_tb[(i/2)+1])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2 * ((24'((dut.pwm_mem_a.mem[i/4][35:24])*dut.pwm_mem_a.mem[i/4][11:0]) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'((((36'(dut.pwm_mem_a.mem[i/4][35:24]*dut.pwm_mem_a.mem[i/4][35:24]*kyber_zeta_tb[i/2])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][11:0]*dut.pwm_mem_a.mem[i/4][11:0])) % MLKEM_Q)) % MLKEM_Q) 
                                                                });
                        // $display("Debug: i=%0d, pwm_mem_a=%h, sampler_data=%h, expected_data=%h", i, dut.pwm_mem_a.mem[i/4][22:0], sampler_data[22:0], 46'(dut.pwm_mem_a.mem[i/4][22:0]*sampler_data[22:0]) % abr_params_pkg::MLDSA_Q);
                    else
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(46'(dut.pwm_mem_a.mem[i/4][94:72]*dut.pwm_mem_a.mem[i/4][94:72])%MLDSA_Q), 24'(46'(dut.pwm_mem_a.mem[i/4][70:48]*dut.pwm_mem_a.mem[i/4][70:48])%MLDSA_Q), 24'(46'(dut.pwm_mem_a.mem[i/4][46:24]*dut.pwm_mem_a.mem[i/4][46:24]) % MLDSA_Q), 24'(46'(dut.pwm_mem_a.mem[i/4][22:0]*dut.pwm_mem_a.mem[i/4][22:0]) % MLDSA_Q)});
                end
                else begin
                    if (mlkem) begin
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(2*2 * ((24'((dut.pwm_mem_a.mem[i/4][83:72])*(dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2*((24'((dut.pwm_mem_a.mem[i/4][59:48]) * (dut.pwm_mem_a.mem[i/4][59:48])) % MLKEM_Q) + (36'((dut.pwm_mem_a.mem[i/4][83:72]) * (dut.pwm_mem_a.mem[i/4][83:72]) * (kyber_zeta_tb[(i/2)+1])) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2*2 * ((24'((dut.pwm_mem_a.mem[i/4][35:24])*dut.pwm_mem_a.mem[i/4][11:0]) % MLKEM_Q)) % MLKEM_Q), 
                                                                    24'(2*((36'((dut.pwm_mem_a.mem[i/4][35:24]) * (dut.pwm_mem_a.mem[i/4][35:24]) * (kyber_zeta_tb[i/2])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][11:0]*dut.pwm_mem_a.mem[i/4][11:0])) % MLKEM_Q)) % MLKEM_Q) 
                                                                });
                        // $display("Debug: i=%0d, pwm_mem_a=%h, zeta=%h expected_data=%h", i, dut.pwm_mem_a.mem[i/4][11:0], kyber_zeta_tb[i/2], 24'(2*((36'((dut.pwm_mem_a.mem[i/4][35:24]) * (dut.pwm_mem_a.mem[i/4][35:24]) * (kyber_zeta_tb[i/2])) % MLKEM_Q) + ((24'(dut.pwm_mem_a.mem[i/4][11:0]*dut.pwm_mem_a.mem[i/4][11:0])) % MLKEM_Q)) % MLKEM_Q) );
                    end
                    else
                        expected_data = ABR_MEM_MASKED_DATA_WIDTH'({24'(((46'(dut.pwm_mem_a.mem[i/4][94:72]*dut.pwm_mem_a.mem[i/4][94:72]) % MLDSA_Q)*2) % MLDSA_Q), 24'(((46'(dut.pwm_mem_a.mem[i/4][70:48]*dut.pwm_mem_a.mem[i/4][70:48]) % MLDSA_Q )*2) % MLDSA_Q), 24'(((46'(dut.pwm_mem_a.mem[i/4][46:24]*dut.pwm_mem_a.mem[i/4][46:24])%MLDSA_Q)*2)%MLDSA_Q), 24'(((46'(dut.pwm_mem_a.mem[i/4][22:0]*dut.pwm_mem_a.mem[i/4][22:0])%MLDSA_Q)*2)%MLDSA_Q)});
                end
            end

            if ((dut.ntt_mem.mem[128+(i/4)] != expected_data)) begin
                $display("Mismatch at index %0d: expected %h, got %h, sampler data = %h", i, expected_data, dut.ntt_mem.mem[128+(i/4)], sampler_data);
                err_ctr++;
            end
        end

        if (err_ctr == 0) begin
            $display("PWM test passed with no errors\n");
        end else begin
            $display("PWM test failed with %0d errors\n", err_ctr);
        end
        err_ctr = 0;
        svalid_ctr = 0;
        svalid_tb = 0;
    end
endtask


initial begin
    init_sim();
    reset_dut();

    init_mem_with_coeffs(.mlkem(0));
    // init_por_coeffs();
    sampler_data = {$urandom(), $urandom(), $urandom()};
    
    $display("-------------------------------------\n");
    ct_test(.mlkem(0), .shuf_en(0));
    gs_test(.mlkem(0), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    ct_test(.mlkem(0), .shuf_en(1));
    gs_test(.mlkem(0), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(1), .acc_en(0), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(1), .acc_en(1), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(0), .acc_en(0), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(0), .acc_en(1), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(0), .acc_en(0), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(0), .sampler(0), .acc_en(1), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(0), .shuf_en(0), .pwa_mode(1));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(0), .shuf_en(0), .pwa_mode(0));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(0), .shuf_en(1), .pwa_mode(1));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(0), .shuf_en(1), .pwa_mode(0));
    $display("-------------------------------------\n");

    init_mem_with_coeffs(.mlkem(1));

    ct_test(.mlkem(1), .shuf_en(0));
    gs_test(.mlkem(1), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    ct_test(.mlkem(1), .shuf_en(1));
    gs_test(.mlkem(1), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(1), .sampler(0), .acc_en(0), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(1), .sampler(0), .acc_en(1), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    // pwm_test(.mlkem(1), .sampler(1), .acc_en(0), .shuf_en(0), .mask_en(0)); //TODO: fix this part
    // $display("-------------------------------------\n");
    // pwm_test(.mlkem(1), .sampler(1), .acc_en(1), .shuf_en(0), .mask_en(0));
    // $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(1), .shuf_en(0), .pwa_mode(1));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(1), .shuf_en(0), .pwa_mode(0));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(1), .shuf_en(1), .pwa_mode(1));
    $display("-------------------------------------\n");
    pwa_pws_test(.mlkem(1), .shuf_en(1), .pwa_mode(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(1), .sampler(0), .acc_en(0), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(1), .sampler(0), .acc_en(1), .shuf_en(1), .mask_en(0));
    $display("-------------------------------------\n");

    pwm_test(.mlkem(1), .sampler(1), .acc_en(0), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");
    pwm_test(.mlkem(1), .sampler(1), .acc_en(1), .shuf_en(0), .mask_en(0));
    $display("-------------------------------------\n");

    repeat(1000) @(posedge clk_tb); // Wait for some time to observe the reset behavior
    $finish;
    
end
endmodule