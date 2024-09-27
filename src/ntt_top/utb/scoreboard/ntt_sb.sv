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
class ntt_sb extends uvm_scoreboard;
    import mldsa_params_pkg::*;
    `uvm_component_utils(ntt_sb)

    uvm_analysis_imp_ntt_txn#(ntt_txn, ntt_sb) ntt_ap;

    uvm_analysis_imp_ntt_mem_txn#(mem_txn, ntt_sb) ntt_mem_ap;
    uvm_analysis_imp_pwm_a_mem_txn#(mem_txn, ntt_sb) pwm_a_mem_ap;
    uvm_analysis_imp_pwm_b_mem_txn#(mem_txn, ntt_sb) pwm_b_mem_ap;



    localparam MLDSA_Q = 23'd8380417;
    localparam MLDSA_N = 256;
    localparam MLDSA_LOGN = $clog2(MLDSA_N);
    localparam f= 8347681;  // 256^-1 mod MLDSA_Q

    // Memory models for the three memories
    bit [MEM_DATA_WIDTH-1:0] ntt_mem_model [0:MEM_DEPTH-1];
    bit [MEM_DATA_WIDTH-1:0] pwm_a_mem_model [0:MEM_DEPTH-1];
    bit [MEM_DATA_WIDTH-1:0] pwm_b_mem_model [0:MEM_DEPTH-1];

    bit [MEM_DATA_WIDTH-1:0] ntt_model_inputs [0:MEM_DEPTH-1];
    bit [MEM_DATA_WIDTH-1:0] pwm_a_model_inputs [0:MEM_DEPTH-1];
    bit [MEM_DATA_WIDTH-1:0] pwm_b_model_inputs [0:MEM_DEPTH-1];

    bit [REG_SIZE-1:0] One_NTT_input [0:MLDSA_N-1];
    bit [REG_SIZE-1:0] model_NTT_output [0:MLDSA_N-1];
    bit [REG_SIZE-1:0] DUT_NTT_output [0:MLDSA_N-1];

    bit [REG_SIZE-1:0] ntt_memory_for_stages[0:3][0:MLDSA_N-1];
    bit [REG_SIZE-1:0] model_stage_memory[0:3][0:MLDSA_N-1];

    //try get from each export and print the transactions
    ntt_txn     ntt_input_txn;

    mem_txn     ntt_mem_txn;
    mem_txn     pwm_a_mem_txn;
    mem_txn     pwm_b_mem_txn;

    //NTT address assignments:
    ntt_mem_addr_t ntt_mem_addrs;
    // This bit indicatres that NTT operation ha been started
    // another enable is going to be discarded until DUT asserts
    // the done signal high.
    logic       ntt_lock;
    // Presents the ntt mode selection.
    mode_t      mode;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        ntt_ap = new("ntt_ap", this);
        ntt_mem_ap = new("ntt_mem_ap", this);
        pwm_a_mem_ap = new("pwm_a_mem_ap", this);
        pwm_b_mem_ap = new("pwm_b_mem_ap", this);
        ntt_lock = 1'b0;
    endfunction: new

    function void build_phase(uvm_phase phase);
       super.build_phase(phase);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
       super.connect_phase(phase);
    endfunction: connect_phase

    virtual function void write_ntt_txn(ntt_txn txn);
        ntt_input_txn = txn;
        if (ntt_input_txn.ntt_enable == 1'b1 &&
                (ntt_input_txn.mode == mode_t'(ct) || ntt_input_txn.mode == mode_t'(gs)) &&
                ntt_lock != 1'b1
                ) begin
            // NTT src, dest and iterim addresses are locked.
            ntt_mem_addrs = ntt_input_txn.ntt_mem_base_addr;
            // NTT mode is locked.
            mode = ntt_input_txn.mode;
            // NTT locked the NTT check mechanism.
            ntt_lock = 1'b1;

            if (mode == mode_t'(ct)) begin
                `uvm_info("ntt_sb", "Going to extract NTT coefficients from input vectors", UVM_LOW)
                extract_256_coeffs(ntt_model_inputs, ntt_mem_addrs.src_base_addr, -1, One_NTT_input);
                // Perform forward NTT
                `uvm_info("ntt_sb", "Performing forward NTT with model input", UVM_LOW)
                fwd_NTT(One_NTT_input, model_NTT_output);
                fwd_2x2_NTT(One_NTT_input, model_stage_memory);
            end
            else begin
                `uvm_info("ntt_sb", "Going to extract INTT coefficients from input vectors", UVM_LOW)
                extract_256_coeffs(ntt_model_inputs, ntt_mem_addrs.src_base_addr, -1, One_NTT_input);
                // Perform forward NTT
                `uvm_info("ntt_sb", "Performing inverse NTT with model input", UVM_LOW)
                inv_NTT(One_NTT_input, model_NTT_output);
                inv_2x2_NTT_div2(One_NTT_input, model_stage_memory);
            end
        end
        if (ntt_input_txn.stage_done == 1'b1 && ntt_lock == 1'b1) begin
            extract_DUTs_NTT_stage_outputs(ntt_input_txn.stage_idx);
        end
        if (ntt_input_txn.ntt_done == 1'b1 && ntt_lock == 1'b1) begin
            `uvm_info("ntt_sb", "Going to extract computed NTT coefficients from DUT", UVM_LOW)
            extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.dest_base_addr, 3, DUT_NTT_output);
            // Compare model and DUT outputs
            `uvm_info("ntt_sb", "Comparing model and DUT outputs", UVM_LOW)
            compare_E2E_ntt_model_outputs();
            compare_ntt_stages();
            ntt_lock = 1'b0;
        end
        
        `uvm_info("ntt_sb", $sformatf("ntt_input_txn: %s", ntt_input_txn.sprint()), UVM_MEDIUM)
    endfunction

    virtual function void write_ntt_mem_txn(mem_txn txn);
        ntt_mem_txn = txn;
        update_sb_memory_model(ntt_mem_model, ntt_model_inputs, txn);
        `uvm_info("ntt_sb", $sformatf("ntt_mem_txn: %s", ntt_mem_txn.sprint()), UVM_MEDIUM)
    endfunction

    virtual function void write_pwm_a_mem_txn(mem_txn txn);
        pwm_a_mem_txn = txn;
        update_sb_memory_model(pwm_a_mem_model, pwm_a_model_inputs, txn);
        `uvm_info("ntt_sb", $sformatf("pwm_a_mem_txn: %s", pwm_a_mem_txn.sprint()), UVM_MEDIUM)
    endfunction

    virtual function void write_pwm_b_mem_txn(mem_txn txn);
        pwm_b_mem_txn = txn;
        update_sb_memory_model(pwm_b_mem_model, pwm_b_model_inputs, txn);
        `uvm_info("ntt_sb", $sformatf("pwm_b_mem_txn: %s", pwm_b_mem_txn.sprint()), UVM_MEDIUM)
    endfunction

    task run_phase(uvm_phase phase);
        super.run_phase(phase);
    endtask

    
    // Function to update the memory model based on the received transactions
    function void update_sb_memory_model(ref bit [MEM_DATA_WIDTH-1:0] mem_from_DUT [0:MEM_DEPTH-1], 
            ref bit [MEM_DATA_WIDTH-1:0] mem_to_model [0:MEM_DEPTH-1], 
            mem_txn mem_txn_i
        );
        if (mem_txn_i.update_mem) begin
            for (int i = 0; i < MEM_DEPTH; i++) begin
                mem_from_DUT[i] = mem_txn_i.artificialMemory[i];
                mem_to_model[i] = mem_txn_i.artificialMemory[i];
            end
            `uvm_info("ntt_sb", "DRIVER UPDATED memory content contents:", UVM_LOW)
        end

        if (mem_txn_i.mem_port0_req.rd_wr_en == RW_WRITE) begin
            mem_from_DUT[mem_txn_i.mem_port0_req.addr] = mem_txn_i.p0_write_data;
        end
        if (mem_txn_i.mem_port1_req.rd_wr_en == RW_WRITE) begin
            mem_from_DUT[mem_txn_i.mem_port1_req.addr] = mem_txn_i.p1_write_data;
        end
    endfunction: update_sb_memory_model

    // Function to extract 256 coefficients from the input memory starting at src_base_addr
    function void extract_256_coeffs(
        input bit [MEM_DATA_WIDTH-1:0] input_memory [0:MEM_DEPTH-1], 
        input logic [MLDSA_MEM_ADDR_WIDTH-1:0] base_addr,
        input int stage_idx,
        output bit [REG_SIZE-1:0] NTT_coeffs [0:MLDSA_N-1]
    );
        int cnt;
        begin
            cnt = 0;
            if (stage_idx == -1 || stage_idx == 3) begin
                // Organize memory into 24-bit coefficients
                for (int i = base_addr; i < base_addr+64; i++) begin
                    NTT_coeffs[4*cnt+0] = input_memory[i][23:0];    // 1st coefficient
                    NTT_coeffs[4*cnt+1] = input_memory[i][47:24];   // 2nd coefficient
                    NTT_coeffs[4*cnt+2] = input_memory[i][71:48];   // 3rd coefficient
                    NTT_coeffs[4*cnt+3] = input_memory[i][95:72];   // 4th coefficient
                    cnt++;
                end
            end
            else if (stage_idx == 0) begin
                // Organize memory into 24-bit coefficients with offsets of 64
                for (int i = 0; i < 64; i++) begin
                    NTT_coeffs[cnt+0] = input_memory[base_addr+i][23:0];       // 1st coefficient
                    NTT_coeffs[cnt+64] = input_memory[base_addr+i][47:24];     // 65th coefficient
                    NTT_coeffs[cnt+128] = input_memory[base_addr+i][71:48];    // 129th coefficient
                    NTT_coeffs[cnt+192] = input_memory[base_addr+i][95:72];    // 193th coefficient
                    cnt++;
                end
            end
            else if (stage_idx == 1) begin
                // Organize memory into 24-bit coefficients with the described offset pattern for addr_offset == 32
                for (int base = 0; base < 16; base++) begin
                    for (int i = 0; i < 4; i++) begin
                        int index = base_addr + base*4 + i;
                        int coeff_index = base + i*64;
                        NTT_coeffs[coeff_index] = input_memory[index][23:0];    // 1st coefficient
                        NTT_coeffs[coeff_index+16] = input_memory[index][47:24]; // 2nd coefficient
                        NTT_coeffs[coeff_index+32] = input_memory[index][71:48]; // 3rd coefficient
                        NTT_coeffs[coeff_index+48] = input_memory[index][95:72]; // 4th coefficient
                    end
                end
            end
            else if (stage_idx == 2) begin
                // Organize memory into 24-bit coefficients with the described offset pattern for addr_offset == 16
                for (int i = 0; i < 4; i++) begin
                    for (int j = 0; j < 16; j++) begin
                        int index = base_addr + i * 16 + j;
                        int coeff_index = i + j * 16;
                        NTT_coeffs[coeff_index] = input_memory[index][23:0];       // 1st coefficient
                        NTT_coeffs[coeff_index+4] = input_memory[index][47:24];  // 2nd coefficient
                        NTT_coeffs[coeff_index+8] = input_memory[index][71:48];  // 3rd coefficient
                        NTT_coeffs[coeff_index+12] = input_memory[index][95:72]; // 4th coefficient
                    end
                end
            end
        end
    endfunction

    
  
    function void ct_bf(
        input logic [22:0] u,    // 23-bit input
        input logic [22:0] v,    // 23-bit input
        input logic [22:0] z,    // 23-bit input
        output logic [22:0] u_out, // 23-bit output
        output logic [22:0] v_out  // 23-bit output
        );
        logic [46:0] t; // 46-bit intermediate variable to handle multiplication
        logic [46:0] u_minus; // Temporary variable for intermediate results

        begin
            t = (v * z) % MLDSA_Q;
            
            if (u >= t) begin
                u_minus = u - t;
            end else begin
                u_minus = (u + MLDSA_Q) - t;
            end

            u_out = (u + t) % MLDSA_Q;
            v_out = u_minus % MLDSA_Q; // Ensure v_out is within the correct range
        end
    endfunction

    function void gs_bf(
        input logic [22:0] u,    // 23-bit input
        input logic [22:0] v,    // 23-bit input
        input logic [22:0] z,    // 23-bit input
        output logic [22:0] u_out, // 23-bit output
        output logic [22:0] v_out  // 23-bit output
        );
        logic [46:0] t; // 46-bit intermediate variable to handle multiplication
        logic [46:0] t_minus; // Temporary variable for intermediate results
        logic [23:0] u_temp; // Temporary variable for intermediate results
    
        begin
            t_minus = (u >= v) ? (u - v) : (u + MLDSA_Q) - v;
            t = t_minus % MLDSA_Q; // Ensure t is within the correct range
            u_temp = (u + v) % MLDSA_Q;
            u_out = u_temp % MLDSA_Q;
            t_minus = (t * z) % MLDSA_Q; // Ensure v_out is within the correct range
            v_out = t_minus % MLDSA_Q;
        end
    endfunction
    

    // Function to perform the forward NTT
    function void fwd_NTT(
        input logic [REG_SIZE-1:0] poly_r[0:MLDSA_N-1],
        output logic [REG_SIZE-1:0] r[0:MLDSA_N-1]
        );
        int k, m, start, j;
        logic [22:0] zeta;
        logic [22:0] temp_u, temp_v, u_out, v_out;

        begin
            // Initialize r with the 23-bit values from poly_r
            for (int i = 0; i < MLDSA_N; i++) begin
                r[i] = poly_r[i][22:0];
            end

            k = 0;
            m = 128;

            while (m > 0) begin
                start = 0;
                while (start < MLDSA_N) begin
                    k += 1;
                    zeta = zetas[k];
                    for (j = start; j < start + m; j++) begin
                        temp_u = r[j];
                        temp_v = r[j + m];
                        ct_bf(temp_u, temp_v, zeta, u_out, v_out);
                        r[j] = u_out;
                        r[j + m] = v_out;
                    end
                    start = start + 2 * m;
                end
                m = m >> 1;
            end
        end
    endfunction


    function void fwd_2x2_NTT(
        input logic [REG_SIZE-1:0] poly_r[0:MLDSA_N-1],
        output logic [REG_SIZE-1:0] r[0:3][0:MLDSA_N-1] // 3D array for storing intermediate stages
        );
        int k, m, start, j, stage_idx;
        logic [22:0] zeta;
        logic [22:0] temp_u, temp_v, u_out, v_out;
        logic [REG_SIZE-1:0] temp_r[0:MLDSA_N-1]; // Temporary array for computation
        
        begin
            // Initialize temp_r with the 23-bit values from poly_r
            for (int i = 0; i < MLDSA_N; i++) begin
                temp_r[i] = poly_r[i][22:0];
            end
    
            k = 0;
            m = 128;
            stage_idx = 1; // To track the stages
    
            while (m > 0) begin
                start = 0;
                while (start < MLDSA_N) begin
                    k += 1;
                    zeta = zetas[k];
                    for (j = start; j < start + m; j++) begin
                        temp_u = temp_r[j];
                        temp_v = temp_r[j + m];
                        ct_bf(temp_u, temp_v, zeta, u_out, v_out);
                        temp_r[j] = u_out;
                        temp_r[j + m] = v_out;
                    end
                    start = start + 2 * m;
                end
    
                // Save the intermediate stages after every two stages
                if (stage_idx % 2 == 0) begin
                    for (int i = 0; i < MLDSA_N; i++) begin
                        r[(stage_idx/2)-1][i] = temp_r[i];
                    end
                end
    
                m = m >> 1;
                stage_idx++;
            end
        end
    endfunction
    
    // Function to compare ntt_model_outputs with ntt_mem_model
    function void compare_E2E_ntt_model_outputs();
        bit match = 1;

        // Compare ntt_model_outputs with organized DUT memory
        for (int i = 0; i < MLDSA_N; i++) begin
            if (model_NTT_output[i] != DUT_NTT_output[i]) begin
                match = 0;
                `uvm_error("ntt_sb", $sformatf("Mismatch at index %0d: model_NTT_output[%0d] = %h, organized_DUT_mem[%0d] = %h", i, i, model_NTT_output[i], i, DUT_NTT_output[i]));
            end
        end

        if (match) begin
            `uvm_info("ntt_sb", "ntt_model_outputs match ntt_mem_model", UVM_LOW)
        end else begin
            `uvm_error("ntt_sb", "ntt_model_outputs do not match ntt_mem_model")
        end
    endfunction: compare_E2E_ntt_model_outputs

    
    // Function to compare ntt outputs at the stage level
    function void compare_ntt_stages();
        bit match = 1;
    
        // Compare ntt_model_outputs with organized DUT memory
        for (int i = 0; i < 3; i++) begin
            for (int j = 0; j < MLDSA_N; j++) begin
                if (model_stage_memory[i][j] != ntt_memory_for_stages[i][j]) begin
                    match = 0;
                    `uvm_error("ntt_sb", $sformatf("Mismatch at index %0d of stage %0d: model_NTT_output[%0d] = %h, DUT_NTT_output[%0d] = %h",
                                                j, (i+1)*2, j, model_stage_memory[i][j], j, ntt_memory_for_stages[i][j]));
                end
            end
        end
    
        if (match) begin
            `uvm_info("ntt_sb", "ntt_model_outputs match ntt_mem_model at the stage level", UVM_LOW)
        end else begin
            `uvm_error("ntt_sb", "ntt_model_outputs do not match ntt_mem_model at the stage level")
        end
    endfunction: compare_ntt_stages
    



    /**
     * @brief Extracts the DUT's NTT stage outputs and stores them in the corresponding stage memory.
     *
     * @param stage_done Indicates whether the current stage is completed.
     * @param stage_idx The index of the current stage (0 to 3).
     *
     * Depending on the stage index, this function extracts the coefficients from the NTT memory model
     * using the appropriate base address and offset. The extracted coefficients are then stored in 
     * the `ntt_memory_for_stages` array for comparison.
     */    
    function void extract_DUTs_NTT_stage_outputs(input int stage_idx);
        bit [REG_SIZE-1:0] tmp_poly [0:MLDSA_N-1];
        begin
            case (stage_idx)
                -1: begin
                    extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.src_base_addr, stage_idx, tmp_poly);
                    for (int i = 0; i < MLDSA_N; i++) begin
                        ntt_memory_for_stages[stage_idx][i] = tmp_poly[i];
                    end
                end
                0: begin
                    if (mode == mode_t'(ct)) begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.interim_base_addr, stage_idx, tmp_poly);
                    end
                    else begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.interim_base_addr, 2-stage_idx, tmp_poly);
                    end
                    for (int i = 0; i < MLDSA_N; i++) begin
                        ntt_memory_for_stages[stage_idx][i] = tmp_poly[i];
                    end
                end
                1: begin                    
                    if (mode == mode_t'(ct)) begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.dest_base_addr, stage_idx, tmp_poly);
                    end
                    else begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.dest_base_addr, 2-stage_idx, tmp_poly);
                    end
                    for (int i = 0; i < MLDSA_N; i++) begin
                        ntt_memory_for_stages[stage_idx][i] = tmp_poly[i];
                    end
                end
                2: begin                    
                    if (mode == mode_t'(ct)) begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.interim_base_addr, stage_idx, tmp_poly);
                    end
                    else begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.interim_base_addr, 2-stage_idx, tmp_poly);
                    end
                    for (int i = 0; i < MLDSA_N; i++) begin
                        ntt_memory_for_stages[stage_idx][i] = tmp_poly[i];
                    end
                end
                3: begin                    
                    if (mode == mode_t'(ct)) begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.dest_base_addr, stage_idx, tmp_poly);
                    end
                    else begin
                        extract_256_coeffs(ntt_mem_model, ntt_mem_addrs.dest_base_addr, 2-stage_idx, tmp_poly);
                    end
                    for (int i = 0; i < MLDSA_N; i++) begin
                        ntt_memory_for_stages[stage_idx][i] = tmp_poly[i];
                    end
                end
                default: begin
                    `uvm_error("ntt_sb", "Invalid stage_idx. Mldsa has only 4 stages to compare (1-4).")
                end
            endcase
        end
    endfunction: extract_DUTs_NTT_stage_outputs


    function void inv_NTT(
        input logic [REG_SIZE-1:0] poly_r[0:MLDSA_N-1],
        output logic [REG_SIZE-1:0] r[0:MLDSA_N-1]
        );
        int k, m, start, j;
        logic [22:0] zeta;
        logic [22:0] temp_u, temp_v, u_out, v_out;
        logic [46:0] temp_last;
    
        begin
            // Initialize r with the 23-bit values from poly_r
            for (int i = 0; i < MLDSA_N; i++) begin
                r[i] = poly_r[i][22:0];
            end
    
            k = MLDSA_N;
            m = 1;
    
            while (m < MLDSA_N) begin
                start = 0;
                while (start < MLDSA_N) begin
                    k -= 1;
                    zeta = zetas_inv[k];
                    for (j = start; j < start + m; j++) begin
                        temp_u = r[j];
                        temp_v = r[j + m];
                        gs_bf(temp_u, temp_v, zeta, u_out, v_out);
                        r[j] = u_out;
                        r[j + m] = v_out;
                    end
                    start = start + 2 * m;
                end
                m = m << 1;
            end
            for (int i = 0; i < MLDSA_N; i++) begin
                temp_last = (f * r[i]) % MLDSA_Q;
                r[i] =  temp_last % MLDSA_Q;
            end
        end
    endfunction
    
    function void inv_2x2_NTT(
        input logic [REG_SIZE-1:0] poly_r[0:MLDSA_N-1],
        output logic [REG_SIZE-1:0] r[0:3][0:MLDSA_N-1] // 3D array for storing intermediate stages
        );
        int k, m, start, j, stage_idx;
        logic [22:0] zeta;
        logic [22:0] temp_u, temp_v, u_out, v_out;
        logic [REG_SIZE-1:0] temp_r[0:MLDSA_N-1]; // Temporary array for computation
        
        begin
            // Initialize temp_r with the 23-bit values from poly_r
            for (int i = 0; i < MLDSA_N; i++) begin
                temp_r[i] = poly_r[i][22:0];
            end
    
            k = MLDSA_N;
            m = 1;
            stage_idx = 1; // To track the stages
    
            while (m < MLDSA_N) begin
                start = 0;
                while (start < MLDSA_N) begin
                    k -= 1;
                    zeta = zetas_inv[k];
                    for (j = start; j < start + m; j++) begin
                        temp_u = temp_r[j];
                        temp_v = temp_r[j + m];
                        gs_bf(temp_u, temp_v, zeta, u_out, v_out);
                        temp_r[j] = u_out;
                        temp_r[j + m] = v_out;
                    end
                    start = start + 2 * m;
                end
    
                // Save the intermediate stages after every two stages
                if (stage_idx % 2 == 0) begin
                    for (int i = 0; i < MLDSA_N; i++) begin
                        r[(stage_idx/2)-1][i] = temp_r[i];
                    end
                end
    
                m = m << 1;
                stage_idx++;
            end
        end
    endfunction
    
    
    function void gs_bf_div2(
        input logic [22:0] u,    // 23-bit input
        input logic [22:0] v,    // 23-bit input
        input logic [22:0] z,    // 23-bit input
        output logic [22:0] u_out, // 23-bit output
        output logic [22:0] v_out  // 23-bit output
        );
        logic [46:0] t; // 46-bit intermediate variable to handle division and addition
        logic [46:0] t_minus; // Temporary variable for intermediate results
        logic [46:0] u_temp; // Temporary variable for intermediate results
        
        begin
            // Calculate t and perform division by 2
            t_minus = (u >= v) ? (u - v) : (u + MLDSA_Q) - v;
            
            if (t_minus & 1) begin
                t = (t_minus >> 1) + ((MLDSA_Q + 1) >> 1);
            end else begin
                t = t_minus >> 1;
            end
            t = t % MLDSA_Q;
            
            // Calculate u and perform division by 2
            u_temp = (u + v) % MLDSA_Q;
            if (u_temp & 1) begin
                u_temp = (u_temp >> 1) + ((MLDSA_Q + 1) >> 1);
            end else begin
                u_temp = u_temp >> 1;
            end
            u_out = u_temp % MLDSA_Q;
    
            // Calculate v_out
            t_minus = (t * z) % MLDSA_Q;
            v_out = t_minus % MLDSA_Q;
        end
    endfunction

    
    function void inv_2x2_NTT_div2(
        input logic [REG_SIZE-1:0] poly_r[0:MLDSA_N-1],
        output logic [REG_SIZE-1:0] r[0:3][0:MLDSA_N-1] // 3D array for storing intermediate stages
        );
        int k1[0:1], k2, m, start, j, stage_idx;
        logic [22:0] zeta1[0:1], zeta2;
        logic [22:0] u00, v00, u01, v01;
        logic [22:0] u10, u11, v10, v11;
        logic [22:0] u20, u21, v20, v21;
        logic [REG_SIZE-1:0] temp_r[0:MLDSA_N-1]; // Temporary array for computation
        
        begin
            // Initialize temp_r with the 23-bit values from poly_r
            for (int i = 0; i < MLDSA_N; i++) begin
                temp_r[i] = poly_r[i][22:0];
            end
    
            m = 1;
            stage_idx = 0; // To track the stages
    
            for (int l = 0; l < 8; l += 2) begin
                m = 1 << l;
                for (int i = 0; i < MLDSA_N; i += (1 << (l + 2))) begin
                    k1[0] = ((MLDSA_N - (i >> 1)) >> l) - 1;
                    k1[1] = k1[0] - 1;
                    k2 = ((MLDSA_N - (i >> 1)) >> (l + 1)) - 1;
                    zeta1[0] = zetas_inv[k1[0]];
                    zeta1[1] = zetas_inv[k1[1]];
                    zeta2 = zetas_inv[k2];
    
                    for (j = i; j < i + m; j++) begin
                        u00 = temp_r[j];
                        v00 = temp_r[j + m];
                        u01 = temp_r[j + 2 * m];
                        v01 = temp_r[j + 3 * m];
    
                        gs_bf_div2(u00, v00, zeta1[0], u10, u11);
                        gs_bf_div2(u01, v01, zeta1[1], v10, v11);
    
                        gs_bf_div2(u10, v10, zeta2, u20, u21);
                        gs_bf_div2(u11, v11, zeta2, v20, v21);
    
                        temp_r[j] = u20;
                        temp_r[j + m] = v20;
                        temp_r[j + 2 * m] = u21;
                        temp_r[j + 3 * m] = v21;
                    end
                end
    
                // Save the intermediate stages after every two stages
                for (int i = 0; i < MLDSA_N; i++) begin
                    r[stage_idx][i] = temp_r[i];
                end
    
                stage_idx++;
            end
        end
    endfunction


endclass: ntt_sb