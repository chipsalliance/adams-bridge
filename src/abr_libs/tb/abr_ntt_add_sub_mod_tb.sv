// SPDX-License-Identifier: Apache-2.0
//
// Testbench for add_sub_mod with REG_SIZE=23, MLKEM_REG_SIZE=12
//

`timescale 1ns/1ps

module abr_ntt_add_sub_mod_tb;

    // Parameters
    parameter REG_SIZE = 23;
    parameter MLKEM_REG_SIZE = 12;

    // DUT signals
    logic clk;
    logic reset_n;
    logic zeroize;
    logic add_en_i;
    logic sub_i;
    logic [REG_SIZE-1:0] opa_i, opb_i, prime_i;
    logic mlkem;
    logic [REG_SIZE-1:0] res_o;
    logic ready_o;

    // Instantiate DUT
    abr_ntt_add_sub_mod #(
        .REG_SIZE(REG_SIZE)
    ) dut (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .add_en_i(add_en_i),
        .sub_i(sub_i),
        .opa_i(opa_i),
        .opb_i(opb_i),
        .prime_i(prime_i),
        .mlkem(mlkem),
        .res_o(res_o),
        .ready_o(ready_o)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Helper function for modular add/sub
    function automatic [REG_SIZE-1:0] mod_add_sub(
        input [REG_SIZE-1:0] opa,
        input [REG_SIZE-1:0] opb,
        input [REG_SIZE-1:0] prime,
        input sub,
        input mlkem_mode
    );
        reg [REG_SIZE:0] tmp;
        reg [REG_SIZE-1:0] opa_m, opb_m, prime_m;
        begin
            if (mlkem_mode) begin
                opa_m   = {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, opa[MLKEM_REG_SIZE-1:0]};
                opb_m   = {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, opb[MLKEM_REG_SIZE-1:0]};
                prime_m = {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, prime[MLKEM_REG_SIZE-1:0]};
            end else begin
                opa_m   = opa;
                opb_m   = opb;
                prime_m = prime;
            end
            if (sub)
                tmp = opa_m - opb_m;
            else
                tmp = opa_m + opb_m;
            // if (tmp >= prime_m)
            //     tmp = tmp - prime_m;
            // if (tmp[REG_SIZE])
            //     tmp = tmp + prime_m;
            if (tmp[REG_SIZE])
                tmp = tmp + prime_m;
            else
                tmp = tmp % prime_m;
            mod_add_sub = tmp[REG_SIZE-1:0];
        end
    endfunction

    // Test task
    task automatic run_test(input mlkem_mode, input [REG_SIZE-1:0] prime_val);
        int errors = 0;
        int total = 0;
        int i, j, l;
        logic [REG_SIZE-1:0] opa_t, opb_t, expected;
        logic sub_t;
        logic [REG_SIZE-1:0] reg_size;

        if (mlkem_mode)
            reg_size = 12;
        else
            reg_size = 23;

        // Use small ranges for exhaustive test (full range is too large)
        for (i = 0; i < 2^reg_size; i++) begin
            for (j = 0; j < 2^reg_size; j++) begin
                for (l = 0; l < 2; l++) begin // sub_i
                    opa_t = i;
                    opb_t = j;
                    sub_t = l;
                    @(negedge clk);
                    add_en_i = 1;
                    opa_i = opa_t;
                    opb_i = opb_t;
                    prime_i = prime_val;
                    sub_i = sub_t;
                    mlkem = mlkem_mode;
                    zeroize = 0;
                    @(negedge clk);
                    add_en_i = 0;
                    // Wait for ready_o
                    wait (ready_o == 1);
                    expected = mod_add_sub(opa_t, opb_t, prime_val, sub_t, mlkem_mode);
                    if (mlkem_mode)
                        expected = {{(REG_SIZE-MLKEM_REG_SIZE){1'b0}}, expected[MLKEM_REG_SIZE-1:0]};
                    if (res_o !== expected) begin
                        $display("ERROR: mlkem=%0d opa=%0d opb=%0d prime=%0d sub=%0d => res_o=%0d expected=%0d", mlkem_mode, opa_t, opb_t, prime_val, sub_t, res_o, expected);
                        errors++;
                    end
                    total++;
                    @(negedge clk);
                end
            end
        end
        $display("Test mlkem=%0d: %0d cases, %0d errors", mlkem_mode, total, errors);
        if (errors == 0)
            $display("PASS");
        else
            $display("FAIL");
    endtask

    // Main test sequence
    initial begin
        clk = 0;
        reset_n = 0;
        zeroize = 0;
        add_en_i = 0;
        sub_i = 0;
        opa_i = 0;
        opb_i = 0;
        prime_i = 1;
        mlkem = 0;
        @(negedge clk);
        reset_n = 1;
        @(negedge clk);

        // Test MLDSA mode (mlkem=0, prime=8380417)
        run_test(0, 23'd8380417);

        // Test MLKEM mode (mlkem=1, prime=3329)
        run_test(1, 23'd3329);

        $display("All tests completed.");
        $finish;
    end

endmodule