`timescale 1ns/1ps

module compress_top_tb;

    // Parameters
    localparam CLK_PERIOD = 10; // Clock period in ns
    localparam ABR_MEM_ADDR_WIDTH = 16;
    localparam COEFF_PER_CLK = 4;
    localparam REG_SIZE = 16;
    localparam MLKEM_REG_SIZE = 12;

    // Testbench signals
    logic clk;
    logic reset_n;
    logic zeroize;
    logic compress_enable;
    compress_mode_t mode;
    logic [ABR_MEM_ADDR_WIDTH-1:0] src_base_addr;
    logic [ABR_MEM_ADDR_WIDTH-1:0] dest_base_addr;
    mem_if_t mem_rd_req;
    mem_if_t mem_wr_req;
    logic [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_rd_data;
    logic [COEFF_PER_CLK-1:0][REG_SIZE-1:0] mem_wr_data;
    logic compress_done;

    // DUT instantiation
    compress_top dut (
        .clk(clk),
        .reset_n(reset_n),
        .zeroize(zeroize),
        .compress_enable(compress_enable),
        .mode(mode),
        .src_base_addr(src_base_addr),
        .dest_base_addr(dest_base_addr),
        .mem_rd_req(mem_rd_req),
        .mem_wr_req(mem_wr_req),
        .mem_rd_data(mem_rd_data),
        .mem_wr_data(mem_wr_data),
        .compress_done(compress_done)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD / 2) clk = ~clk;
    end

    // Reset generation
    initial begin
        reset_n = 0;
        #20 reset_n = 1;
    end

    // Stimulus
    initial begin
        // Initialize inputs
        zeroize = 0;
        compress_enable = 0;
        mode = 0;
        src_base_addr = 16'h0000;
        dest_base_addr = 16'h1000;
        mem_rd_data = '{default: 12'h000};

        // Wait for reset
        @(posedge reset_n);

        // Test case 1: Compress with mode 0
        compress_enable = 1;
        mode = 0;
        mem_rd_data = '{12'h123, 12'h456, 12'h789, 12'hABC};
        @(posedge clk);
        compress_enable = 0;

        // Wait for compression to complete
        wait(compress_done);
        $display("Test case 1 complete. mem_wr_data = %p", mem_wr_data);

        // Test case 2: Compress with mode 1
        compress_enable = 1;
        mode = 1;
        mem_rd_data = '{12'hFFF, 12'hAAA, 12'h555, 12'h000};
        @(posedge clk);
        compress_enable = 0;

        // Wait for compression to complete
        wait(compress_done);
        $display("Test case 2 complete. mem_wr_data = %p", mem_wr_data);

        // Test case 3: Zeroize
        zeroize = 1;
        @(posedge clk);
        zeroize = 0;
        $display("Zeroize complete. mem_wr_data = %p", mem_wr_data);

        // Finish simulation
        $finish;
    end

    // Monitor
    initial begin
        $monitor("Time: %0t | compress_done: %b | mem_wr_data: %p", $time, compress_done, mem_wr_data);
    end

endmodule