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

module abr_1r1w_be_ram #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter STROBE_WIDTH = 8
    ,localparam ADDR_WIDTH = $clog2(DEPTH)
    )
    (
    input  logic                           clk_i,

    input  logic                           we_i,
    input  logic [(DATA_WIDTH/STROBE_WIDTH)-1:0]      wstrobe_i,
    input  logic [ADDR_WIDTH-1:0]          waddr_i,
    input  logic [(DATA_WIDTH/STROBE_WIDTH)-1:0][STROBE_WIDTH-1:0] wdata_i,
    input  logic                           re_i,
    input  logic [ADDR_WIDTH-1:0]          raddr_i,
    output logic [DATA_WIDTH-1:0]          rdata_o
    );

`ifdef RV_FPGA_OPTIMIZE


    logic [DATA_WIDTH-1:0] flattened_wdata;

    // Create a flattened version of the wdata_i using always_comb
    always_comb begin
        flattened_wdata = '0;  // Initialize to zero
        for (int i = 0; i < (DATA_WIDTH/STROBE_WIDTH); i++) begin
            flattened_wdata[i*STROBE_WIDTH +: STROBE_WIDTH] = wdata_i[i];
        end
    end

    // Instantiation of the dual-port byte-write RAM
    bytewrite_tdp_ram_rf #(
        .NUM_COL(DATA_WIDTH / STROBE_WIDTH),   // Number of columns (bytes)
        .COL_WIDTH(STROBE_WIDTH),              // Width of each column (byte width)
        .ADDR_WIDTH(ADDR_WIDTH),               // Address width
        .DATA_WIDTH(DATA_WIDTH),                // Data width (total)
        .DEPTH(DEPTH)
    ) bytewrite_ram_inst (
        .clkA(clk_i),                          // Clock for Port A (write)
        .enaA(we_i),                           // Enable for Port A (write enable)
        .weA(wstrobe_i),                       // Byte-wise write enable for Port A
        .addrA(waddr_i),                       // Address for Port A (write)
        .dinA(flattened_wdata),                // Data input for Port A (flattened)
        .doutA(),                              // Data output for Port A (unused in write-only)

        .clkB(clk_i),                          // Clock for Port B (read)
        .enaB(re_i),                           // Enable for Port B (read enable)
        .weB({(DATA_WIDTH/STROBE_WIDTH){1'b0}}),                         // No write enable for Port B
        .addrB(raddr_i),                       // Address for Port B (read)
        .dinB({DATA_WIDTH{1'b0}}),             // No data input for Port B
        .doutB(rdata_o)                        // Data output for Port B (read data)
    );

`else

    //storage element
   logic [(DATA_WIDTH/STROBE_WIDTH)-1:0][STROBE_WIDTH-1:0] ram [DEPTH-1:0];

    always @(posedge clk_i) begin
        if (we_i) begin
            for (int i = 0; i < (DATA_WIDTH/STROBE_WIDTH); i++) begin
                if (wstrobe_i[i])
                    ram[waddr_i][i] <= wdata_i[i];
            end
        end
    end

    always @(posedge clk_i) begin
        if (re_i) begin
            rdata_o <= ram[raddr_i];
        end
    end


`endif


endmodule

`ifdef RV_FPGA_OPTIMIZE

module bytewrite_tdp_ram_rf #(
    parameter NUM_COL   = 4,    // Number of columns (bytes)
    parameter COL_WIDTH = 8,    // Width of each column (byte)
    parameter ADDR_WIDTH = 10,  // Address width
    parameter DATA_WIDTH = NUM_COL * COL_WIDTH,  // Data width (total)
    parameter DEPTH = 64
) (
    input  wire                      clkA,     // Clock for Port A
    input  wire                      enaA,     // Enable for Port A
    input  wire [NUM_COL-1:0]        weA,      // Write enable for Port A (byte-wise)
    input  wire [ADDR_WIDTH-1:0]     addrA,    // Address for Port A
    input  wire [DATA_WIDTH-1:0]     dinA,     // Data input for Port A
    output reg  [DATA_WIDTH-1:0]     doutA,    // Data output for Port A

    input  wire                      clkB,     // Clock for Port B
    input  wire                      enaB,     // Enable for Port B
    input  wire [NUM_COL-1:0]        weB,      // Write enable for Port B (byte-wise)
    input  wire [ADDR_WIDTH-1:0]     addrB,    // Address for Port B
    input  wire [DATA_WIDTH-1:0]     dinB,     // Data input for Port B
    output reg  [DATA_WIDTH-1:0]     doutB     // Data output for Port B
);

    // Core memory storage (True Dual Port)
     (* ram_style = "block" *) reg [DATA_WIDTH-1:0] ram_block [DEPTH-1:0];  // Memory array

    integer i;

    // Port A Operations
    always @(posedge clkA) begin
        if (enaA) begin
            for (i = 0; i < NUM_COL; i = i + 1) begin
                if (weA[i]) begin
                    ram_block[addrA][i*COL_WIDTH +: COL_WIDTH] <= dinA[i*COL_WIDTH +: COL_WIDTH];  // Write byte
                end
            end
            doutA <= ram_block[addrA];  // Read operation (read-first)
        end
    end

    // Port B Operations
    always @(posedge clkB) begin
        if (enaB) begin
            for (i = 0; i < NUM_COL; i = i + 1) begin
                if (weB[i]) begin
                    ram_block[addrB][i*COL_WIDTH +: COL_WIDTH] <= dinB[i*COL_WIDTH +: COL_WIDTH];  // Write byte
                end
            end
            doutB <= ram_block[addrB];  // Read operation (read-first)
        end
    end

endmodule

`endif
