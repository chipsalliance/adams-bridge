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
// decompose_w1_mem.sv
// --------
// Stores 256-bit z components for 8 polynomials (256*8 = 2048 bits)
// z value is derived from r1 of decompose unit. z = (r1 != 0)
// Decompose unit writes to this buffer. Makehint reads from this buffer
// to calculate hint as needed.
// To align with main memory access pattern, this buffer also stores 4 bits per addr
// that represent 4 coeffs. Hence, 64 locations are needed per poly

module decompose_w1_mem #(
    parameter ADDR_WIDTH = 9, //8 poly * 64 addr per poly = 512 locations
    parameter DATA_WIDTH = 4
    )
    (      
    input  wire                      clk,
    input  wire                      reset_n,
    input  wire                      zeroize,
    
    input  wire                      rden, //read en
    input  wire                      wren, //write en
    input  wire  [ADDR_WIDTH-1 : 0]  addr,
    input  wire  [DATA_WIDTH-1 : 0]  din,
    output logic [DATA_WIDTH-1 : 0]  dout
    );
 
    // Declare the RAM variable
    localparam ADDR_LENGTH = 2**ADDR_WIDTH;
    reg [DATA_WIDTH-1:0]    mem[ADDR_LENGTH-1:0];
   

    always_ff @ (posedge clk or negedge reset_n) 
    begin : reading_memory
        if (!reset_n) begin
            dout <= '0;
        end
        else if (zeroize) begin
            dout <= '0;
        end
        else begin
            if (rden)
                dout <= mem[addr];
        end
    end // reading_memory

    always_ff @ (posedge clk or negedge reset_n) 
    begin : writing_memory
        if (!reset_n) begin
            for (int i0 = 0; i0 < ADDR_LENGTH; i0++)
                mem[i0] <= '0;
        end
        else if (zeroize) begin
            for (int i0 = 0; i0 < ADDR_LENGTH; i0++)
                mem[i0] <= '0;
        end
        else begin
            if (wren)
                mem[addr] <= din;
        end
    end // writing_memory

endmodule
