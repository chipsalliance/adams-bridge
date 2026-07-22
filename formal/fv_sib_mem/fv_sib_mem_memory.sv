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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------

module fv_sib_mem_memory #(
    parameter int                   DEPTH           = 64           ,
    parameter int                   NUM_PORTS       = 1            ,
    parameter int                   DATA_WIDTH      = 32           ,
    parameter int                   MEM_LATENCY     = 1            ,
    parameter int                   ADDR_WIDTH      = $clog2(DEPTH),
    parameter int                   ASSERT_INPUTS   = 0            ,
    parameter int                   RD_WR_SYM_ADDR  = 0            ,
    parameter int                   RD_BEFORE_WRITE = 0            ,
    parameter int                   ENABLE_COVERS   = 0            ,
    parameter logic[DATA_WIDTH-1:0] INITIAL_VALUE   = 0

)
(
    input logic                                 clk          ,
    input logic                                 rst_n        ,
    input logic [NUM_PORTS-1:0]                 write_enable ,
    input logic [NUM_PORTS-1:0][ADDR_WIDTH-1:0] write_address,
    input logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] write_data   ,
    input logic [NUM_PORTS-1:0]                 read_enable  ,
    input logic [NUM_PORTS-1:0][ADDR_WIDTH-1:0] read_address ,
    input logic [NUM_PORTS-1:0][DATA_WIDTH-1:0] read_data
);

    default clocking default_clk @(posedge clk); endclocking

    localparam NUM_PORTS_WIDTH = (NUM_PORTS == 1 ? 1 : $clog2(NUM_PORTS));

    function static logic multi_write_sym_addr;
        input [NUM_PORTS-1:0]                 write_enable;
        input [NUM_PORTS-1:0][ADDR_WIDTH-1:0] address;
        input [ADDR_WIDTH-1:0]                sym_addr;

        for(int port1 = 0; port1 < NUM_PORTS; port1++) begin
            if (address[port1] == sym_addr && write_enable[port1]) begin
                for (int port2 = port1 + 1; port2 < NUM_PORTS; port2++) begin
                    if (address[port2] == sym_addr && write_enable[port2]) begin
                        return 1'b1;
                    end
                end
                return 1'b0;
            end
        end
        return 1'b0;
    endfunction

    function static logic sym_address_match;
        input [NUM_PORTS-1:0]                 enable;
        input [ADDR_WIDTH-1:0]                sym_addr;
        input [NUM_PORTS-1:0][ADDR_WIDTH-1:0] address;

        for(int port = 0; port < NUM_PORTS; port++) begin
            if (enable[port] && address[port] == sym_addr) begin
                return 1'b1;
            end
        end
        return 1'b0;
    endfunction

    function static logic [NUM_PORTS_WIDTH-1:0] find_sym_addr_port;
        input [NUM_PORTS-1:0]                 enable;
        input [ADDR_WIDTH-1:0]                sym_addr;
        input [NUM_PORTS-1:0][ADDR_WIDTH-1:0] address;

        for(int port = 0; port < NUM_PORTS; port++) begin
            if (enable[port] && address[port] == sym_addr) begin
                return port;
            end
        end
        return '0;
    endfunction

    logic                       sym_addr_rd_request;
    logic                       sym_addr_wr_request;
    logic                       sym_addr_written_reg;
    logic [DATA_WIDTH-1:0]      sym_data;
    logic [ADDR_WIDTH-1:0]      sym_addr;
    logic [NUM_PORTS_WIDTH-1:0] sym_port;
    logic [NUM_PORTS_WIDTH-1:0] sym_addr_read_port;
    logic [NUM_PORTS_WIDTH-1:0] sym_addr_write_port;

    assume_stable_sym_data      : assume property (##1 $stable(sym_data));
    assume_stable_sym_addr      : assume property (##1 $stable(sym_addr));
    assume_stable_sym_port      : assume property (##1 $stable(sym_port));
    assume_sym_port_lt_num_ports: assume property (sym_port < NUM_PORTS);

    assign sym_addr_rd_request = sym_address_match(read_enable, sym_addr, read_address);
    assign sym_addr_wr_request = sym_address_match(write_enable, sym_addr, write_address);

    assign sym_addr_read_port  = find_sym_addr_port(read_enable, sym_addr, read_address);
    assign sym_addr_write_port = find_sym_addr_port(write_enable, sym_addr, write_address);

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            sym_addr_written_reg <= 1'b0;
        end
        else begin
            if (sym_addr_wr_request) begin
                sym_addr_written_reg <= 1'b1;
            end
        end
    end

    // An address must not be read before it has been written.
    property no_rd_if_no_wr;
        disable iff(!rst_n)
        !sym_addr_written_reg
    |->
        !sym_addr_rd_request
    ;endproperty

    // There must not be a read and a write to the same address
    // in the same clock cycle.
    property no_rd_wr_sym_addr;
        disable iff(!rst_n)
        |read_enable || |write_enable
    |->
        !(sym_addr_rd_request && sym_addr_wr_request)
    ;endproperty

    // There must not be writes to the same address from different ports.
    property no_multi_write_to_sym_addr;
        disable iff(!rst_n)
        |write_enable
    |->
        !(multi_write_sym_addr(write_enable, write_address, sym_addr))
    ;endproperty

    // If an address is written and it is not written again, the next
    // time we read this address, the data must be the same as the one
    // that was initially written.
    assert_sym_addr_mem_data_integrity: assert property (disable iff(!rst_n)
        ##0 (sym_addr_wr_request && write_data[sym_addr_write_port] == sym_data)
        ##1 !sym_addr_wr_request[*1:$]
        ##1 read_enable[sym_port] && read_address[sym_port] == sym_addr
    |->
        ##MEM_LATENCY
        read_data[sym_port] == sym_data
    );

    // If there is a read before write, then the memory should contain the initial value set
    // This assertion would fill the gap from reset if there is no write to the 
    // symbolic addr and there is a read req from any of the ports or both then
    // the data returned should be INITIAL VALUE.
    if(RD_BEFORE_WRITE) begin: gen_rd_before_write
        assert_rd_before_wr_intitials: assert property(disable iff(!rst_n)
           (read_enable[sym_port] && read_address[sym_port] == sym_addr) && !sym_addr_written_reg
        |->
            ##MEM_LATENCY
            read_data[sym_port] == INITIAL_VALUE
        );
    end

    if (ASSERT_INPUTS) begin: gen_assert_inputs
        assert_no_multi_write_to_sym_addr: assert property (no_multi_write_to_sym_addr);

        if (!RD_WR_SYM_ADDR) begin: gen_no_rd_wr
            assert_no_rd_wr_sym_addr: assert property (no_rd_wr_sym_addr);
        end

        if (!RD_BEFORE_WRITE) begin: gen_no_rd_before_wr
            assert_no_rd_if_no_wr: assert property (no_rd_if_no_wr);
        end
    end
    else begin: gen_assume_inputs
        assume_no_multi_write_to_sym_addr: assume property (no_multi_write_to_sym_addr);

        if (!RD_WR_SYM_ADDR) begin: gen_no_multi_port_same_addr
            assume_no_rd_wr_sym_addr: assume property (no_rd_wr_sym_addr);
        end

        if (!RD_BEFORE_WRITE) begin: gen_no_rd_before_wr
            assume_no_rd_if_no_wr: assume property (no_rd_if_no_wr);
        end
    end

    if (ENABLE_COVERS) begin: gen_covers
        cover_rd_wr_sym_addr: cover property (disable iff(!rst_n)
            ##0 (sym_addr_wr_request && write_data[sym_addr_write_port] == sym_data)
            ##1 !sym_addr_wr_request[*1:$]
            ##1 sym_addr_rd_request && sym_addr_wr_request
        );

        cover_multi_rd_sym_addr: cover property (disable iff(!rst_n)
            (sym_port < NUM_PORTS-1) &&
            (read_enable[sym_port] && read_enable[sym_port+1]) &&
            (read_address[sym_port] == sym_addr) &&
            (read_address[sym_port] == read_address[sym_port+1])
        );
    end

endmodule
