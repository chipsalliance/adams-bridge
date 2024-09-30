`include "config_defines.svh"
`ifndef RV_FPGA_OPTIMIZE
module abr_1r1w_ram #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    )
    (
    input  logic                       clk_i,

    input  logic                       we_i,
    input  logic [ADDR_WIDTH-1:0]      waddr_i,
    input  logic [DATA_WIDTH-1:0]      wdata_i,
    input  logic                       re_i,
    input  logic [ADDR_WIDTH-1:0]      raddr_i,
    output logic [DATA_WIDTH-1:0]      rdata_o
    );

    //storage element
    logic [DEPTH-1:0][DATA_WIDTH-1:0] ram;

    always @(posedge clk_i) begin
        if (we_i) begin
            ram[waddr_i] <= wdata_i;
        end
    end

    always @(posedge clk_i) begin
        if (re_i) begin
            rdata_o <= ram[raddr_i];
        end
    end

endmodule

`else
module abr_1r1w_ram #(
     parameter DEPTH      = 64
    ,parameter DATA_WIDTH = 32
    ,parameter ADDR_WIDTH = $clog2(DEPTH)

    )
    (
    input  logic                       clk_i,

    input  logic                       we_i,
    input  logic [ADDR_WIDTH-1:0]      waddr_i,
    input  logic [DATA_WIDTH-1:0]      wdata_i,
    input  logic                       re_i,
    input  logic [ADDR_WIDTH-1:0]      raddr_i,
    output logic [DATA_WIDTH-1:0]      rdata_o
    );

    (* ram_style = "block" *) reg [DATA_WIDTH-1:0] ram [DEPTH-1:0];
    
    always @(posedge clk_i) begin
        if (we_i) begin
            if (we_i)
                ram[waddr_i] <= wdata_i;
        end
    end
    
    always @(posedge clk_i) begin
        if (re_i)
            rdata_o <= ram[raddr_i];
    end

endmodule

`endif