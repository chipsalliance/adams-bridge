//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 07/21/2023 01:27:54 PM
// Design Name: 
// Module Name: cw305_mldsa_top
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`timescale 1ns / 1ps
`default_nettype none 
// `include "mldsa_config_defines.svh"

module cw310_mldsa_top
    #(
    parameter pBYTECNT_SIZE     = 8,
    parameter pADDR_WIDTH       = 20,
    parameter pPT_WIDTH         = 384,
    parameter pCT_WIDTH         = 384,
    parameter pKEY_WIDTH        = 384,
    parameter AHB_ADDR_WIDTH    = 32,
    parameter AHB_DATA_WIDTH    = 32
)(
    // USB Interface
    input wire                          usb_clk,        // Clock
`ifdef SS2_WRAPPER
    output wire                         usb_clk_buf,    // Clock
`endif
    inout wire [7:0]                    usb_data,       // Data for write/read
    input wire [pADDR_WIDTH-1:0]        usb_addr,       // Address
    input wire                          usb_rdn,        // !RD, low when addr valid for read
    input wire                          usb_wrn,        // !WR, low when data+addr valid for write
    input wire                          usb_cen,        // !CE, active low chip enable
    input wire                          usb_trigger,    // High when trigger requested

    // Buttons/LEDs on Board
    input wire                          j16_sel,        // DIP switch J16
    input wire                          k16_sel,      // DIP Switch L14
    input wire                          pushbutton,     // Pushbutton SW4, connected to R1, used here as reset
    output wire                         led1,           // red LED
    output wire                         led2,           // green LED
    output wire                         led3,           // blue LED

    // PLL
    input wire                          pll_clk1,       //PLL Clock Channel #1
    //input wire                        pll_clk2,       //PLL Clock Channel #2 (unused in this example)

    // 20-Pin Connector Stuff
    output wire                         tio_trigger,
    output wire                         tio_clkout,
    input  wire                         tio_clkin

    );

     //================== TRIGGERS =======================
  
    wire NTT_trigger;
    wire PWM_trigger;
    wire PWA_trigger;
    wire INTT_trigger; 

`ifndef SS2_WRAPPER
    wire usb_clk_buf;
`endif

    wire crypt_init;
    wire crypt_ready;
    wire crypt_start;
    wire crypt_done;
    wire crypt_busy;

    wire [7:0] usb_dout;
    wire isout;
    wire [pADDR_WIDTH-pBYTECNT_SIZE-1:0] reg_address;
    wire [pBYTECNT_SIZE-1:0] reg_bytecnt;
    wire reg_addrvalid;
    wire [7:0] write_data;
    wire [7:0] read_data;
    wire reg_read;
    wire reg_write;
    wire [4:0] clk_settings;
    wire crypt_clk;    

    wire resetn = pushbutton;
    wire reset = !resetn;

    wire  [AHB_ADDR_WIDTH-1:0]  haddr_i;
    wire  [AHB_DATA_WIDTH-1:0]  hwdata_i;
    wire                        hsel_i;
    wire                        hwrite_i;
    wire                        hready_i;
    wire  [1:0]                 htrans_i;
    wire  [2:0]                 hsize_i;
    wire                        hresp_o;
    wire                        hreadyout_o;
    wire [AHB_DATA_WIDTH-1:0]   hrdata_o;

    // mldsa_mem_if mldsa_memory_export();

    // Declare a counter large enough to hold the count for 1 second
    reg [23:0] counter; // 24 bits can count up to 16,777,215
    reg led2_reg;

    // Synchronous process with active-low reset
    always @(posedge crypt_clk or negedge resetn) begin
        if (!resetn) begin
            counter   <= 24'd0;
            led2_reg  <= 1'b0;
        end else begin
            if (tio_trigger) begin
                // Start the counter when trigger is high
                counter  <= 24'd10000000; // Load counter with 10,000,000
                led2_reg <= 1'b1;         // Turn on the LED
            end else if (counter != 24'd0) begin
                // Decrement the counter if it's not zero
                counter <= counter - 1'b1;
                if (counter == 24'd1) begin
                    led2_reg <= 1'b0;     // Turn off the LED when counter reaches zero
                end
            end
        end
    end
    // Drive the LED output
    assign led2 = led2_reg;
      
  
    // USB CLK Heartbeat
    // reg [31:0] usb_timer_heartbeat;
    // always @(posedge usb_clk_buf) usb_timer_heartbeat <= usb_timer_heartbeat +  32'd1;
    wire O_user_led;
    assign led1 = O_user_led;

    // CRYPT CLK Heartbeat
    reg [22:0] crypt_clk_heartbeat;
    always @(posedge crypt_clk) crypt_clk_heartbeat <= crypt_clk_heartbeat +  23'd1;
    
    assign led3 = 1'b1;


    cw305_usb_reg_fe #(
       .pBYTECNT_SIZE           (pBYTECNT_SIZE),
       .pADDR_WIDTH             (pADDR_WIDTH)
    ) U_usb_reg_fe (
       .rst                     (reset),
       .usb_clk                 (usb_clk_buf), 
       .usb_din                 (usb_data), 
       .usb_dout                (usb_dout), 
       .usb_rdn                 (usb_rdn), 
       .usb_wrn                 (usb_wrn),
       .usb_cen                 (usb_cen),
       .usb_alen                (1'b0),                 // unused
       .usb_addr                (usb_addr),
       .usb_isout               (isout), 
       .reg_address             (reg_address), 
       .reg_bytecnt             (reg_bytecnt), 
       .reg_datao               (write_data), 
       .reg_datai               (read_data),
       .reg_read                (reg_read), 
       .reg_write               (reg_write), 
       .reg_addrvalid           (reg_addrvalid)
    );


    ahb_interface    #(
       .pBYTECNT_SIZE           (pBYTECNT_SIZE),
       .pADDR_WIDTH             (pADDR_WIDTH),
       .AHB_ADDR_WIDTH          (AHB_ADDR_WIDTH),
       .AHB_DATA_WIDTH          (AHB_DATA_WIDTH)
    )
    ahb_interface_i
    (
       .usb_clk                 (usb_clk_buf), 
       .crypto_clk              (crypt_clk),
       .reset_i                 (reset),
       .reg_address             (reg_address[pADDR_WIDTH-pBYTECNT_SIZE-1:0]), 
       .reg_bytecnt             (reg_bytecnt), 
       .read_data               (read_data), 
       .write_data              (write_data),
       .reg_read                (reg_read), 
       .reg_write               (reg_write), 
       .reg_addrvalid           (reg_addrvalid),

       .exttrigger_in           (usb_trigger),
       
       .O_clksettings           (clk_settings),
       .O_user_led              (O_user_led),
       
        //AHB Lite Interface
        .haddr                  (haddr_i),
        .hwdata                 (hwdata_i),
        .hsel                   (hsel_i),
        .hwrite                 (hwrite_i),
        .hready                 (hready_i),
        .htrans                 (htrans_i),
        .hsize                  (hsize_i),
        .hresp                  (hresp_o),
        .hreadyout              (hreadyout_o),
        .hrdata                 (hrdata_o)
    );

    assign usb_data = isout? usb_dout : 8'bZ;


    clocks U_clocks (
       .usb_clk                 (usb_clk),
       .usb_clk_buf             (usb_clk_buf),
       .I_j16_sel               (j16_sel),
       .I_k16_sel               (k16_sel),
       .I_clock_reg             (clk_settings),
       .I_cw_clkin              (tio_clkin),
       .I_pll_clk1              (pll_clk1),
       .O_cw_clkout             (tio_clkout),
       .O_cryptoclk             (crypt_clk)

    );

  //----------------------------------------------------------------
  // Device Under Test.
  //----------------------------------------------------------------
    /*
  mldsa_top #(
             .AHB_DATA_WIDTH(32),
             .AHB_ADDR_WIDTH(32)
            )
            dut (
             .clk(crypt_clk),
             .rst_b(resetn),
             
            .NTT_trigger(NTT_trigger),
            .PWM_trigger(PWM_trigger),
            .PWA_trigger(PWA_trigger),
            .INTT_trigger(INTT_trigger),

             .haddr_i(haddr_i),
             .hwdata_i(hwdata_i),
             .hsel_i(hsel_i),
             .hwrite_i(hwrite_i),
             .hready_i(hready_i),
             .htrans_i(htrans_i),
             .hsize_i(hsize_i),

             .hresp_o(hresp_o),
             .hreadyout_o(hreadyout_o),
             .hrdata_o(hrdata_o),
             
             .mldsa_memory_export(mldsa_memory_export.req),

//             .kv_read(),
//             .kv_rd_resp('0),
//             .pcr_signing_data('0),

             .debugUnlock_or_scan_mode_switch('0),
             .busy_o(crypt_busy),
             
             .error_intr(),
             .notif_intr()
            //  .trigger(trigger),
              
            );
            

    mldsa_mem_top mldsa_mem_top_inst (
        .clk_i(crypt_clk),
        .mldsa_memory_export(mldsa_memory_export.resp)
    );
    */

    ntt_wrapper_fpga #(
        .AHB_ADDR_WIDTH(AHB_ADDR_WIDTH),
        .AHB_DATA_WIDTH(AHB_DATA_WIDTH)
    ) dut (
        .hclk(crypt_clk),
        .hreset_n(resetn),
        .haddr_i(haddr_i),
        .hwdata_i(hwdata_i),
        .hsel_i(hsel_i),
        .hwrite_i(hwrite_i),
        .hready_i(hready_i),
        .htrans_i(htrans_i),
        .hsize_i(hsize_i),
        .hresp_o(hresp_o),
        .hreadyout_o(hreadyout_o),
        .hrdata_o(hrdata_o),

        // NTT triggers
        .ntt_trigger_o(NTT_trigger)
    );

   assign tio_trigger = NTT_trigger; //PWM_trigger; //TODO: confirm?

    

endmodule

`default_nettype wire