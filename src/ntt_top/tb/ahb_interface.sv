// `timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 10/05/2023 07:33:09 AM
// Design Name: 
// Module Name: ahb_interface
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


module ahb_interface    #(
    parameter pADDR_WIDTH           = 21,
    parameter pBYTECNT_SIZE         = 8,
    parameter pDONE_EDGE_SENSITIVE  = 1,
    parameter pCRYPT_TYPE           = 8'h3,
    parameter pCRYPT_REV            = 8'h1,
    parameter pIDENTIFY             = 8'h2e,
   
    parameter AHB_ADDR_WIDTH        = 32,
    parameter AHB_DATA_WIDTH        = 32
    )
    (
    //CW Interface
    // Interface to cw305_usb_reg_fe:
    input  wire                                  usb_clk,
    input  wire                                  crypto_clk,
    input  wire                                  reset_i,
    input  wire [pADDR_WIDTH-pBYTECNT_SIZE-1:0]  reg_address,     // Address of register
    input  wire [pBYTECNT_SIZE-1:0]              reg_bytecnt,     // Current byte count
    output reg  [7:0]                            read_data,       //
    input  wire [7:0]                            write_data,      //
    input  wire                                  reg_read,        // Read flag. One clock cycle AFTER this flag is high
                                                                 // valid data must be present on the read_data bus
    input  wire                                  reg_write,       // Write flag. When high on rising edge valid data is
                                                                 // present on write_data
    input  wire                                  reg_addrvalid,   // Address valid flag

    // from top:
    input  wire                                  exttrigger_in,
   
    // register outputs:
    output reg  [4:0]                            O_clksettings,
    output reg                                   O_user_led,   

    //AHB Lite Interface
    output wire  [AHB_ADDR_WIDTH-1:0]  haddr,
    output wire  [AHB_DATA_WIDTH-1:0]  hwdata,
    output wire                        hsel,
    output wire                        hwrite,
    output wire                        hready,
    output wire  [1:0]                 htrans,
    output wire  [2:0]                 hsize,

    input wire                         hresp,
    input wire                         hreadyout,
    input wire [AHB_DATA_WIDTH-1:0]    hrdata
    
    );
    
    
    `define REG_CLKSETTINGS                 'h00
    `define REG_USER_LED                    'h01
    `define REG_CRYPT_TYPE                  'h02
    `define REG_CRYPT_REV                   'h03
    `define REG_IDENTIFY                    'h04
    //`define REG_CRYPT_GO                    'h05
    //`define REG_CRYPT_TEXTIN                'h06
    //`define REG_CRYPT_CIPHERIN              'h07
    //`define REG_CRYPT_TEXTOUT               'h08
    //`define REG_CRYPT_CIPHEROUT             'h09
    //`define REG_CRYPT_KEY                   'h0a
    `define REG_BUILDTIME                   'h0b
    
    `define REG_CRYPT_WR                    'h06
    `define REG_CRYPT_RD                    'h07
    `define REG_CRYPT_ADDR                  'h08
    `define REG_CRYPT_CTRL                  'h09
   
   
    reg  [7:0]                   reg_read_data;
    reg  [31:0]                  buildtime;

    reg  [AHB_DATA_WIDTH-1:0]    reg_wr;
    reg  [AHB_DATA_WIDTH-1:0]    reg_rd;
    reg  [AHB_ADDR_WIDTH-1 : 0]  reg_addr;
    reg  [7 : 0]                 reg_ctrl;

   (* ASYNC_REG = "TRUE" *) reg  [AHB_DATA_WIDTH-1:0] reg_wr_crypt;
   (* ASYNC_REG = "TRUE" *) reg  [AHB_ADDR_WIDTH : 0] reg_addr_crypt;
   (* ASYNC_REG = "TRUE" *) reg  [7 : 0]              reg_ctrl_crypt;
   (* ASYNC_REG = "TRUE" *) reg  [AHB_DATA_WIDTH-1:0] reg_rd_usb;
    
   always @(posedge crypto_clk) begin
       reg_wr_crypt <= reg_wr;
       reg_addr_crypt <= reg_addr;
       buildtime    <= 'h0;
   end
   
   always @(posedge crypto_clk) begin
        if (reset_i)
            reg_ctrl_crypt <= '0;
        else if (reg_ctrl_crypt == 0)
            reg_ctrl_crypt <= reg_ctrl;
        else
            reg_ctrl_crypt <= '0;
   end

   always @(posedge usb_clk) begin
       reg_rd_usb <= reg_rd;
   end
    

   //////////////////////////////////
   // read logic:
   //////////////////////////////////

   always @(*) begin
      if (reg_addrvalid && reg_read) begin
         case (reg_address)
            `REG_CLKSETTINGS:           reg_read_data = O_clksettings;
            `REG_USER_LED:              reg_read_data = O_user_led;
            `REG_CRYPT_TYPE:            reg_read_data = pCRYPT_TYPE;
            `REG_CRYPT_REV:             reg_read_data = pCRYPT_REV;
            `REG_IDENTIFY:              reg_read_data = pIDENTIFY;
            `REG_BUILDTIME:             reg_read_data = buildtime[reg_bytecnt*8 +: 8];
            `REG_CRYPT_WR:              reg_read_data = reg_wr[reg_bytecnt*8 +: 8];
            `REG_CRYPT_RD:              reg_read_data = reg_rd[reg_bytecnt*8 +: 8];
            `REG_CRYPT_ADDR:            reg_read_data = reg_addr[reg_bytecnt*8 +: 8];
            `REG_CRYPT_CTRL:            reg_read_data = reg_ctrl;
            default:                    reg_read_data = 8'h5A;
         endcase
      end
      else
         reg_read_data = 0;
   end

   // Register output read data to ease timing. If you need read data one clock
   // cycle earlier, simply remove this stage:
   always @(posedge usb_clk)
      read_data <= reg_read_data;
    

   //////////////////////////////////
   // write logic (USB clock domain):
   //////////////////////////////////
   always @(posedge usb_clk) begin
      if (reset_i) begin
         O_clksettings <= 0;
         O_user_led <= 0;
      end

      else begin
         if (reg_addrvalid && reg_write) begin
            case (reg_address)
               `REG_CLKSETTINGS:        O_clksettings <= write_data[4 : 0];
               `REG_USER_LED:           O_user_led <= write_data[0];
               `REG_CRYPT_WR:           reg_wr[reg_bytecnt*8 +: 8] <= write_data;
               `REG_CRYPT_ADDR:         reg_addr[reg_bytecnt*8 +: 8] <= write_data;
               `REG_CRYPT_CTRL:         reg_ctrl <= write_data;
            endcase
         end
         else if (reg_ctrl == reg_ctrl_crypt)
            reg_ctrl <= 0;
      end
   end
   

   //ddddd_MMMM_yyyyyy_hhhhh_mmmmmm_ssssss 
   
    
   //////////////////////////////////
   // AHB Interface Handler
   //////////////////////////////////   
    logic                        ahb_write_done;
    logic                        ahb_read_done;
    
    logic  [AHB_ADDR_WIDTH-1:0]  haddr_i;
    logic  [AHB_DATA_WIDTH-1:0]  hwdata_i;
    logic                        hsel_i;
    logic                        hwrite_i;
    logic                        hready_i;
    logic  [1:0]                 htrans_i;
    logic  [2:0]                 hsize_i;
    
    localparam AHB_HTRANS_IDLE     = 0;
    localparam AHB_HTRANS_BUSY     = 1;
    localparam AHB_HTRANS_NONSEQ   = 2;
    localparam AHB_HTRANS_SEQ      = 3;
        

    /*State register*/
    reg [2 : 0]  state_reg;
    reg [2 : 0]  state_next;
        
    /*STATES*/
    localparam [2 : 0] IDLE_ST          = 3'd0; 
    localparam [2 : 0] WRITE_ST         = 3'd1;
    localparam [2 : 0] READ_ST          = 3'd2;  
    localparam [2 : 0] DONE_ST          = 3'd3; 
    localparam [2 : 0] READ_ST_2        = 3'd4;  


    always_ff @(posedge crypto_clk) 
    begin : state_reg_update
        if (reset_i)
            state_reg       <= IDLE_ST;
        else
            state_reg       <= state_next;
    end // state_reg_update   
    
    //----------------------------------------------------------------
    // FSM_flow
    //
    //----------------------------------------------------------------
    always_comb 
    begin : interface_fsm
        state_next = IDLE_ST;
        unique casez(state_reg)
            IDLE_ST: begin
                   if (reg_ctrl_crypt == 8'h1)
                        state_next = WRITE_ST;
                   else if (reg_ctrl_crypt == 8'h2)
                        state_next = READ_ST;
                   else
                        state_next = IDLE_ST;
            end
            WRITE_ST:       state_next = (ahb_write_done)? DONE_ST : WRITE_ST;
            READ_ST:        state_next = READ_ST_2;
            READ_ST_2:      state_next = (ahb_read_done)? DONE_ST : READ_ST_2;
            DONE_ST:        state_next = IDLE_ST;
            default:        state_next = IDLE_ST;
        endcase
    end // interface_fsm
  
    always_ff @(posedge crypto_clk) 
    begin : ahb_interface
        if (reset_i) begin
            hsel_i          <= '0;
            haddr_i         <= '0;
            hwrite_i        <= '0;
            hready_i        <= '0;
            htrans_i        <= '0;
            hsize_i         <= '0;
            hwdata_i        <= '0;
            ahb_write_done  <= '0;
            ahb_read_done   <= '0;
        end
        else begin
            unique casez(state_reg)
                WRITE_ST: begin
                    if (ahb_write_done == 0) begin
                        hsel_i          <= 1'b1;
                        haddr_i         <= reg_addr_crypt;
                        hwrite_i        <= 1'b1;
                        hready_i        <= 1'b1;
                        htrans_i        <= AHB_HTRANS_NONSEQ;
                        hsize_i         <= 3'b011;
                        hwdata_i        <= '0;
                        
                        ahb_write_done  <= hreadyout;
                    end
                    else begin
                        haddr_i         <= 'Z;
                        hwrite_i        <= '0;
                        htrans_i        <= AHB_HTRANS_IDLE;
                        hwdata_i        <= reg_wr_crypt;                        
                    end
                end
                READ_ST: begin
                    hsel_i          <= 1'b1;
                    haddr_i         <= reg_addr_crypt;
                    hwrite_i        <= '0;
                    hready_i        <= 1'b1;
                    htrans_i        <= AHB_HTRANS_NONSEQ;
                    hsize_i         <= 3'b011;                    
                    ahb_read_done   <= '0;
               
                end
                READ_ST_2: begin
                    if (ahb_read_done == 0) begin
                        hsel_i          <= 1'b1;
                        haddr_i         <= reg_addr_crypt;
                        hwrite_i        <= '0;
                        hready_i        <= 1'b1;
                        htrans_i        <= AHB_HTRANS_NONSEQ;
                        hsize_i         <= 3'b011;
                        
                        ahb_read_done   <= hreadyout;
                    end
                    else begin
                        haddr_i         <= 'Z;
                        htrans_i        <= AHB_HTRANS_IDLE;
                        hwdata_i        <= '0;
                    end
               
                end
                default: begin
                    ahb_write_done  <= '0;
                    ahb_read_done   <= '0;
                end
            endcase
        end
   end
   
   logic ahb_read_done_ff;

   always_ff @(posedge crypto_clk) 
    begin
        if (reset_i)
            ahb_read_done_ff          <= '0;
        else if (ahb_read_done)
            ahb_read_done_ff          <= ahb_read_done;
    end
       
   always_ff @(posedge crypto_clk) 
    begin : read_reg_ff
        if (reset_i)
            reg_rd          <= '0;
        else if (ahb_read_done & ahb_read_done_ff)
            reg_rd          <= hrdata;
    end

    assign haddr = haddr_i;
    assign hwdata = hwdata_i;
    assign hsel = hsel_i;
    assign hwrite = hwrite_i;
    assign hready = hready_i;
    assign htrans = htrans_i;
    assign hsize = hsize_i;

          
endmodule
