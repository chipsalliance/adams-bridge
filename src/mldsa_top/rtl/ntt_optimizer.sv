module ntt_optimizer 
  import abr_prim_alert_pkg::*;
  import mldsa_reg_pkg::*;
  import mldsa_params_pkg::*;
  import mldsa_ctrl_pkg::*;
  import mldsa_sampler_pkg::*;
  import abr_sha3_pkg::*;
  import ntt_defines_pkg::*;
  import decompose_defines_pkg::*;
  #(
    // Top-level parameters
    parameter AHB_ADDR_WIDTH   = 32,
    parameter AHB_DATA_WIDTH   = 64,
    parameter CLIENT_DATA_WIDTH = 32
  ) (
    input logic clk,
    input logic reset_n,

    // Inputs from controller
    input logic [1:0] ntt_enable,           // ntt_enable[0] for NTT_0, ntt_enable[1] for NTT_1
    input mldsa_ntt_mode_e [1:0] ntt_mode,
    input ntt_mem_addr_t [1:0] ntt_mem_base_addr,
    input pwo_mem_addr_t [1:0] pwo_mem_base_addr,

    // Outputs to controller
    output logic [1:0] ntt_busy,

    // Interface to NTT engine
    output logic ntt_start,
    output mldsa_ntt_mode_e ntt_mode_o,
    output ntt_mem_addr_t ntt_mem_base_addr_o,
    output pwo_mem_addr_t pwo_mem_base_addr_o,
    output logic sampler_valid_o,   // Added sampler_valid_o
    input logic ntt_done            // Signal from NTT engine indicating operation is done
);

    // Constants
    localparam DELAY_CYCLES = 4;

    // Type definitions
    typedef enum logic [3:0] {
        NTT_IDLE,
        NTT_RUNNING0,
        NTT_RUNNING1,
        NTT_DELAY_BEFORE_START1,
        NTT_DELAY_BEFORE_START0,
        NTT_RUNNING01,
        NTT_RUNNING10,
        NTT_WAITING_TO_RELEASE_BUSY0,
        NTT_WAITING_TO_RELEASE_BUSY1,
        NTT_WAITING_TO_RELEASE_BUSY10,
        NTT_WAITING_TO_RELEASE_BUSY01
    } ntt_engine_state_t;

    typedef struct {
        mldsa_ntt_mode_e ntt_mode;
        ntt_mem_addr_t ntt_mem_base_addr;
        pwo_mem_addr_t pwo_mem_base_addr;
        logic valid; // Indicates whether a valid request is stored
    } ntt_request_t;

    // Internal signals
    ntt_engine_state_t ntt_engine_state;
    logic ntt_active_request; // 0 for NTT_0, 1 for NTT_1
    ntt_request_t ntt0_req, ntt1_req;
    logic [3:0] delay_counter; // For delay cycles before releasing busy signals

    // Internal registers for outputs
    logic ntt_start_reg;
    mldsa_ntt_mode_e ntt_mode_o_reg;
    ntt_mem_addr_t ntt_mem_base_addr_o_reg;
    pwo_mem_addr_t pwo_mem_base_addr_o_reg;
    logic sampler_valid_o_reg;
    logic [1:0] busy_valid_disable;
    // Assign outputs
    assign ntt_start             = ntt_start_reg;
    assign ntt_mode_o            = ntt_mode_o_reg;
    assign ntt_mem_base_addr_o   = ntt_mem_base_addr_o_reg;
    assign pwo_mem_base_addr_o   = pwo_mem_base_addr_o_reg;
    assign sampler_valid_o       = sampler_valid_o_reg;

    // Reset and request capturing
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            ntt_engine_state       <= NTT_IDLE;
            ntt_active_request     <= 0;
            ntt_start_reg          <= 0;
            ntt0_req.valid         <= 0;
            ntt_busy[0]            <= 0;
            ntt1_req.valid         <= 0;
            ntt_busy[1]            <= 0;
            delay_counter          <= 0;
            sampler_valid_o_reg    <= 0;
            busy_valid_disable     <= 0;
        end else begin
            // Capture incoming requests
            if (ntt_enable[0]) begin
                ntt0_req.valid               <= 1;
                ntt0_req.ntt_mode            <= ntt_mode[0];
                ntt0_req.ntt_mem_base_addr   <= ntt_mem_base_addr[0];
                ntt0_req.pwo_mem_base_addr   <= pwo_mem_base_addr[0];
                ntt_busy[0]                  <= 3;
            end
            else if (busy_valid_disable[0]==1'b1)begin
                ntt0_req.valid               <= 0;
                ntt0_req.ntt_mode            <= ntt_mode[1];
                ntt0_req.ntt_mem_base_addr   <= 0;
                ntt0_req.pwo_mem_base_addr   <= 0;
                ntt_busy[0]                  <= 0;
            end

            if (ntt_enable[1]) begin
                ntt1_req.valid               <= 1;
                ntt1_req.ntt_mode            <= ntt_mode[1];
                ntt1_req.ntt_mem_base_addr   <= ntt_mem_base_addr[1];
                ntt1_req.pwo_mem_base_addr   <= pwo_mem_base_addr[1];
                ntt_busy[1]                  <= 1;
            end
            else if (busy_valid_disable[1]==1'b1)begin
                ntt1_req.valid               <= 0;
                ntt1_req.ntt_mode            <= ntt_mode[1];
                ntt1_req.ntt_mem_base_addr   <= 0;
                ntt1_req.pwo_mem_base_addr   <= 0;
                ntt_busy[1]                  <= 0;
            end


            // NTT engine state machine
            case (ntt_engine_state)
                NTT_IDLE: begin
                    busy_valid_disable     <= 0;
                    if (ntt0_req.valid) begin
                        // Start processing NTT_0 request
                        ntt_mode_o_reg            <= ntt0_req.ntt_mode;
                        ntt_mem_base_addr_o_reg   <= ntt0_req.ntt_mem_base_addr;
                        pwo_mem_base_addr_o_reg   <= ntt0_req.pwo_mem_base_addr;
                        ntt_start_reg             <= 1;
                        sampler_valid_o_reg       <= 1; // Enable sampler_valid_o for NTT_0
                        ntt_engine_state          <= NTT_RUNNING0;
                    end else if (ntt1_req.valid) begin
                        // Start processing NTT_1 request
                        ntt_mode_o_reg            <= ntt1_req.ntt_mode;
                        ntt_mem_base_addr_o_reg   <= ntt1_req.ntt_mem_base_addr;
                        pwo_mem_base_addr_o_reg   <= ntt1_req.pwo_mem_base_addr;
                        ntt_start_reg             <= 1;
                        sampler_valid_o_reg       <= 0; // Disable sampler_valid_o for NTT_1
                        ntt_engine_state          <= NTT_RUNNING1;
                    end else begin
                        ntt_start_reg             <= 0;
                    end
                end
                NTT_RUNNING0: begin
                    ntt_start_reg <= 0; // Deassert start
                    busy_valid_disable     <= 0;
                    if (ntt_done && ~ntt_start_reg) begin
                        // Operation completed
                        if (ntt1_req.valid) begin
                            // Start processing NTT_1 request                            
                            delay_counter       <= 0;
                            sampler_valid_o_reg       <= 0; // Disable sampler_valid_o for NTT_1
                            ntt_engine_state          <= NTT_DELAY_BEFORE_START1;
                        end else begin
                            // No more requests
                            ntt_engine_state    <= NTT_WAITING_TO_RELEASE_BUSY0;
                            delay_counter       <= 0;
                        end
                    end
                end
                NTT_RUNNING1: begin
                    busy_valid_disable     <= 0;
                    ntt_start_reg <= 0; // Deassert start
                    if (ntt_done && ~ntt_start_reg) begin
                        // Operation completed
                        if (ntt0_req.valid) begin
                        // Start processing NTT_0 request                            
                            delay_counter       <= 0;
                            sampler_valid_o_reg <= 1; // Disable sampler_valid_o when done
                            ntt_engine_state          <= NTT_DELAY_BEFORE_START0;
                        end else begin
                            // No more requests
                            ntt_engine_state    <= NTT_WAITING_TO_RELEASE_BUSY1;
                            delay_counter       <= 0;
                            sampler_valid_o_reg <= 0; // Disable sampler_valid_o when done
                        end
                    end
                end
                // Delay before starting NTT_1
                NTT_DELAY_BEFORE_START1: begin
                    ntt_start_reg <= 0;
                    busy_valid_disable     <= 0;
                    if (delay_counter < DELAY_CYCLES - 1) begin
                        delay_counter <= delay_counter + 1;
                    end else begin
                        // Start processing NTT_1 request
                        ntt_mode_o_reg            <= ntt1_req.ntt_mode;
                        ntt_mem_base_addr_o_reg   <= ntt1_req.ntt_mem_base_addr;
                        pwo_mem_base_addr_o_reg   <= ntt1_req.pwo_mem_base_addr;
                        ntt_start_reg             <= 1;
                        sampler_valid_o_reg       <= 0; // Disable sampler_valid_o for NTT_1
                        ntt_engine_state          <= NTT_RUNNING01;
                    end
                end
                // Delay before starting NTT_0
                NTT_DELAY_BEFORE_START0: begin
                    ntt_start_reg <= 0;
                    busy_valid_disable     <= 0;
                    if (delay_counter < DELAY_CYCLES - 1) begin
                        delay_counter <= delay_counter + 1;
                    end else begin
                        // Start processing NTT_0 request
                        ntt_mode_o_reg            <= ntt0_req.ntt_mode;
                        ntt_mem_base_addr_o_reg   <= ntt0_req.ntt_mem_base_addr;
                        pwo_mem_base_addr_o_reg   <= ntt0_req.pwo_mem_base_addr;
                        ntt_start_reg             <= 1;
                        sampler_valid_o_reg       <= 1; // Enable sampler_valid_o for NTT_0
                        ntt_engine_state          <= NTT_RUNNING10;
                    end
                end
                
                NTT_RUNNING10: begin
                    busy_valid_disable     <= 0;
                    ntt_start_reg <= 0; // Deassert start
                    if (ntt_done && ~ntt_start_reg) begin
                        // Operation completed
                        ntt_engine_state    <= NTT_WAITING_TO_RELEASE_BUSY10;
                        delay_counter       <= 0;
                        sampler_valid_o_reg <= 0; // Disable sampler_valid_o when done
                    end
                end
                
                NTT_RUNNING01: begin
                    busy_valid_disable     <= 0;
                    ntt_start_reg <= 0; // Deassert start
                    if (ntt_done && ~ntt_start_reg) begin
                        // Operation completed
                        ntt_engine_state    <= NTT_WAITING_TO_RELEASE_BUSY01;
                        delay_counter       <= 0;
                        sampler_valid_o_reg <= 0; // Disable sampler_valid_o when done
                    end
                end

                NTT_WAITING_TO_RELEASE_BUSY0: begin
                    if (delay_counter < DELAY_CYCLES) begin
                        delay_counter <= delay_counter + 1;
                    end else begin
                        ntt_engine_state       <= NTT_IDLE;
                        delay_counter          <= 0;
                    end
                    if (delay_counter == 0) begin
                        busy_valid_disable     <= 1;
                    end else begin
                        busy_valid_disable     <= 0;
                    end
                end

                NTT_WAITING_TO_RELEASE_BUSY1: begin
                    if (delay_counter < DELAY_CYCLES) begin
                        delay_counter <= delay_counter + 1;
                    end else begin
                        ntt_engine_state       <= NTT_IDLE;
                        delay_counter          <= 0;
                    end
                    if (delay_counter == 0) begin
                        busy_valid_disable     <= 2;
                    end else begin
                        busy_valid_disable     <= 0;
                    end
                end

                
                NTT_WAITING_TO_RELEASE_BUSY10: begin
                    if (delay_counter < DELAY_CYCLES) begin
                        delay_counter <= delay_counter + 1;
                    end else begin
                        ntt_engine_state       <= NTT_WAITING_TO_RELEASE_BUSY0;
                        delay_counter          <= 0;
                    end
                    if (delay_counter == 0) begin
                        busy_valid_disable     <= 2;
                    end else begin
                        busy_valid_disable     <= 0;
                    end
                end
                NTT_WAITING_TO_RELEASE_BUSY01: begin
                    if (delay_counter < DELAY_CYCLES) begin
                        delay_counter <= delay_counter + 1;
                        // busy_valid_disable     <= 1;
                    end else begin
                        ntt_engine_state       <= NTT_WAITING_TO_RELEASE_BUSY1;
                        delay_counter          <= 0;
                    end
                    if (delay_counter == 0) begin
                        busy_valid_disable     <= 1;
                    end else begin
                        busy_valid_disable     <= 0;
                    end
                end

                default: begin
                    ntt_engine_state <= NTT_IDLE;
                end
            endcase
        end
    end

endmodule
