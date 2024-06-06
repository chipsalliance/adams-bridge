// import ntt_utb_defines::*;
import ntt_defines_pkg::*;
interface ntt_if(input bit clk);

    logic                           reset_n;
    logic                           zeroize;
    mode_t                          mode;
    logic                           ntt_enable;

    ntt_mem_addr_t                  ntt_mem_base_addr;
    pwo_mem_addr_t                  pwo_mem_base_addr;

    logic                           accumulate;
    logic                           sampler_valid;
    logic                           sampler_mode;
    logic [MEM_DATA_WIDTH-1:0]      sampler_data;

    logic                           ntt_done;
    logic                           stage_done;

    clocking ntt_m_cb @ (posedge clk);
        default input #1step output #1ns;
        input reset_n;
        output zeroize;
        output mode;
        output ntt_enable;

        output ntt_mem_base_addr;
        output pwo_mem_base_addr;

        output accumulate;
        output sampler_valid;
        output sampler_mode;
        output sampler_data;

        input ntt_done;
        input stage_done;
    endclocking: ntt_m_cb

    clocking ntt_s_cb@ (posedge clk);
        default input #1step output #1ns;
        input reset_n;
        input zeroize;
        input mode;
        input ntt_enable;

        input ntt_mem_base_addr;
        input pwo_mem_base_addr;

        input accumulate;
        input sampler_valid;
        input sampler_mode;
        input sampler_data;

        input ntt_done;
        input stage_done;
    endclocking :ntt_s_cb

    modport ntt_m_sync_mp(clocking ntt_m_cb);
    modport ntt_s_sync_mp(clocking ntt_s_cb);

endinterface: ntt_if