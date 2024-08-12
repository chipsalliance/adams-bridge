
interface mem_if(input bit clk);
    import abr_params_pkg::*;
    logic reset_n;
    mem_if_t mem_port0_req;
    mem_if_t mem_port1_req;
    logic [MEM_DATA_WIDTH-1:0] p0_read_data;
    logic [MEM_DATA_WIDTH-1:0] p0_write_data;
    logic [MEM_DATA_WIDTH-1:0] p1_read_data;
    logic [MEM_DATA_WIDTH-1:0] p1_write_data;
    logic update_mem;
    string mem_path;
    



    clocking mem_s_cb @ (posedge clk);
        default input #1step output #1ns;
        input reset_n;
        input mem_port0_req;
        input mem_port1_req;
        input p0_read_data;
        input p0_write_data;
        input p1_read_data;
        input p1_write_data;
    endclocking: mem_s_cb

    // modport mem_m_sync_mp(clocking mem_m_cb);
    modport mem_s_sync_mp(clocking mem_s_cb);

    task update_mem_task(input logic [ABR_MEM_ADDR_WIDTH-1:0] addr, input logic [MEM_DATA_WIDTH-1:0] data);
        // Time zero assignment to update memory content using hierarchical reference
        case (mem_path)
            "mem_ntt": ntt_utb_top.ntt_mem.mem[addr]        = data;
            "mem_pwm_a": ntt_utb_top.pwm_mem_a.mem[addr]    = data;
            "mem_pwm_b": ntt_utb_top.pwm_mem_b.mem[addr]    = data;
            default: $fatal("Unknown memory path: %s", mem_path);
        endcase
    endtask: update_mem_task

    task read_mem(input logic [ABR_MEM_ADDR_WIDTH-1:0] addr, output logic [MEM_DATA_WIDTH-1:0] data);
        // Read the memory content using hierarchical reference
        case (mem_path)
            "mem_ntt": data     = ntt_utb_top.ntt_mem.mem[addr];
            "mem_pwm_a": data   = ntt_utb_top.pwm_mem_a.mem[addr];
            "mem_pwm_b": data   = ntt_utb_top.pwm_mem_b.mem[addr];
            default: $fatal("Unknown memory path: %s", mem_path);
        endcase
    endtask: read_mem

endinterface: mem_if