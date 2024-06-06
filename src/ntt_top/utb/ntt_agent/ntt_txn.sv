// import ntt_utb_defines::*;
// import ntt_defines_pkg::*;

class ntt_txn extends uvm_sequence_item;

    rand  bit                       zeroize;
    rand  mode_t                    mode;
    rand  bit                       ntt_enable;


    rand  ntt_mem_addr_t            ntt_mem_base_addr;
    rand  pwo_mem_addr_t            pwo_mem_base_addr;

    rand  bit                       accumulate;
    rand  bit                       sampler_valid;
    rand  bit                       sampler_mode;
    rand  bit [MEM_DATA_WIDTH-1:0]  sampler_data;
    rand  bit                       ntt_done;
    rand  bit                       stage_done;
    rand  int                       stage_idx;

    constraint ntt_c {
        ntt_enable == 1;
    }


    // Constraints for ntt_mem_base_addr
    constraint ntt_mem_base_addr_c {
        // src_base_addr must be a multiple of 64 and within the valid address range
        ntt_mem_base_addr.src_base_addr % 64 == 0;
        ntt_mem_base_addr.src_base_addr < (MEM_DEPTH-64);
        
        ntt_mem_base_addr.interim_base_addr == ntt_mem_base_addr.src_base_addr + 64;
        
        // dest_base_addr must be a multiple of 64, within the valid address range, and different from src_base_addr
        ntt_mem_base_addr.dest_base_addr % 64 == 0;
        ntt_mem_base_addr.dest_base_addr < (MEM_DEPTH-64);
        ntt_mem_base_addr.dest_base_addr != ntt_mem_base_addr.interim_base_addr;
    }

    function new(string name = "");
       super.new(name);
    endfunction: new

    // function void post_randomize();
    //     //-- load source data to memory at src_base_addr
    //     fork
    //         begin
    //             top.load_mem(src_base_addr, src_data, src_data.size());
    //         end
    //     join_none
    // endfunction: post_randomize

    `uvm_object_utils_begin(ntt_txn)
        `uvm_field_int(zeroize, UVM_ALL_ON)
        `uvm_field_int(mode, UVM_ALL_ON)
        `uvm_field_int(ntt_enable, UVM_ALL_ON)
        `uvm_field_int(ntt_mem_base_addr.src_base_addr, UVM_ALL_ON)
        `uvm_field_int(ntt_mem_base_addr.interim_base_addr, UVM_ALL_ON)
        `uvm_field_int(ntt_mem_base_addr.dest_base_addr, UVM_ALL_ON)
        `uvm_field_int(pwo_mem_base_addr.pw_base_addr_a, UVM_ALL_ON)
        `uvm_field_int(pwo_mem_base_addr.pw_base_addr_b, UVM_ALL_ON)
        `uvm_field_int(pwo_mem_base_addr.pw_base_addr_c, UVM_ALL_ON)
        `uvm_field_int(accumulate, UVM_ALL_ON)
        `uvm_field_int(sampler_valid, UVM_ALL_ON)
        `uvm_field_int(sampler_mode, UVM_ALL_ON)
        `uvm_field_int(sampler_data, UVM_ALL_ON)
        `uvm_field_int(stage_done, UVM_ALL_ON)
        `uvm_field_int(stage_idx, UVM_ALL_ON)
    `uvm_object_utils_end

endclass: ntt_txn
