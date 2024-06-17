// import ntt_utb_defines::*;
// import ntt_defines_pkg::*;
// import uvm_pkg::*;


class mem_txn extends uvm_sequence_item;

    rand bit reset_n;
    rand bit reset_indicator;
    rand  mem_if_t mem_port0_req;
    rand  mem_if_t mem_port1_req;
    rand  bit [MEM_DATA_WIDTH-1:0] p0_read_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p0_write_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p1_read_data;
    rand  bit [MEM_DATA_WIDTH-1:0] p1_write_data;
    rand bit update_mem;
    rand bit [MEM_DATA_WIDTH-1:0]    artificialMemory [];

    // Define constants
    localparam int DILITHIUM_Q = 23'd8380417;


    function new(string name = "");
       super.new(name);
       artificialMemory = new[MEM_DEPTH];
    endfunction: new

    //Constraint for artificialMemory
    constraint artificialMemory_c {
        foreach (artificialMemory[i]) {
            (artificialMemory[i][23:0] < DILITHIUM_Q) &&
            (artificialMemory[i][47:24] < DILITHIUM_Q) &&
            (artificialMemory[i][71:48] < DILITHIUM_Q) &&
            (artificialMemory[i][95:72] < DILITHIUM_Q);
        }
    }


    `uvm_object_utils_begin(mem_txn)
        `uvm_field_int(reset_n, UVM_ALL_ON)
        `uvm_field_int(mem_port0_req.addr, UVM_ALL_ON)
        `uvm_field_enum(mem_rw_mode_e, mem_port0_req.rd_wr_en, UVM_ALL_ON)
        `uvm_field_int(mem_port1_req.addr, UVM_ALL_ON)
        `uvm_field_enum(mem_rw_mode_e, mem_port1_req.rd_wr_en, UVM_ALL_ON)
        `uvm_field_int(p0_read_data, UVM_ALL_ON)
        `uvm_field_int(p0_write_data, UVM_ALL_ON)
        `uvm_field_int(p1_read_data, UVM_ALL_ON)
        `uvm_field_int(p1_write_data, UVM_ALL_ON)
        `uvm_field_int(update_mem, UVM_ALL_ON)
        `uvm_field_array_int(artificialMemory, UVM_ALL_ON)
    `uvm_object_utils_end



endclass: mem_txn