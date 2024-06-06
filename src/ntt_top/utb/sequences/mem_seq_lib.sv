class mem_base_seq extends uvm_sequence#(mem_txn);

    `uvm_object_utils(mem_base_seq)

    function new (string name = "");
        super.new(name);
    endfunction: new

endclass

class mem_init_seq extends mem_base_seq;

    `uvm_object_utils(mem_init_seq)
    mem_txn mem_txn_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        mem_txn_i = mem_txn::type_id::create(.name("mem_txn_i"));
        start_item(mem_txn_i);
        assert(mem_txn_i.randomize() with {
            update_mem == 1;
        });
        finish_item(mem_txn_i);
    endtask: body

endclass