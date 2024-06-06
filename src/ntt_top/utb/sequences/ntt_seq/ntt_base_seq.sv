class ntt_base_seq extends uvm_sequence#(ntt_txn);

    `uvm_object_utils(ntt_base_seq)

    function new (string name = "");
        super.new(name);
    endfunction: new

endclass