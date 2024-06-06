class ntt_fwd_seq extends ntt_base_seq;

    `uvm_object_utils(ntt_fwd_seq)
    ntt_txn ntt_txn_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        ntt_txn_i = ntt_txn::type_id::create(.name("ntt_txn_i"));
        start_item(ntt_txn_i);
        assert(ntt_txn_i.randomize() with {
            ntt_enable == 1;
            mode == mode_t'(ct);       // Set mode to 'ct'
            zeroize == 0;              // Set zeroize to 0
            accumulate == 0;
            sampler_valid == 0;
            sampler_mode == 0;
            sampler_data == 0;
        }) else begin
            `uvm_error("RANDOMIZE_FAIL", "Randomization failed for ntt_txn_i")
        end
        // Print the randomized values for debugging
        // `uvm_info("ntt_simple_seq", $sformatf("Randomized ntt_txn_i: %p", ntt_txn_i), UVM_LOW)
        finish_item(ntt_txn_i);
    endtask: body

endclass