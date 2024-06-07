class ntt_inv_seq extends ntt_base_seq;

    `uvm_object_utils(ntt_inv_seq)
    ntt_txn ntt_txn_i;
    ntt_mem_addr_t ntt_mem_base_addr; // Shared variable for base address
    bit use_shared_addr; // Flag to control address assignment

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        ntt_txn_i = ntt_txn::type_id::create(.name("ntt_txn_i"));
        start_item(ntt_txn_i);
        if (use_shared_addr != null) begin
            assert(ntt_txn_i.randomize() with {
                ntt_enable == 1;
                mode == mode_t'(gs);       // Set mode to 'gs'
                zeroize == 0;              // Set zeroize to 0
                accumulate == 0;
                sampler_valid == 0;
                sampler_mode == 0;
                sampler_data == 0;
                ntt_mem_base_addr == this.ntt_mem_base_addr; // Use the shared variable
            }) else begin
                `uvm_error("RANDOMIZE_FAIL", "Randomization failed for ntt_txn_i")
            end
        end else begin
            assert(ntt_txn_i.randomize() with {
                ntt_enable == 1;
                mode == mode_t'(gs);       // Set mode to 'gs'
                zeroize == 0;              // Set zeroize to 0
                accumulate == 0;
                sampler_valid == 0;
                sampler_mode == 0;
                sampler_data == 0;
            }) else begin
                `uvm_error("RANDOMIZE_FAIL", "Randomization failed for ntt_txn_i")
            end
        end
        // Print the randomized values for debugging
        // `uvm_info("ntt_simple_seq", $sformatf("Randomized ntt_txn_i: %p", ntt_txn_i), UVM_LOW)
        finish_item(ntt_txn_i);
    endtask: body

endclass
