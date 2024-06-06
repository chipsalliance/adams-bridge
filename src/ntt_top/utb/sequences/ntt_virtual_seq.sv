class ntt_virtual_seq extends uvm_sequence#(uvm_sequence_item);

    `uvm_object_utils(ntt_virtual_seq)

    // Declare handles for the sequencers
    mem_sequencer mem_seqr;
    ntt_sequencer ntt_seqr;
    mem_base_seq mem_seq_i;
    ntt_base_seq ntt_seq_i;

    function new(string name = "");
        super.new(name);
    endfunction: new

    task body();
        // Instantiate the memory init sequence and NTT sequence      
        // mem_seq_i = mem_init_seq::type_id::create(.name("mem_seq_i"));
        // ntt_seq_i = ntt_base_seq::type_id::create(.name("ntt_seq_i"));

        fork
            begin
                mem_seq_i.start(mem_seqr);
            end
            begin
                #10ns;
                ntt_seq_i.start(ntt_seqr);
            end
        join

        // Optionally, you can add more sequences or additional coordination logic here
    endtask: body

endclass

