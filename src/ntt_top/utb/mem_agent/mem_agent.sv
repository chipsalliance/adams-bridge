class mem_agent extends uvm_agent;

    `uvm_component_utils(mem_agent)

    uvm_analysis_port#(mem_txn) mem_ap;

    mem_sequencer           mem_sqcr_i;
    mem_driver              mem_driver_i;
    mem_mon                 mem_mon_i;

    function new(string name, uvm_component parent);
        super.new(name, parent);
        mem_ap = new("mem_ap", this);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);

        mem_sqcr_i = mem_sequencer::type_id::create(.name("mem_sqcr_i"), .parent(this));
        mem_driver_i = mem_driver::type_id::create(.name("mem_driver_i"), .parent(this));
        mem_mon_i = mem_mon::type_id::create(.name("mem_mon_i"), .parent(this));
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        mem_driver_i.seq_item_port.connect(mem_sqcr_i.seq_item_export);
        mem_mon_i.mem_ap.connect(mem_ap);
    endfunction: connect_phase

endclass: mem_agent