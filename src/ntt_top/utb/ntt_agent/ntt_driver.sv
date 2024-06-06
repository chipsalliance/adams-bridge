class ntt_driver extends uvm_driver#(ntt_txn);
    `uvm_component_utils(ntt_driver)

    virtual ntt_if ntt_vif;
    // Member variables to store the base addresses
    ntt_mem_addr_t stored_ntt_mem_base_addr;
    pwo_mem_addr_t stored_pwo_mem_base_addr;
    mode_t mode;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // assert( uvm_config_db#( virtual ntt_if )::get( this, "", "ntt_if", ntt_vif));
    endfunction: build_phase

    task run_phase(uvm_phase phase);

        ntt_txn ntt_txn_i;
        int txn_count;

        txn_count = 1;
        stored_ntt_mem_base_addr            <= '{default:0};
        stored_pwo_mem_base_addr            <= '{default:0};

        forever begin
            @ntt_vif.ntt_m_cb;
            seq_item_port.try_next_item(ntt_txn_i);            
            if(ntt_txn_i  != null ) begin
                // `uvm_info("TXN", $sformatf(" NTT_INPUT_TXN %0d : \n %s", txn_count++, ntt_txn_i.convert2string()), UVM_NONE)
                ntt_vif.ntt_m_cb.zeroize             <= ntt_txn_i.zeroize;
                ntt_vif.ntt_m_cb.mode                <= ntt_txn_i.mode;
                ntt_vif.ntt_m_cb.ntt_enable          <= ntt_txn_i.ntt_enable;

                ntt_vif.ntt_m_cb.ntt_mem_base_addr   <= ntt_txn_i.ntt_mem_base_addr;
                ntt_vif.ntt_m_cb.pwo_mem_base_addr   <= ntt_txn_i.pwo_mem_base_addr;

                // Update stored values with the new transaction values
                stored_ntt_mem_base_addr            <= ntt_txn_i.ntt_mem_base_addr;
                stored_pwo_mem_base_addr            <= ntt_txn_i.pwo_mem_base_addr;
                mode                                <= ntt_txn_i.mode;

                ntt_vif.ntt_m_cb.accumulate          <= ntt_txn_i.accumulate;
                ntt_vif.ntt_m_cb.sampler_valid       <= ntt_txn_i.sampler_valid;
                ntt_vif.ntt_m_cb.sampler_mode        <= ntt_txn_i.sampler_mode;
                ntt_vif.ntt_m_cb.sampler_data        <= ntt_txn_i.sampler_data;
                seq_item_port.item_done();
            end else begin
                ntt_vif.ntt_m_cb.zeroize             <= 'h0;
                ntt_vif.ntt_m_cb.mode                <= mode;
                ntt_vif.ntt_m_cb.ntt_enable          <= 'h0;

                // Use stored values instead of resetting to zero
                ntt_vif.ntt_m_cb.ntt_mem_base_addr   <= stored_ntt_mem_base_addr;
                ntt_vif.ntt_m_cb.pwo_mem_base_addr   <= stored_pwo_mem_base_addr;

                ntt_vif.ntt_m_cb.accumulate          <= 'h0;
                ntt_vif.ntt_m_cb.sampler_valid       <= 'h0;
                ntt_vif.ntt_m_cb.sampler_mode        <= 'h0;
                ntt_vif.ntt_m_cb.sampler_data        <= 'h0;
            end
        end

    endtask

endclass