
// This file was autogenerated by PeakRDL-uvm
package adamsbridge_reg_uvm;
    `include "uvm_macros.svh"
    import uvm_pkg::*;
    
    // Reg - adamsbridge_reg::ADAMSBRIDGE_NAME
    class adamsbridge_reg__ADAMSBRIDGE_NAME extends uvm_reg;
        rand uvm_reg_field NAME;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_NAME");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.NAME = new("NAME");
            this.NAME.configure(this, 32, 0, "RO", 1, 'h0, 0, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_NAME

    // Reg - adamsbridge_reg::ADAMSBRIDGE_VERSION
    class adamsbridge_reg__ADAMSBRIDGE_VERSION extends uvm_reg;
        rand uvm_reg_field VERSION;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_VERSION");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.VERSION = new("VERSION");
            this.VERSION.configure(this, 32, 0, "RO", 1, 'h0, 0, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_VERSION

    // Reg - adamsbridge_reg::ADAMSBRIDGE_CTRL
    class adamsbridge_reg__ADAMSBRIDGE_CTRL extends uvm_reg;
        rand uvm_reg_field CTRL;
        rand uvm_reg_field ZEROIZE;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_CTRL");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.CTRL = new("CTRL");
            this.CTRL.configure(this, 3, 0, "WO", 1, 'h0, 1, 1, 0);
            this.ZEROIZE = new("ZEROIZE");
            this.ZEROIZE.configure(this, 1, 3, "WO", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_CTRL

    // Reg - adamsbridge_reg::ADAMSBRIDGE_STATUS
    class adamsbridge_reg__ADAMSBRIDGE_STATUS extends uvm_reg;
        rand uvm_reg_field READY;
        rand uvm_reg_field VALID;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_STATUS");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.READY = new("READY");
            this.READY.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
            this.VALID = new("VALID");
            this.VALID.configure(this, 1, 1, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_STATUS

    // Reg - adamsbridge_reg::ADAMSBRIDGE_IV
    class adamsbridge_reg__ADAMSBRIDGE_IV extends uvm_reg;
        rand uvm_reg_field IV;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_IV");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.IV = new("IV");
            this.IV.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_IV

    // Reg - adamsbridge_reg::ADAMSBRIDGE_SEED
    class adamsbridge_reg__ADAMSBRIDGE_SEED extends uvm_reg;
        rand uvm_reg_field SEED;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_SEED");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SEED = new("SEED");
            this.SEED.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_SEED

    // Reg - adamsbridge_reg::ADAMSBRIDGE_SIGN_RND
    class adamsbridge_reg__ADAMSBRIDGE_SIGN_RND extends uvm_reg;
        rand uvm_reg_field SIGN_RND;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_SIGN_RND");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SIGN_RND = new("SIGN_RND");
            this.SIGN_RND.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_SIGN_RND

    // Reg - adamsbridge_reg::ADAMSBRIDGE_MSG
    class adamsbridge_reg__ADAMSBRIDGE_MSG extends uvm_reg;
        rand uvm_reg_field MSG;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_MSG");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.MSG = new("MSG");
            this.MSG.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_MSG

    // Reg - adamsbridge_reg::ADAMSBRIDGE_VERIFY_RES
    class adamsbridge_reg__ADAMSBRIDGE_VERIFY_RES extends uvm_reg;
        rand uvm_reg_field VERIFY_RES;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_VERIFY_RES");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.VERIFY_RES = new("VERIFY_RES");
            this.VERIFY_RES.configure(this, 32, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_VERIFY_RES

    // Reg - adamsbridge_reg::ADAMSBRIDGE_PUBKEY
    class adamsbridge_reg__ADAMSBRIDGE_PUBKEY extends uvm_reg;
        rand uvm_reg_field PUBKEY;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_PUBKEY");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.PUBKEY = new("PUBKEY");
            this.PUBKEY.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_PUBKEY

    // Reg - adamsbridge_reg::ADAMSBRIDGE_SIGNATURE
    class adamsbridge_reg__ADAMSBRIDGE_SIGNATURE extends uvm_reg;
        rand uvm_reg_field SIGNATURE;

        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_SIGNATURE");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SIGNATURE = new("SIGNATURE");
            this.SIGNATURE.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_SIGNATURE

    // Mem - adamsbridge_reg::ADAMSBRIDGE_PRIVKEY_OUT
    class adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_OUT extends uvm_reg_block;
        rand uvm_mem m_mem;
        
        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_OUT");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4.0, UVM_NO_ENDIAN);
            this.m_mem = new("m_mem", 1224, 32, "RW");
            this.m_mem.configure(this);
            this.default_map.add_mem(this.m_mem, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_OUT

    // Mem - adamsbridge_reg::ADAMSBRIDGE_PRIVKEY_IN
    class adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_IN extends uvm_reg_block;
        rand uvm_mem m_mem;
        
        function new(string name = "adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_IN");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4.0, UVM_NO_ENDIAN);
            this.m_mem = new("m_mem", 1224, 32, "RW");
            this.m_mem.configure(this);
            this.default_map.add_mem(this.m_mem, 0);
        endfunction : build
    endclass : adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_IN

    // Reg - adamsbridge_reg::intr_block_t::global_intr_en_t
    class adamsbridge_reg__intr_block_t__global_intr_en_t extends uvm_reg;
        rand uvm_reg_field error_en;
        rand uvm_reg_field notif_en;

        function new(string name = "adamsbridge_reg__intr_block_t__global_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_en = new("error_en");
            this.error_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
            this.notif_en = new("notif_en");
            this.notif_en.configure(this, 1, 1, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__global_intr_en_t

    // Reg - adamsbridge_reg::intr_block_t::error_intr_en_t
    class adamsbridge_reg__intr_block_t__error_intr_en_t extends uvm_reg;
        rand uvm_reg_field error_internal_en;

        function new(string name = "adamsbridge_reg__intr_block_t__error_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_en = new("error_internal_en");
            this.error_internal_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__error_intr_en_t

    // Reg - adamsbridge_reg::intr_block_t::notif_intr_en_t
    class adamsbridge_reg__intr_block_t__notif_intr_en_t extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_en;

        function new(string name = "adamsbridge_reg__intr_block_t__notif_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_en = new("notif_cmd_done_en");
            this.notif_cmd_done_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__notif_intr_en_t

    // Reg - adamsbridge_reg::intr_block_t::global_intr_t_agg_sts_dd3dcf0a
    class adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a extends uvm_reg;
        rand uvm_reg_field agg_sts;

        function new(string name = "adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.agg_sts = new("agg_sts");
            this.agg_sts.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a

    // Reg - adamsbridge_reg::intr_block_t::global_intr_t_agg_sts_e6399b4a
    class adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a extends uvm_reg;
        rand uvm_reg_field agg_sts;

        function new(string name = "adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.agg_sts = new("agg_sts");
            this.agg_sts.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a

    // Reg - adamsbridge_reg::intr_block_t::error_intr_t_error_internal_sts_83adab02
    class adamsbridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02 extends uvm_reg;
        rand uvm_reg_field error_internal_sts;

        function new(string name = "adamsbridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_sts = new("error_internal_sts");
            this.error_internal_sts.configure(this, 1, 0, "W1C", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02

    // Reg - adamsbridge_reg::intr_block_t::notif_intr_t_notif_cmd_done_sts_1c68637e
    class adamsbridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_sts;

        function new(string name = "adamsbridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_sts = new("notif_cmd_done_sts");
            this.notif_cmd_done_sts.configure(this, 1, 0, "W1C", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e

    // Reg - adamsbridge_reg::intr_block_t::error_intr_trig_t
    class adamsbridge_reg__intr_block_t__error_intr_trig_t extends uvm_reg;
        rand uvm_reg_field error_internal_trig;

        function new(string name = "adamsbridge_reg__intr_block_t__error_intr_trig_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_trig = new("error_internal_trig");
            this.error_internal_trig.configure(this, 1, 0, "W1S", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__error_intr_trig_t

    // Reg - adamsbridge_reg::intr_block_t::notif_intr_trig_t
    class adamsbridge_reg__intr_block_t__notif_intr_trig_t extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_trig;

        function new(string name = "adamsbridge_reg__intr_block_t__notif_intr_trig_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_trig = new("notif_cmd_done_trig");
            this.notif_cmd_done_trig.configure(this, 1, 0, "W1S", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__notif_intr_trig_t

    // Reg - adamsbridge_reg::intr_block_t::intr_count_t_cnt_60ddff93
    class adamsbridge_reg__intr_block_t__intr_count_t_cnt_60ddff93 extends uvm_reg;
        rand uvm_reg_field cnt;

        function new(string name = "adamsbridge_reg__intr_block_t__intr_count_t_cnt_60ddff93");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.cnt = new("cnt");
            this.cnt.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__intr_count_t_cnt_60ddff93

    // Reg - adamsbridge_reg::intr_block_t::intr_count_t_cnt_be67d6d5
    class adamsbridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5 extends uvm_reg;
        rand uvm_reg_field cnt;

        function new(string name = "adamsbridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.cnt = new("cnt");
            this.cnt.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5

    // Reg - adamsbridge_reg::intr_block_t::intr_count_incr_t_pulse_15e6ed7e
    class adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e extends uvm_reg;
        rand uvm_reg_field pulse;

        function new(string name = "adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.pulse = new("pulse");
            this.pulse.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e

    // Reg - adamsbridge_reg::intr_block_t::intr_count_incr_t_pulse_6173128e
    class adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e extends uvm_reg;
        rand uvm_reg_field pulse;

        function new(string name = "adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.pulse = new("pulse");
            this.pulse.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e

    // Regfile - adamsbridge_reg::intr_block_t
    class adamsbridge_reg__intr_block_t extends uvm_reg_block;
        rand adamsbridge_reg__intr_block_t__global_intr_en_t global_intr_en_r;
        rand adamsbridge_reg__intr_block_t__error_intr_en_t error_intr_en_r;
        rand adamsbridge_reg__intr_block_t__notif_intr_en_t notif_intr_en_r;
        rand adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a error_global_intr_r;
        rand adamsbridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a notif_global_intr_r;
        rand adamsbridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02 error_internal_intr_r;
        rand adamsbridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e notif_internal_intr_r;
        rand adamsbridge_reg__intr_block_t__error_intr_trig_t error_intr_trig_r;
        rand adamsbridge_reg__intr_block_t__notif_intr_trig_t notif_intr_trig_r;
        rand adamsbridge_reg__intr_block_t__intr_count_t_cnt_60ddff93 error_internal_intr_count_r;
        rand adamsbridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5 notif_cmd_done_intr_count_r;
        rand adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e error_internal_intr_count_incr_r;
        rand adamsbridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e notif_cmd_done_intr_count_incr_r;

        function new(string name = "adamsbridge_reg__intr_block_t");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4, UVM_NO_ENDIAN);
            this.global_intr_en_r = new("global_intr_en_r");
            this.global_intr_en_r.configure(this);

            this.global_intr_en_r.build();
            this.default_map.add_reg(this.global_intr_en_r, 'h0);
            this.error_intr_en_r = new("error_intr_en_r");
            this.error_intr_en_r.configure(this);

            this.error_intr_en_r.build();
            this.default_map.add_reg(this.error_intr_en_r, 'h4);
            this.notif_intr_en_r = new("notif_intr_en_r");
            this.notif_intr_en_r.configure(this);

            this.notif_intr_en_r.build();
            this.default_map.add_reg(this.notif_intr_en_r, 'h8);
            this.error_global_intr_r = new("error_global_intr_r");
            this.error_global_intr_r.configure(this);

            this.error_global_intr_r.build();
            this.default_map.add_reg(this.error_global_intr_r, 'hc);
            this.notif_global_intr_r = new("notif_global_intr_r");
            this.notif_global_intr_r.configure(this);

            this.notif_global_intr_r.build();
            this.default_map.add_reg(this.notif_global_intr_r, 'h10);
            this.error_internal_intr_r = new("error_internal_intr_r");
            this.error_internal_intr_r.configure(this);

            this.error_internal_intr_r.build();
            this.default_map.add_reg(this.error_internal_intr_r, 'h14);
            this.notif_internal_intr_r = new("notif_internal_intr_r");
            this.notif_internal_intr_r.configure(this);

            this.notif_internal_intr_r.build();
            this.default_map.add_reg(this.notif_internal_intr_r, 'h18);
            this.error_intr_trig_r = new("error_intr_trig_r");
            this.error_intr_trig_r.configure(this);

            this.error_intr_trig_r.build();
            this.default_map.add_reg(this.error_intr_trig_r, 'h1c);
            this.notif_intr_trig_r = new("notif_intr_trig_r");
            this.notif_intr_trig_r.configure(this);

            this.notif_intr_trig_r.build();
            this.default_map.add_reg(this.notif_intr_trig_r, 'h20);
            this.error_internal_intr_count_r = new("error_internal_intr_count_r");
            this.error_internal_intr_count_r.configure(this);

            this.error_internal_intr_count_r.build();
            this.default_map.add_reg(this.error_internal_intr_count_r, 'h100);
            this.notif_cmd_done_intr_count_r = new("notif_cmd_done_intr_count_r");
            this.notif_cmd_done_intr_count_r.configure(this);

            this.notif_cmd_done_intr_count_r.build();
            this.default_map.add_reg(this.notif_cmd_done_intr_count_r, 'h180);
            this.error_internal_intr_count_incr_r = new("error_internal_intr_count_incr_r");
            this.error_internal_intr_count_incr_r.configure(this);

            this.error_internal_intr_count_incr_r.build();
            this.default_map.add_reg(this.error_internal_intr_count_incr_r, 'h200);
            this.notif_cmd_done_intr_count_incr_r = new("notif_cmd_done_intr_count_incr_r");
            this.notif_cmd_done_intr_count_incr_r.configure(this);

            this.notif_cmd_done_intr_count_incr_r.build();
            this.default_map.add_reg(this.notif_cmd_done_intr_count_incr_r, 'h204);
        endfunction : build
    endclass : adamsbridge_reg__intr_block_t

    // Addrmap - adamsbridge_reg
    class adamsbridge_reg extends uvm_reg_block;
        rand adamsbridge_reg__ADAMSBRIDGE_NAME ADAMSBRIDGE_NAME[2];
        rand adamsbridge_reg__ADAMSBRIDGE_VERSION ADAMSBRIDGE_VERSION[2];
        rand adamsbridge_reg__ADAMSBRIDGE_CTRL ADAMSBRIDGE_CTRL;
        rand adamsbridge_reg__ADAMSBRIDGE_STATUS ADAMSBRIDGE_STATUS;
        rand adamsbridge_reg__ADAMSBRIDGE_IV ADAMSBRIDGE_IV[16];
        rand adamsbridge_reg__ADAMSBRIDGE_SEED ADAMSBRIDGE_SEED[8];
        rand adamsbridge_reg__ADAMSBRIDGE_SIGN_RND ADAMSBRIDGE_SIGN_RND[8];
        rand adamsbridge_reg__ADAMSBRIDGE_MSG ADAMSBRIDGE_MSG[16];
        rand adamsbridge_reg__ADAMSBRIDGE_VERIFY_RES ADAMSBRIDGE_VERIFY_RES[16];
        rand adamsbridge_reg__ADAMSBRIDGE_PUBKEY ADAMSBRIDGE_PUBKEY[648];
        rand adamsbridge_reg__ADAMSBRIDGE_SIGNATURE ADAMSBRIDGE_SIGNATURE[1157];
        rand adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_OUT ADAMSBRIDGE_PRIVKEY_OUT;
        rand adamsbridge_reg__ADAMSBRIDGE_PRIVKEY_IN ADAMSBRIDGE_PRIVKEY_IN;
        rand adamsbridge_reg__intr_block_t intr_block_rf;

        function new(string name = "adamsbridge_reg");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4, UVM_NO_ENDIAN);
            foreach(this.ADAMSBRIDGE_NAME[i0]) begin
                this.ADAMSBRIDGE_NAME[i0] = new($sformatf("ADAMSBRIDGE_NAME[%0d]", i0));
                this.ADAMSBRIDGE_NAME[i0].configure(this);
                
                this.ADAMSBRIDGE_NAME[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_NAME[i0], 'h0 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_VERSION[i0]) begin
                this.ADAMSBRIDGE_VERSION[i0] = new($sformatf("ADAMSBRIDGE_VERSION[%0d]", i0));
                this.ADAMSBRIDGE_VERSION[i0].configure(this);
                
                this.ADAMSBRIDGE_VERSION[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_VERSION[i0], 'h8 + i0*'h4);
            end
            this.ADAMSBRIDGE_CTRL = new("ADAMSBRIDGE_CTRL");
            this.ADAMSBRIDGE_CTRL.configure(this);

            this.ADAMSBRIDGE_CTRL.build();
            this.default_map.add_reg(this.ADAMSBRIDGE_CTRL, 'h10);
            this.ADAMSBRIDGE_STATUS = new("ADAMSBRIDGE_STATUS");
            this.ADAMSBRIDGE_STATUS.configure(this);

            this.ADAMSBRIDGE_STATUS.build();
            this.default_map.add_reg(this.ADAMSBRIDGE_STATUS, 'h18);
            foreach(this.ADAMSBRIDGE_IV[i0]) begin
                this.ADAMSBRIDGE_IV[i0] = new($sformatf("ADAMSBRIDGE_IV[%0d]", i0));
                this.ADAMSBRIDGE_IV[i0].configure(this);
                
                this.ADAMSBRIDGE_IV[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_IV[i0], 'h80 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_SEED[i0]) begin
                this.ADAMSBRIDGE_SEED[i0] = new($sformatf("ADAMSBRIDGE_SEED[%0d]", i0));
                this.ADAMSBRIDGE_SEED[i0].configure(this);
                
                this.ADAMSBRIDGE_SEED[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_SEED[i0], 'h100 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_SIGN_RND[i0]) begin
                this.ADAMSBRIDGE_SIGN_RND[i0] = new($sformatf("ADAMSBRIDGE_SIGN_RND[%0d]", i0));
                this.ADAMSBRIDGE_SIGN_RND[i0].configure(this);
                
                this.ADAMSBRIDGE_SIGN_RND[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_SIGN_RND[i0], 'h180 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_MSG[i0]) begin
                this.ADAMSBRIDGE_MSG[i0] = new($sformatf("ADAMSBRIDGE_MSG[%0d]", i0));
                this.ADAMSBRIDGE_MSG[i0].configure(this);
                
                this.ADAMSBRIDGE_MSG[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_MSG[i0], 'h200 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_VERIFY_RES[i0]) begin
                this.ADAMSBRIDGE_VERIFY_RES[i0] = new($sformatf("ADAMSBRIDGE_VERIFY_RES[%0d]", i0));
                this.ADAMSBRIDGE_VERIFY_RES[i0].configure(this);
                
                this.ADAMSBRIDGE_VERIFY_RES[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_VERIFY_RES[i0], 'h280 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_PUBKEY[i0]) begin
                this.ADAMSBRIDGE_PUBKEY[i0] = new($sformatf("ADAMSBRIDGE_PUBKEY[%0d]", i0));
                this.ADAMSBRIDGE_PUBKEY[i0].configure(this);
                
                this.ADAMSBRIDGE_PUBKEY[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_PUBKEY[i0], 'h2c0 + i0*'h4);
            end
            foreach(this.ADAMSBRIDGE_SIGNATURE[i0]) begin
                this.ADAMSBRIDGE_SIGNATURE[i0] = new($sformatf("ADAMSBRIDGE_SIGNATURE[%0d]", i0));
                this.ADAMSBRIDGE_SIGNATURE[i0].configure(this);
                
                this.ADAMSBRIDGE_SIGNATURE[i0].build();
                this.default_map.add_reg(this.ADAMSBRIDGE_SIGNATURE[i0], 'hce0 + i0*'h4);
            end
            this.ADAMSBRIDGE_PRIVKEY_OUT = new("ADAMSBRIDGE_PRIVKEY_OUT");
            this.ADAMSBRIDGE_PRIVKEY_OUT.configure(this);
            this.ADAMSBRIDGE_PRIVKEY_OUT.build();
            this.default_map.add_submap(this.ADAMSBRIDGE_PRIVKEY_OUT.default_map, 'h2000);
            this.ADAMSBRIDGE_PRIVKEY_IN = new("ADAMSBRIDGE_PRIVKEY_IN");
            this.ADAMSBRIDGE_PRIVKEY_IN.configure(this);
            this.ADAMSBRIDGE_PRIVKEY_IN.build();
            this.default_map.add_submap(this.ADAMSBRIDGE_PRIVKEY_IN.default_map, 'h4000);
            this.intr_block_rf = new("intr_block_rf");
            this.intr_block_rf.configure(this);
            this.intr_block_rf.build();
            this.default_map.add_submap(this.intr_block_rf.default_map, 'h6000);
        endfunction : build
    endclass : adamsbridge_reg

endpackage: adamsbridge_reg_uvm
