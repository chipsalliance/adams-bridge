
// This file was autogenerated by PeakRDL-uvm
package adams_bridge_reg_uvm;
    `include "uvm_macros.svh"
    import uvm_pkg::*;
    
    // Reg - adams_bridge_reg::ADAMS_BRIDGE_NAME
    class adams_bridge_reg__ADAMS_BRIDGE_NAME extends uvm_reg;
        rand uvm_reg_field NAME;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_NAME");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.NAME = new("NAME");
            this.NAME.configure(this, 32, 0, "RO", 1, 'h0, 0, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_NAME

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_VERSION
    class adams_bridge_reg__ADAMS_BRIDGE_VERSION extends uvm_reg;
        rand uvm_reg_field VERSION;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_VERSION");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.VERSION = new("VERSION");
            this.VERSION.configure(this, 32, 0, "RO", 1, 'h0, 0, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_VERSION

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_CTRL
    class adams_bridge_reg__ADAMS_BRIDGE_CTRL extends uvm_reg;
        rand uvm_reg_field CTRL;
        rand uvm_reg_field ZEROIZE;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_CTRL");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.CTRL = new("CTRL");
            this.CTRL.configure(this, 2, 0, "WO", 1, 'h0, 1, 1, 0);
            this.ZEROIZE = new("ZEROIZE");
            this.ZEROIZE.configure(this, 1, 2, "WO", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_CTRL

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_STATUS
    class adams_bridge_reg__ADAMS_BRIDGE_STATUS extends uvm_reg;
        rand uvm_reg_field READY;
        rand uvm_reg_field VALID;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_STATUS");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.READY = new("READY");
            this.READY.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
            this.VALID = new("VALID");
            this.VALID.configure(this, 1, 1, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_STATUS

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_IV
    class adams_bridge_reg__ADAMS_BRIDGE_IV extends uvm_reg;
        rand uvm_reg_field IV;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_IV");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.IV = new("IV");
            this.IV.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_IV

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_SEED
    class adams_bridge_reg__ADAMS_BRIDGE_SEED extends uvm_reg;
        rand uvm_reg_field SEED;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_SEED");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SEED = new("SEED");
            this.SEED.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_SEED

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_SIGN_RND
    class adams_bridge_reg__ADAMS_BRIDGE_SIGN_RND extends uvm_reg;
        rand uvm_reg_field SIGN_RND;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_SIGN_RND");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SIGN_RND = new("SIGN_RND");
            this.SIGN_RND.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_SIGN_RND

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_MSG
    class adams_bridge_reg__ADAMS_BRIDGE_MSG extends uvm_reg;
        rand uvm_reg_field MSG;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_MSG");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.MSG = new("MSG");
            this.MSG.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_MSG

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_VERIFY_RES
    class adams_bridge_reg__ADAMS_BRIDGE_VERIFY_RES extends uvm_reg;
        rand uvm_reg_field VERIFY_RES;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_VERIFY_RES");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.VERIFY_RES = new("VERIFY_RES");
            this.VERIFY_RES.configure(this, 32, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_VERIFY_RES

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_PRIVKEY_OUT
    class adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_OUT extends uvm_reg;
        rand uvm_reg_field PRIVKEY_OUT;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_OUT");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.PRIVKEY_OUT = new("PRIVKEY_OUT");
            this.PRIVKEY_OUT.configure(this, 32, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_OUT

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_PRIVKEY_IN
    class adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_IN extends uvm_reg;
        rand uvm_reg_field PRIVKEY_IN;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_IN");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.PRIVKEY_IN = new("PRIVKEY_IN");
            this.PRIVKEY_IN.configure(this, 32, 0, "WO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_IN

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_PUBKEY
    class adams_bridge_reg__ADAMS_BRIDGE_PUBKEY extends uvm_reg;
        rand uvm_reg_field PUBKEY;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_PUBKEY");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.PUBKEY = new("PUBKEY");
            this.PUBKEY.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_PUBKEY

    // Reg - adams_bridge_reg::ADAMS_BRIDGE_SIGNATURE
    class adams_bridge_reg__ADAMS_BRIDGE_SIGNATURE extends uvm_reg;
        rand uvm_reg_field SIGNATURE;

        function new(string name = "adams_bridge_reg__ADAMS_BRIDGE_SIGNATURE");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.SIGNATURE = new("SIGNATURE");
            this.SIGNATURE.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__ADAMS_BRIDGE_SIGNATURE

    // Reg - adams_bridge_reg::intr_block_t::global_intr_en_t
    class adams_bridge_reg__intr_block_t__global_intr_en_t extends uvm_reg;
        rand uvm_reg_field error_en;
        rand uvm_reg_field notif_en;

        function new(string name = "adams_bridge_reg__intr_block_t__global_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_en = new("error_en");
            this.error_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
            this.notif_en = new("notif_en");
            this.notif_en.configure(this, 1, 1, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__global_intr_en_t

    // Reg - adams_bridge_reg::intr_block_t::error_intr_en_t
    class adams_bridge_reg__intr_block_t__error_intr_en_t extends uvm_reg;
        rand uvm_reg_field error_internal_en;

        function new(string name = "adams_bridge_reg__intr_block_t__error_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_en = new("error_internal_en");
            this.error_internal_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__error_intr_en_t

    // Reg - adams_bridge_reg::intr_block_t::notif_intr_en_t
    class adams_bridge_reg__intr_block_t__notif_intr_en_t extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_en;

        function new(string name = "adams_bridge_reg__intr_block_t__notif_intr_en_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_en = new("notif_cmd_done_en");
            this.notif_cmd_done_en.configure(this, 1, 0, "RW", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__notif_intr_en_t

    // Reg - adams_bridge_reg::intr_block_t::global_intr_t_agg_sts_dd3dcf0a
    class adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a extends uvm_reg;
        rand uvm_reg_field agg_sts;

        function new(string name = "adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.agg_sts = new("agg_sts");
            this.agg_sts.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a

    // Reg - adams_bridge_reg::intr_block_t::global_intr_t_agg_sts_e6399b4a
    class adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a extends uvm_reg;
        rand uvm_reg_field agg_sts;

        function new(string name = "adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.agg_sts = new("agg_sts");
            this.agg_sts.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a

    // Reg - adams_bridge_reg::intr_block_t::error_intr_t_error_internal_sts_83adab02
    class adams_bridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02 extends uvm_reg;
        rand uvm_reg_field error_internal_sts;

        function new(string name = "adams_bridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_sts = new("error_internal_sts");
            this.error_internal_sts.configure(this, 1, 0, "W1C", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02

    // Reg - adams_bridge_reg::intr_block_t::notif_intr_t_notif_cmd_done_sts_1c68637e
    class adams_bridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_sts;

        function new(string name = "adams_bridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_sts = new("notif_cmd_done_sts");
            this.notif_cmd_done_sts.configure(this, 1, 0, "W1C", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e

    // Reg - adams_bridge_reg::intr_block_t::error_intr_trig_t
    class adams_bridge_reg__intr_block_t__error_intr_trig_t extends uvm_reg;
        rand uvm_reg_field error_internal_trig;

        function new(string name = "adams_bridge_reg__intr_block_t__error_intr_trig_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.error_internal_trig = new("error_internal_trig");
            this.error_internal_trig.configure(this, 1, 0, "W1S", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__error_intr_trig_t

    // Reg - adams_bridge_reg::intr_block_t::notif_intr_trig_t
    class adams_bridge_reg__intr_block_t__notif_intr_trig_t extends uvm_reg;
        rand uvm_reg_field notif_cmd_done_trig;

        function new(string name = "adams_bridge_reg__intr_block_t__notif_intr_trig_t");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.notif_cmd_done_trig = new("notif_cmd_done_trig");
            this.notif_cmd_done_trig.configure(this, 1, 0, "W1S", 0, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__notif_intr_trig_t

    // Reg - adams_bridge_reg::intr_block_t::intr_count_t_cnt_60ddff93
    class adams_bridge_reg__intr_block_t__intr_count_t_cnt_60ddff93 extends uvm_reg;
        rand uvm_reg_field cnt;

        function new(string name = "adams_bridge_reg__intr_block_t__intr_count_t_cnt_60ddff93");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.cnt = new("cnt");
            this.cnt.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__intr_count_t_cnt_60ddff93

    // Reg - adams_bridge_reg::intr_block_t::intr_count_t_cnt_be67d6d5
    class adams_bridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5 extends uvm_reg;
        rand uvm_reg_field cnt;

        function new(string name = "adams_bridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.cnt = new("cnt");
            this.cnt.configure(this, 32, 0, "RW", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5

    // Reg - adams_bridge_reg::intr_block_t::intr_count_incr_t_pulse_15e6ed7e
    class adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e extends uvm_reg;
        rand uvm_reg_field pulse;

        function new(string name = "adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.pulse = new("pulse");
            this.pulse.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e

    // Reg - adams_bridge_reg::intr_block_t::intr_count_incr_t_pulse_6173128e
    class adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e extends uvm_reg;
        rand uvm_reg_field pulse;

        function new(string name = "adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e");
            super.new(name, 32, UVM_NO_COVERAGE);
        endfunction : new

        virtual function void build();
            this.pulse = new("pulse");
            this.pulse.configure(this, 1, 0, "RO", 1, 'h0, 1, 1, 0);
        endfunction : build
    endclass : adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e

    // Regfile - adams_bridge_reg::intr_block_t
    class adams_bridge_reg__intr_block_t extends uvm_reg_block;
        rand adams_bridge_reg__intr_block_t__global_intr_en_t global_intr_en_r;
        rand adams_bridge_reg__intr_block_t__error_intr_en_t error_intr_en_r;
        rand adams_bridge_reg__intr_block_t__notif_intr_en_t notif_intr_en_r;
        rand adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a error_global_intr_r;
        rand adams_bridge_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a notif_global_intr_r;
        rand adams_bridge_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02 error_internal_intr_r;
        rand adams_bridge_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e notif_internal_intr_r;
        rand adams_bridge_reg__intr_block_t__error_intr_trig_t error_intr_trig_r;
        rand adams_bridge_reg__intr_block_t__notif_intr_trig_t notif_intr_trig_r;
        rand adams_bridge_reg__intr_block_t__intr_count_t_cnt_60ddff93 error_internal_intr_count_r;
        rand adams_bridge_reg__intr_block_t__intr_count_t_cnt_be67d6d5 notif_cmd_done_intr_count_r;
        rand adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e error_internal_intr_count_incr_r;
        rand adams_bridge_reg__intr_block_t__intr_count_incr_t_pulse_6173128e notif_cmd_done_intr_count_incr_r;

        function new(string name = "adams_bridge_reg__intr_block_t");
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
    endclass : adams_bridge_reg__intr_block_t

    // Addrmap - adams_bridge_reg
    class adams_bridge_reg extends uvm_reg_block;
        rand adams_bridge_reg__ADAMS_BRIDGE_NAME ADAMS_BRIDGE_NAME[2];
        rand adams_bridge_reg__ADAMS_BRIDGE_VERSION ADAMS_BRIDGE_VERSION[2];
        rand adams_bridge_reg__ADAMS_BRIDGE_CTRL ADAMS_BRIDGE_CTRL;
        rand adams_bridge_reg__ADAMS_BRIDGE_STATUS ADAMS_BRIDGE_STATUS;
        rand adams_bridge_reg__ADAMS_BRIDGE_IV ADAMS_BRIDGE_IV[16];
        rand adams_bridge_reg__ADAMS_BRIDGE_SEED ADAMS_BRIDGE_SEED[8];
        rand adams_bridge_reg__ADAMS_BRIDGE_SIGN_RND ADAMS_BRIDGE_SIGN_RND[8];
        rand adams_bridge_reg__ADAMS_BRIDGE_MSG ADAMS_BRIDGE_MSG[16];
        rand adams_bridge_reg__ADAMS_BRIDGE_VERIFY_RES ADAMS_BRIDGE_VERIFY_RES[16];
        rand adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_OUT ADAMS_BRIDGE_PRIVKEY_OUT[1216];
        rand adams_bridge_reg__ADAMS_BRIDGE_PRIVKEY_IN ADAMS_BRIDGE_PRIVKEY_IN[1216];
        rand adams_bridge_reg__ADAMS_BRIDGE_PUBKEY ADAMS_BRIDGE_PUBKEY[648];
        rand adams_bridge_reg__ADAMS_BRIDGE_SIGNATURE ADAMS_BRIDGE_SIGNATURE[1149];
        rand adams_bridge_reg__intr_block_t intr_block_rf;

        function new(string name = "adams_bridge_reg");
            super.new(name);
        endfunction : new

        virtual function void build();
            this.default_map = create_map("reg_map", 0, 4, UVM_NO_ENDIAN);
            foreach(this.ADAMS_BRIDGE_NAME[i0]) begin
                this.ADAMS_BRIDGE_NAME[i0] = new($sformatf("ADAMS_BRIDGE_NAME[%0d]", i0));
                this.ADAMS_BRIDGE_NAME[i0].configure(this);
                
                this.ADAMS_BRIDGE_NAME[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_NAME[i0], 'h0 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_VERSION[i0]) begin
                this.ADAMS_BRIDGE_VERSION[i0] = new($sformatf("ADAMS_BRIDGE_VERSION[%0d]", i0));
                this.ADAMS_BRIDGE_VERSION[i0].configure(this);
                
                this.ADAMS_BRIDGE_VERSION[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_VERSION[i0], 'h8 + i0*'h4);
            end
            this.ADAMS_BRIDGE_CTRL = new("ADAMS_BRIDGE_CTRL");
            this.ADAMS_BRIDGE_CTRL.configure(this);

            this.ADAMS_BRIDGE_CTRL.build();
            this.default_map.add_reg(this.ADAMS_BRIDGE_CTRL, 'h10);
            this.ADAMS_BRIDGE_STATUS = new("ADAMS_BRIDGE_STATUS");
            this.ADAMS_BRIDGE_STATUS.configure(this);

            this.ADAMS_BRIDGE_STATUS.build();
            this.default_map.add_reg(this.ADAMS_BRIDGE_STATUS, 'h18);
            foreach(this.ADAMS_BRIDGE_IV[i0]) begin
                this.ADAMS_BRIDGE_IV[i0] = new($sformatf("ADAMS_BRIDGE_IV[%0d]", i0));
                this.ADAMS_BRIDGE_IV[i0].configure(this);
                
                this.ADAMS_BRIDGE_IV[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_IV[i0], 'h80 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_SEED[i0]) begin
                this.ADAMS_BRIDGE_SEED[i0] = new($sformatf("ADAMS_BRIDGE_SEED[%0d]", i0));
                this.ADAMS_BRIDGE_SEED[i0].configure(this);
                
                this.ADAMS_BRIDGE_SEED[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_SEED[i0], 'h100 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_SIGN_RND[i0]) begin
                this.ADAMS_BRIDGE_SIGN_RND[i0] = new($sformatf("ADAMS_BRIDGE_SIGN_RND[%0d]", i0));
                this.ADAMS_BRIDGE_SIGN_RND[i0].configure(this);
                
                this.ADAMS_BRIDGE_SIGN_RND[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_SIGN_RND[i0], 'h180 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_MSG[i0]) begin
                this.ADAMS_BRIDGE_MSG[i0] = new($sformatf("ADAMS_BRIDGE_MSG[%0d]", i0));
                this.ADAMS_BRIDGE_MSG[i0].configure(this);
                
                this.ADAMS_BRIDGE_MSG[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_MSG[i0], 'h200 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_VERIFY_RES[i0]) begin
                this.ADAMS_BRIDGE_VERIFY_RES[i0] = new($sformatf("ADAMS_BRIDGE_VERIFY_RES[%0d]", i0));
                this.ADAMS_BRIDGE_VERIFY_RES[i0].configure(this);
                
                this.ADAMS_BRIDGE_VERIFY_RES[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_VERIFY_RES[i0], 'h280 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_PRIVKEY_OUT[i0]) begin
                this.ADAMS_BRIDGE_PRIVKEY_OUT[i0] = new($sformatf("ADAMS_BRIDGE_PRIVKEY_OUT[%0d]", i0));
                this.ADAMS_BRIDGE_PRIVKEY_OUT[i0].configure(this);
                
                this.ADAMS_BRIDGE_PRIVKEY_OUT[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_PRIVKEY_OUT[i0], 'h300 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_PRIVKEY_IN[i0]) begin
                this.ADAMS_BRIDGE_PRIVKEY_IN[i0] = new($sformatf("ADAMS_BRIDGE_PRIVKEY_IN[%0d]", i0));
                this.ADAMS_BRIDGE_PRIVKEY_IN[i0].configure(this);
                
                this.ADAMS_BRIDGE_PRIVKEY_IN[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_PRIVKEY_IN[i0], 'h1600 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_PUBKEY[i0]) begin
                this.ADAMS_BRIDGE_PUBKEY[i0] = new($sformatf("ADAMS_BRIDGE_PUBKEY[%0d]", i0));
                this.ADAMS_BRIDGE_PUBKEY[i0].configure(this);
                
                this.ADAMS_BRIDGE_PUBKEY[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_PUBKEY[i0], 'h2900 + i0*'h4);
            end
            foreach(this.ADAMS_BRIDGE_SIGNATURE[i0]) begin
                this.ADAMS_BRIDGE_SIGNATURE[i0] = new($sformatf("ADAMS_BRIDGE_SIGNATURE[%0d]", i0));
                this.ADAMS_BRIDGE_SIGNATURE[i0].configure(this);
                
                this.ADAMS_BRIDGE_SIGNATURE[i0].build();
                this.default_map.add_reg(this.ADAMS_BRIDGE_SIGNATURE[i0], 'h3400 + i0*'h4);
            end
            this.intr_block_rf = new("intr_block_rf");
            this.intr_block_rf.configure(this);
            this.intr_block_rf.build();
            this.default_map.add_submap(this.intr_block_rf.default_map, 'h4600);
        endfunction : build
    endclass : adams_bridge_reg

endpackage: adams_bridge_reg_uvm
