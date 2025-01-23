// Generated by PeakRDL-regblock - A free and open-source SystemVerilog generator
//  https://github.com/SystemRDL/PeakRDL-regblock

package mldsa_reg_pkg;

    localparam MLDSA_REG_DATA_WIDTH = 32;
    localparam MLDSA_REG_MIN_ADDR_WIDTH = 16;

    typedef struct packed{
        logic [31:0] next;
    } mldsa_reg__MLDSA_NAME__NAME__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_NAME__NAME__in_t NAME;
    } mldsa_reg__MLDSA_NAME__in_t;

    typedef struct packed{
        logic [31:0] next;
    } mldsa_reg__MLDSA_VERSION__VERSION__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_VERSION__VERSION__in_t VERSION;
    } mldsa_reg__MLDSA_VERSION__in_t;

    typedef struct packed{
        logic hwclr;
    } mldsa_reg__MLDSA_CTRL__CTRL__in_t;

    typedef struct packed{
        logic hwclr;
    } mldsa_reg__MLDSA_CTRL__PCR_SIGN__in_t;

    typedef struct packed{
        logic hwclr;
    } mldsa_reg__MLDSA_CTRL__EXTERNAL_MU__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_CTRL__CTRL__in_t CTRL;
        mldsa_reg__MLDSA_CTRL__PCR_SIGN__in_t PCR_SIGN;
        mldsa_reg__MLDSA_CTRL__EXTERNAL_MU__in_t EXTERNAL_MU;
    } mldsa_reg__MLDSA_CTRL__in_t;

    typedef struct packed{
        logic next;
    } mldsa_reg__MLDSA_STATUS__READY__in_t;

    typedef struct packed{
        logic next;
    } mldsa_reg__MLDSA_STATUS__VALID__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_STATUS__READY__in_t READY;
        mldsa_reg__MLDSA_STATUS__VALID__in_t VALID;
    } mldsa_reg__MLDSA_STATUS__in_t;

    typedef struct packed{
        logic hwclr;
    } mldsa_reg__MLDSA_ENTROPY__ENTROPY__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_ENTROPY__ENTROPY__in_t ENTROPY;
    } mldsa_reg__MLDSA_ENTROPY__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
        logic swwe;
        logic hwclr;
    } mldsa_reg__MLDSA_SEED__SEED__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_SEED__SEED__in_t SEED;
    } mldsa_reg__MLDSA_SEED__in_t;

    typedef struct packed{
        logic hwclr;
    } mldsa_reg__MLDSA_SIGN_RND__SIGN_RND__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_SIGN_RND__SIGN_RND__in_t SIGN_RND;
    } mldsa_reg__MLDSA_SIGN_RND__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
        logic hwclr;
    } mldsa_reg__MLDSA_MSG__MSG__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_MSG__MSG__in_t MSG;
    } mldsa_reg__MLDSA_MSG__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
        logic hwclr;
    } mldsa_reg__MLDSA_VERIFY_RES__VERIFY_RES__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_VERIFY_RES__VERIFY_RES__in_t VERIFY_RES;
    } mldsa_reg__MLDSA_VERIFY_RES__in_t;

    typedef struct packed{
        logic [31:0] next;
        logic we;
        logic hwclr;
    } mldsa_reg__MLDSA_EXTERNAL_MU__EXTERNAL_MU__in_t;

    typedef struct packed{
        mldsa_reg__MLDSA_EXTERNAL_MU__EXTERNAL_MU__in_t EXTERNAL_MU;
    } mldsa_reg__MLDSA_EXTERNAL_MU__in_t;

    typedef struct packed{
        logic rd_ack;
        logic [31:0] rd_data;
        logic wr_ack;
    } mldsa_reg__MLDSA_PUBKEY__external__in_t;

    typedef struct packed{
        logic rd_ack;
        logic [31:0] rd_data;
        logic wr_ack;
    } mldsa_reg__MLDSA_SIGNATURE__external__in_t;

    typedef struct packed{
        logic rd_ack;
        logic [31:0] rd_data;
        logic wr_ack;
    } mldsa_reg__MLDSA_PRIVKEY_OUT__external__in_t;

    typedef struct packed{
        logic rd_ack;
        logic [31:0] rd_data;
        logic wr_ack;
    } mldsa_reg__MLDSA_PRIVKEY_IN__external__in_t;

    typedef struct packed{
        logic hwclr;
    } kv_read_ctrl_reg__read_en__in_t;

    typedef struct packed{
        kv_read_ctrl_reg__read_en__in_t read_en;
    } kv_read_ctrl_reg__in_t;

    typedef struct packed{
        logic next;
    } kv_status_reg__READY__in_t;

    typedef struct packed{
        logic hwclr;
        logic hwset;
    } kv_status_reg__VALID__in_t;

    typedef struct packed{
        logic [7:0] next;
    } kv_status_reg__ERROR__in_t;

    typedef struct packed{
        kv_status_reg__READY__in_t READY;
        kv_status_reg__VALID__in_t VALID;
        kv_status_reg__ERROR__in_t ERROR;
    } kv_status_reg__in_t;

    typedef struct packed{
        logic hwset;
    } mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__error_internal_sts_enable_d33001bb_next_52b75ffa_resetsignal_0d7eaa27__in_t;

    typedef struct packed{
        mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__error_internal_sts_enable_d33001bb_next_52b75ffa_resetsignal_0d7eaa27__in_t error_internal_sts;
    } mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__in_t;

    typedef struct packed{
        logic hwset;
    } mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__notif_cmd_done_sts_enable_dabe0b8b_next_540fa3b7__in_t;

    typedef struct packed{
        mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__notif_cmd_done_sts_enable_dabe0b8b_next_540fa3b7__in_t notif_cmd_done_sts;
    } mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__in_t;

    typedef struct packed{
        mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__in_t error_internal_intr_r;
        mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__in_t notif_internal_intr_r;
    } mldsa_reg__intr_block_t__in_t;

    typedef struct packed{
        logic reset_b;
        logic hard_reset_b;
        logic mldsa_ready;
        mldsa_reg__MLDSA_NAME__in_t [2-1:0]MLDSA_NAME;
        mldsa_reg__MLDSA_VERSION__in_t [2-1:0]MLDSA_VERSION;
        mldsa_reg__MLDSA_CTRL__in_t MLDSA_CTRL;
        mldsa_reg__MLDSA_STATUS__in_t MLDSA_STATUS;
        mldsa_reg__MLDSA_ENTROPY__in_t [16-1:0]MLDSA_ENTROPY;
        mldsa_reg__MLDSA_SEED__in_t [8-1:0]MLDSA_SEED;
        mldsa_reg__MLDSA_SIGN_RND__in_t [8-1:0]MLDSA_SIGN_RND;
        mldsa_reg__MLDSA_MSG__in_t [16-1:0]MLDSA_MSG;
        mldsa_reg__MLDSA_VERIFY_RES__in_t [16-1:0]MLDSA_VERIFY_RES;
        mldsa_reg__MLDSA_EXTERNAL_MU__in_t [16-1:0]MLDSA_EXTERNAL_MU;
        mldsa_reg__MLDSA_PUBKEY__external__in_t MLDSA_PUBKEY;
        mldsa_reg__MLDSA_SIGNATURE__external__in_t MLDSA_SIGNATURE;
        mldsa_reg__MLDSA_PRIVKEY_OUT__external__in_t MLDSA_PRIVKEY_OUT;
        mldsa_reg__MLDSA_PRIVKEY_IN__external__in_t MLDSA_PRIVKEY_IN;
        kv_read_ctrl_reg__in_t mldsa_kv_rd_seed_ctrl;
        kv_status_reg__in_t mldsa_kv_rd_seed_status;
        mldsa_reg__intr_block_t__in_t intr_block_rf;
    } mldsa_reg__in_t;

    typedef struct packed{
        logic [2:0] value;
    } mldsa_reg__MLDSA_CTRL__CTRL__out_t;

    typedef struct packed{
        logic value;
    } mldsa_reg__MLDSA_CTRL__ZEROIZE__out_t;

    typedef struct packed{
        logic value;
    } mldsa_reg__MLDSA_CTRL__PCR_SIGN__out_t;

    typedef struct packed{
        logic value;
    } mldsa_reg__MLDSA_CTRL__EXTERNAL_MU__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_CTRL__CTRL__out_t CTRL;
        mldsa_reg__MLDSA_CTRL__ZEROIZE__out_t ZEROIZE;
        mldsa_reg__MLDSA_CTRL__PCR_SIGN__out_t PCR_SIGN;
        mldsa_reg__MLDSA_CTRL__EXTERNAL_MU__out_t EXTERNAL_MU;
    } mldsa_reg__MLDSA_CTRL__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_ENTROPY__ENTROPY__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_ENTROPY__ENTROPY__out_t ENTROPY;
    } mldsa_reg__MLDSA_ENTROPY__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_SEED__SEED__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_SEED__SEED__out_t SEED;
    } mldsa_reg__MLDSA_SEED__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_SIGN_RND__SIGN_RND__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_SIGN_RND__SIGN_RND__out_t SIGN_RND;
    } mldsa_reg__MLDSA_SIGN_RND__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_MSG__MSG__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_MSG__MSG__out_t MSG;
    } mldsa_reg__MLDSA_MSG__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_VERIFY_RES__VERIFY_RES__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_VERIFY_RES__VERIFY_RES__out_t VERIFY_RES;
    } mldsa_reg__MLDSA_VERIFY_RES__out_t;

    typedef struct packed{
        logic [31:0] value;
    } mldsa_reg__MLDSA_EXTERNAL_MU__EXTERNAL_MU__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_EXTERNAL_MU__EXTERNAL_MU__out_t EXTERNAL_MU;
    } mldsa_reg__MLDSA_EXTERNAL_MU__out_t;

    typedef struct packed{
        logic req;
        logic [11:0] addr;
        logic req_is_wr;
        logic [31:0] wr_data;
        logic [31:0] wr_biten;
    } mldsa_reg__MLDSA_PUBKEY__external__out_t;

    typedef struct packed{
        logic req;
        logic [12:0] addr;
        logic req_is_wr;
        logic [31:0] wr_data;
        logic [31:0] wr_biten;
    } mldsa_reg__MLDSA_SIGNATURE__external__out_t;

    typedef struct packed{
        logic req;
        logic [12:0] addr;
        logic req_is_wr;
        logic [31:0] wr_data;
        logic [31:0] wr_biten;
    } mldsa_reg__MLDSA_PRIVKEY_OUT__external__out_t;

    typedef struct packed{
        logic req;
        logic [12:0] addr;
        logic req_is_wr;
        logic [31:0] wr_data;
        logic [31:0] wr_biten;
    } mldsa_reg__MLDSA_PRIVKEY_IN__external__out_t;

    typedef struct packed{
        logic value;
    } kv_read_ctrl_reg__read_en__out_t;

    typedef struct packed{
        logic [4:0] value;
    } kv_read_ctrl_reg__read_entry__out_t;

    typedef struct packed{
        logic value;
    } kv_read_ctrl_reg__pcr_hash_extend__out_t;

    typedef struct packed{
        logic [24:0] value;
    } kv_read_ctrl_reg__rsvd__out_t;

    typedef struct packed{
        kv_read_ctrl_reg__read_en__out_t read_en;
        kv_read_ctrl_reg__read_entry__out_t read_entry;
        kv_read_ctrl_reg__pcr_hash_extend__out_t pcr_hash_extend;
        kv_read_ctrl_reg__rsvd__out_t rsvd;
    } kv_read_ctrl_reg__out_t;

    typedef struct packed{
        logic intr;
    } mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a__out_t;

    typedef struct packed{
        logic intr;
    } mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a__out_t;

    typedef struct packed{
        logic intr;
    } mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__out_t;

    typedef struct packed{
        logic intr;
    } mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__out_t;

    typedef struct packed{
        mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a__out_t error_global_intr_r;
        mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a__out_t notif_global_intr_r;
        mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02__out_t error_internal_intr_r;
        mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e__out_t notif_internal_intr_r;
    } mldsa_reg__intr_block_t__out_t;

    typedef struct packed{
        mldsa_reg__MLDSA_CTRL__out_t MLDSA_CTRL;
        mldsa_reg__MLDSA_ENTROPY__out_t [16-1:0]MLDSA_ENTROPY;
        mldsa_reg__MLDSA_SEED__out_t [8-1:0]MLDSA_SEED;
        mldsa_reg__MLDSA_SIGN_RND__out_t [8-1:0]MLDSA_SIGN_RND;
        mldsa_reg__MLDSA_MSG__out_t [16-1:0]MLDSA_MSG;
        mldsa_reg__MLDSA_VERIFY_RES__out_t [16-1:0]MLDSA_VERIFY_RES;
        mldsa_reg__MLDSA_EXTERNAL_MU__out_t [16-1:0]MLDSA_EXTERNAL_MU;
        mldsa_reg__MLDSA_PUBKEY__external__out_t MLDSA_PUBKEY;
        mldsa_reg__MLDSA_SIGNATURE__external__out_t MLDSA_SIGNATURE;
        mldsa_reg__MLDSA_PRIVKEY_OUT__external__out_t MLDSA_PRIVKEY_OUT;
        mldsa_reg__MLDSA_PRIVKEY_IN__external__out_t MLDSA_PRIVKEY_IN;
        kv_read_ctrl_reg__out_t mldsa_kv_rd_seed_ctrl;
        mldsa_reg__intr_block_t__out_t intr_block_rf;
    } mldsa_reg__out_t;

    typedef enum logic [31:0] {
        kv_status_reg__ERROR__kv_error_e__SUCCESS = 'h0,
        kv_status_reg__ERROR__kv_error_e__KV_READ_FAIL = 'h1,
        kv_status_reg__ERROR__kv_error_e__KV_WRITE_FAIL = 'h2
    } kv_status_reg__ERROR__kv_error_e_e;

    localparam MLDSA_REG_ADDR_WIDTH = 32'd16;

endpackage