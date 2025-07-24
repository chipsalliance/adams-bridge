// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

`ifndef ABR_REG_COVERGROUPS
    `define ABR_REG_COVERGROUPS
    
    /*----------------------- ABR_REG__MLDSA_NAME COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_NAME_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_NAME_fld_cg with function sample(
    input bit [32-1:0] NAME
    );
        option.per_instance = 1;
        NAME_cp : coverpoint NAME;

    endgroup

    /*----------------------- ABR_REG__MLDSA_VERSION COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_VERSION_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_VERSION_fld_cg with function sample(
    input bit [32-1:0] VERSION
    );
        option.per_instance = 1;
        VERSION_cp : coverpoint VERSION;

    endgroup

    /*----------------------- ABR_REG__MLDSA_CTRL COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_CTRL_fld_cg with function sample(
    input bit [3-1:0] CTRL,
    input bit [1-1:0] ZEROIZE,
    input bit [1-1:0] PCR_SIGN,
    input bit [1-1:0] EXTERNAL_MU,
    input bit [1-1:0] STREAM_MSG
    );
        option.per_instance = 1;
        CTRL_cp : coverpoint CTRL;
        ZEROIZE_cp : coverpoint ZEROIZE;
        PCR_SIGN_cp : coverpoint PCR_SIGN;
        EXTERNAL_MU_cp : coverpoint EXTERNAL_MU;
        STREAM_MSG_cp : coverpoint STREAM_MSG;

    endgroup

    /*----------------------- ABR_REG__MLDSA_STATUS COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_STATUS_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID,
    input bit [1-1:0] MSG_STREAM_READY
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;
        MSG_STREAM_READY_cp : coverpoint MSG_STREAM_READY;

    endgroup

    /*----------------------- ABR_REG__ABR_ENTROPY COVERGROUPS -----------------------*/
    covergroup abr_reg__ABR_ENTROPY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__ABR_ENTROPY_fld_cg with function sample(
    input bit [32-1:0] ENTROPY
    );
        option.per_instance = 1;
        ENTROPY_cp : coverpoint ENTROPY;

    endgroup

    /*----------------------- ABR_REG__MLDSA_SEED COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_SEED_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_SEED_fld_cg with function sample(
    input bit [32-1:0] SEED
    );
        option.per_instance = 1;
        SEED_cp : coverpoint SEED;

    endgroup

    /*----------------------- ABR_REG__MLDSA_SIGN_RND COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_SIGN_RND_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_SIGN_RND_fld_cg with function sample(
    input bit [32-1:0] SIGN_RND
    );
        option.per_instance = 1;
        SIGN_RND_cp : coverpoint SIGN_RND;

    endgroup

    /*----------------------- ABR_REG__MLDSA_MSG COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_MSG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_MSG_fld_cg with function sample(
    input bit [32-1:0] MSG
    );
        option.per_instance = 1;
        MSG_cp : coverpoint MSG;

    endgroup

    /*----------------------- ABR_REG__MLDSA_VERIFY_RES COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_VERIFY_RES_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_VERIFY_RES_fld_cg with function sample(
    input bit [32-1:0] VERIFY_RES
    );
        option.per_instance = 1;
        VERIFY_RES_cp : coverpoint VERIFY_RES;

    endgroup

    /*----------------------- ABR_REG__MLDSA_EXTERNAL_MU COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_EXTERNAL_MU_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_EXTERNAL_MU_fld_cg with function sample(
    input bit [32-1:0] EXTERNAL_MU
    );
        option.per_instance = 1;
        EXTERNAL_MU_cp : coverpoint EXTERNAL_MU;

    endgroup

    /*----------------------- ABR_REG__MLDSA_MSG_STROBE COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_MSG_STROBE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_MSG_STROBE_fld_cg with function sample(
    input bit [4-1:0] STROBE
    );
        option.per_instance = 1;
        STROBE_cp : coverpoint STROBE;

    endgroup

    /*----------------------- ABR_REG__MLDSA_CTX_CONFIG COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_CTX_CONFIG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_CTX_CONFIG_fld_cg with function sample(
    input bit [8-1:0] CTX_SIZE
    );
        option.per_instance = 1;
        CTX_SIZE_cp : coverpoint CTX_SIZE;

    endgroup

    /*----------------------- ABR_REG__MLDSA_CTX COVERGROUPS -----------------------*/
    covergroup abr_reg__MLDSA_CTX_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLDSA_CTX_fld_cg with function sample(
    input bit [32-1:0] CTX
    );
        option.per_instance = 1;
        CTX_cp : coverpoint CTX;

    endgroup

    /*----------------------- KV_READ_CTRL_REG COVERGROUPS -----------------------*/
    covergroup kv_read_ctrl_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_read_ctrl_reg_fld_cg with function sample(
    input bit [1-1:0] read_en,
    input bit [5-1:0] read_entry,
    input bit [1-1:0] pcr_hash_extend,
    input bit [25-1:0] rsvd
    );
        option.per_instance = 1;
        read_en_cp : coverpoint read_en;
        read_entry_cp : coverpoint read_entry;
        pcr_hash_extend_cp : coverpoint pcr_hash_extend;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- KV_STATUS_REG COVERGROUPS -----------------------*/
    covergroup kv_status_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_status_reg_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID,
    input bit [8-1:0] ERROR
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;
        ERROR_cp : coverpoint ERROR;

    endgroup

    /*----------------------- ABR_REG__MLKEM_NAME COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_NAME_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_NAME_fld_cg with function sample(
    input bit [32-1:0] NAME
    );
        option.per_instance = 1;
        NAME_cp : coverpoint NAME;

    endgroup

    /*----------------------- ABR_REG__MLKEM_VERSION COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_VERSION_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_VERSION_fld_cg with function sample(
    input bit [32-1:0] VERSION
    );
        option.per_instance = 1;
        VERSION_cp : coverpoint VERSION;

    endgroup

    /*----------------------- ABR_REG__MLKEM_CTRL COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_CTRL_fld_cg with function sample(
    input bit [3-1:0] CTRL,
    input bit [1-1:0] ZEROIZE
    );
        option.per_instance = 1;
        CTRL_cp : coverpoint CTRL;
        ZEROIZE_cp : coverpoint ZEROIZE;

    endgroup

    /*----------------------- ABR_REG__MLKEM_STATUS COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_STATUS_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;

    endgroup

    /*----------------------- ABR_REG__MLKEM_SEED_D COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_SEED_D_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_SEED_D_fld_cg with function sample(
    input bit [32-1:0] SEED
    );
        option.per_instance = 1;
        SEED_cp : coverpoint SEED;

    endgroup

    /*----------------------- ABR_REG__MLKEM_SEED_Z COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_SEED_Z_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_SEED_Z_fld_cg with function sample(
    input bit [32-1:0] SEED
    );
        option.per_instance = 1;
        SEED_cp : coverpoint SEED;

    endgroup

    /*----------------------- ABR_REG__MLKEM_SHARED_KEY COVERGROUPS -----------------------*/
    covergroup abr_reg__MLKEM_SHARED_KEY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__MLKEM_SHARED_KEY_fld_cg with function sample(
    input bit [32-1:0] KEY
    );
        option.per_instance = 1;
        KEY_cp : coverpoint KEY;

    endgroup

    /*----------------------- KV_WRITE_CTRL_REG COVERGROUPS -----------------------*/
    covergroup kv_write_ctrl_reg_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup kv_write_ctrl_reg_fld_cg with function sample(
    input bit [1-1:0] write_en,
    input bit [5-1:0] write_entry,
    input bit [1-1:0] hmac_key_dest_valid,
    input bit [1-1:0] hmac_block_dest_valid,
    input bit [1-1:0] mldsa_seed_dest_valid,
    input bit [1-1:0] ecc_pkey_dest_valid,
    input bit [1-1:0] ecc_seed_dest_valid,
    input bit [21-1:0] rsvd
    );
        option.per_instance = 1;
        write_en_cp : coverpoint write_en;
        write_entry_cp : coverpoint write_entry;
        hmac_key_dest_valid_cp : coverpoint hmac_key_dest_valid;
        hmac_block_dest_valid_cp : coverpoint hmac_block_dest_valid;
        mldsa_seed_dest_valid_cp : coverpoint mldsa_seed_dest_valid;
        ecc_pkey_dest_valid_cp : coverpoint ecc_pkey_dest_valid;
        ecc_seed_dest_valid_cp : coverpoint ecc_seed_dest_valid;
        rsvd_cp : coverpoint rsvd;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_en
    );
        option.per_instance = 1;
        error_internal_en_cp : coverpoint error_internal_en;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_en
    );
        option.per_instance = 1;
        notif_cmd_done_en_cp : coverpoint notif_cmd_done_en;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_INTERNAL_STS_83ADAB02 COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02_fld_cg with function sample(
    input bit [1-1:0] error_internal_sts
    );
        option.per_instance = 1;
        error_internal_sts_cp : coverpoint error_internal_sts;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_sts
    );
        option.per_instance = 1;
        notif_cmd_done_sts_cp : coverpoint notif_cmd_done_sts;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_trig
    );
        option.per_instance = 1;
        error_internal_trig_cp : coverpoint error_internal_trig;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_trig
    );
        option.per_instance = 1;
        notif_cmd_done_trig_cp : coverpoint notif_cmd_done_trig;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_60DDFF93 COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__intr_count_t_cnt_60ddff93_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__intr_count_t_cnt_60ddff93_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_BE67D6D5 COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__intr_count_t_cnt_be67d6d5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__intr_count_t_cnt_be67d6d5_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6173128E COVERGROUPS -----------------------*/
    covergroup abr_reg__intr_block_t__intr_count_incr_t_pulse_6173128e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup abr_reg__intr_block_t__intr_count_incr_t_pulse_6173128e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif
