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

`ifndef MLDSA_REG_COVERGROUPS
    `define MLDSA_REG_COVERGROUPS
    
    /*----------------------- MLDSA_REG__MLDSA_NAME COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_NAME_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_NAME_fld_cg with function sample(
    input bit [32-1:0] NAME
    );
        option.per_instance = 1;
        NAME_cp : coverpoint NAME;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_VERSION COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_VERSION_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_VERSION_fld_cg with function sample(
    input bit [32-1:0] VERSION
    );
        option.per_instance = 1;
        VERSION_cp : coverpoint VERSION;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_CTRL COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_CTRL_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_CTRL_fld_cg with function sample(
    input bit [3-1:0] CTRL,
    input bit [1-1:0] ZEROIZE
    );
        option.per_instance = 1;
        CTRL_cp : coverpoint CTRL;
        ZEROIZE_cp : coverpoint ZEROIZE;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_STATUS COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_STATUS_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_STATUS_fld_cg with function sample(
    input bit [1-1:0] READY,
    input bit [1-1:0] VALID
    );
        option.per_instance = 1;
        READY_cp : coverpoint READY;
        VALID_cp : coverpoint VALID;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_ENTROPY COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_ENTROPY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_ENTROPY_fld_cg with function sample(
    input bit [32-1:0] ENTROPY
    );
        option.per_instance = 1;
        ENTROPY_cp : coverpoint ENTROPY;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_SEED COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_SEED_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_SEED_fld_cg with function sample(
    input bit [32-1:0] SEED
    );
        option.per_instance = 1;
        SEED_cp : coverpoint SEED;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_SIGN_RND COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_SIGN_RND_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_SIGN_RND_fld_cg with function sample(
    input bit [32-1:0] SIGN_RND
    );
        option.per_instance = 1;
        SIGN_RND_cp : coverpoint SIGN_RND;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_MSG COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_MSG_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_MSG_fld_cg with function sample(
    input bit [32-1:0] MSG
    );
        option.per_instance = 1;
        MSG_cp : coverpoint MSG;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_VERIFY_RES COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_VERIFY_RES_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_VERIFY_RES_fld_cg with function sample(
    input bit [32-1:0] VERIFY_RES
    );
        option.per_instance = 1;
        VERIFY_RES_cp : coverpoint VERIFY_RES;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_PUBKEY COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_PUBKEY_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_PUBKEY_fld_cg with function sample(
    input bit [32-1:0] PUBKEY
    );
        option.per_instance = 1;
        PUBKEY_cp : coverpoint PUBKEY;

    endgroup

    /*----------------------- MLDSA_REG__MLDSA_SIGNATURE COVERGROUPS -----------------------*/
    covergroup mldsa_reg__MLDSA_SIGNATURE_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__MLDSA_SIGNATURE_fld_cg with function sample(
    input bit [32-1:0] SIGNATURE
    );
        option.per_instance = 1;
        SIGNATURE_cp : coverpoint SIGNATURE;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__global_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__global_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_en,
    input bit [1-1:0] notif_en
    );
        option.per_instance = 1;
        error_en_cp : coverpoint error_en;
        notif_en_cp : coverpoint notif_en;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__error_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__error_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_en
    );
        option.per_instance = 1;
        error_internal_en_cp : coverpoint error_internal_en;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__notif_intr_en_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__notif_intr_en_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_en
    );
        option.per_instance = 1;
        notif_cmd_done_en_cp : coverpoint notif_cmd_done_en;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a_fld_cg with function sample(
    input bit [1-1:0] agg_sts
    );
        option.per_instance = 1;
        agg_sts_cp : coverpoint agg_sts;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_INTERNAL_STS_83ADAB02 COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02_fld_cg with function sample(
    input bit [1-1:0] error_internal_sts
    );
        option.per_instance = 1;
        error_internal_sts_cp : coverpoint error_internal_sts;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_sts
    );
        option.per_instance = 1;
        notif_cmd_done_sts_cp : coverpoint notif_cmd_done_sts;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__error_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__error_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] error_internal_trig
    );
        option.per_instance = 1;
        error_internal_trig_cp : coverpoint error_internal_trig;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__notif_intr_trig_t_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__notif_intr_trig_t_fld_cg with function sample(
    input bit [1-1:0] notif_cmd_done_trig
    );
        option.per_instance = 1;
        notif_cmd_done_trig_cp : coverpoint notif_cmd_done_trig;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_60DDFF93 COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__intr_count_t_cnt_60ddff93_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__intr_count_t_cnt_60ddff93_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_BE67D6D5 COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__intr_count_t_cnt_be67d6d5_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__intr_count_t_cnt_be67d6d5_fld_cg with function sample(
    input bit [32-1:0] cnt
    );
        option.per_instance = 1;
        cnt_cp : coverpoint cnt;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6173128E COVERGROUPS -----------------------*/
    covergroup mldsa_reg__intr_block_t__intr_count_incr_t_pulse_6173128e_bit_cg with function sample(input bit reg_bit);
        option.per_instance = 1;
        reg_bit_cp : coverpoint reg_bit {
            bins value[2] = {0,1};
        }
        reg_bit_edge_cp : coverpoint reg_bit {
            bins rise = (0 => 1);
            bins fall = (1 => 0);
        }

    endgroup
    covergroup mldsa_reg__intr_block_t__intr_count_incr_t_pulse_6173128e_fld_cg with function sample(
    input bit [1-1:0] pulse
    );
        option.per_instance = 1;
        pulse_cp : coverpoint pulse;

    endgroup

`endif