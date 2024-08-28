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

`ifndef MLDSA_REG_SAMPLE
    `define MLDSA_REG_SAMPLE
    
    /*----------------------- MLDSA_REG__MLDSA_NAME SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_NAME::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*NAME*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_NAME::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(NAME.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( NAME.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_VERSION SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_VERSION::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*VERSION*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_VERSION::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(VERSION.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERSION.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTRL_bit_cg[bt]) this.CTRL_bit_cg[bt].sample(data[0 + bt]);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(data[3 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[2:0]/*CTRL*/  ,  data[3:3]/*ZEROIZE*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTRL_bit_cg[bt]) this.CTRL_bit_cg[bt].sample(CTRL.get_mirrored_value() >> bt);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CTRL.get_mirrored_value()  ,  ZEROIZE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_ENTROPY SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_ENTROPY::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ENTROPY_bit_cg[bt]) this.ENTROPY_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*ENTROPY*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_ENTROPY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ENTROPY_bit_cg[bt]) this.ENTROPY_bit_cg[bt].sample(ENTROPY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ENTROPY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_SEED SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_SEED::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SEED_bit_cg[bt]) this.SEED_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*SEED*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_SEED::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SEED_bit_cg[bt]) this.SEED_bit_cg[bt].sample(SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_SIGN_RND SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_SIGN_RND::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SIGN_RND_bit_cg[bt]) this.SIGN_RND_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*SIGN_RND*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_SIGN_RND::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SIGN_RND_bit_cg[bt]) this.SIGN_RND_bit_cg[bt].sample(SIGN_RND.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SIGN_RND.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_MSG SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_MSG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MSG_bit_cg[bt]) this.MSG_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*MSG*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_MSG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MSG_bit_cg[bt]) this.MSG_bit_cg[bt].sample(MSG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MSG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_VERIFY_RES SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_VERIFY_RES::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERIFY_RES_bit_cg[bt]) this.VERIFY_RES_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*VERIFY_RES*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_VERIFY_RES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERIFY_RES_bit_cg[bt]) this.VERIFY_RES_bit_cg[bt].sample(VERIFY_RES.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERIFY_RES.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_PUBKEY SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_PUBKEY::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PUBKEY_bit_cg[bt]) this.PUBKEY_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*PUBKEY*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_PUBKEY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(PUBKEY_bit_cg[bt]) this.PUBKEY_bit_cg[bt].sample(PUBKEY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( PUBKEY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__MLDSA_SIGNATURE SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__MLDSA_SIGNATURE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SIGNATURE_bit_cg[bt]) this.SIGNATURE_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*SIGNATURE*/   );
        end
    endfunction

    function void mldsa_reg__MLDSA_SIGNATURE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SIGNATURE_bit_cg[bt]) this.SIGNATURE_bit_cg[bt].sample(SIGNATURE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SIGNATURE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__global_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(data[1 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_en*/  ,  data[1:1]/*notif_en*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__error_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_en_bit_cg[bt]) this.error_internal_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_en*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_en_bit_cg[bt]) this.error_internal_en_bit_cg[bt].sample(error_internal_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__notif_intr_en_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_en*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(notif_cmd_done_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*agg_sts*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_INTERNAL_STS_83ADAB02 SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_sts_bit_cg[bt]) this.error_internal_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_sts*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_sts_bit_cg[bt]) this.error_internal_sts_bit_cg[bt].sample(error_internal_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_sts*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(notif_cmd_done_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__error_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_trig_bit_cg[bt]) this.error_internal_trig_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*error_internal_trig*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_trig_bit_cg[bt]) this.error_internal_trig_bit_cg[bt].sample(error_internal_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__notif_intr_trig_t::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*notif_cmd_done_trig*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(notif_cmd_done_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_60DDFF93 SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__intr_count_t_cnt_60ddff93::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__intr_count_t_cnt_60ddff93::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_BE67D6D5 SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__intr_count_t_cnt_be67d6d5::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*cnt*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__intr_count_t_cnt_be67d6d5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- MLDSA_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6173128E SAMPLE FUNCTIONS -----------------------*/
    function void mldsa_reg__intr_block_t__intr_count_incr_t_pulse_6173128e::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*pulse*/   );
        end
    endfunction

    function void mldsa_reg__intr_block_t__intr_count_incr_t_pulse_6173128e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif