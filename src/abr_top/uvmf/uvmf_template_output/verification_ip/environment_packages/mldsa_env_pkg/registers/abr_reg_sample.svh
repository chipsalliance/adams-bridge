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

`ifndef ABR_REG_SAMPLE
    `define ABR_REG_SAMPLE
    
    /*----------------------- ABR_REG__MLDSA_NAME SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_NAME::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_NAME::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(NAME.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( NAME.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_VERSION SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_VERSION::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_VERSION::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(VERSION.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERSION.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_CTRL::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTRL_bit_cg[bt]) this.CTRL_bit_cg[bt].sample(data[0 + bt]);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(data[3 + bt]);
            foreach(PCR_SIGN_bit_cg[bt]) this.PCR_SIGN_bit_cg[bt].sample(data[4 + bt]);
            foreach(EXTERNAL_MU_bit_cg[bt]) this.EXTERNAL_MU_bit_cg[bt].sample(data[5 + bt]);
            foreach(STREAM_MSG_bit_cg[bt]) this.STREAM_MSG_bit_cg[bt].sample(data[6 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[2:0]/*CTRL*/  ,  data[3:3]/*ZEROIZE*/  ,  data[4:4]/*PCR_SIGN*/  ,  data[5:5]/*EXTERNAL_MU*/  ,  data[6:6]/*STREAM_MSG*/   );
        end
    endfunction

    function void abr_reg__MLDSA_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTRL_bit_cg[bt]) this.CTRL_bit_cg[bt].sample(CTRL.get_mirrored_value() >> bt);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
            foreach(PCR_SIGN_bit_cg[bt]) this.PCR_SIGN_bit_cg[bt].sample(PCR_SIGN.get_mirrored_value() >> bt);
            foreach(EXTERNAL_MU_bit_cg[bt]) this.EXTERNAL_MU_bit_cg[bt].sample(EXTERNAL_MU.get_mirrored_value() >> bt);
            foreach(STREAM_MSG_bit_cg[bt]) this.STREAM_MSG_bit_cg[bt].sample(STREAM_MSG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CTRL.get_mirrored_value()  ,  ZEROIZE.get_mirrored_value()  ,  PCR_SIGN.get_mirrored_value()  ,  EXTERNAL_MU.get_mirrored_value()  ,  STREAM_MSG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_STATUS::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
            foreach(MSG_STREAM_READY_bit_cg[bt]) this.MSG_STREAM_READY_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/  ,  data[2:2]/*MSG_STREAM_READY*/   );
        end
    endfunction

    function void abr_reg__MLDSA_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(MSG_STREAM_READY_bit_cg[bt]) this.MSG_STREAM_READY_bit_cg[bt].sample(MSG_STREAM_READY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()  ,  MSG_STREAM_READY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__ABR_ENTROPY SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__ABR_ENTROPY::sample(uvm_reg_data_t  data,
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

    function void abr_reg__ABR_ENTROPY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(ENTROPY_bit_cg[bt]) this.ENTROPY_bit_cg[bt].sample(ENTROPY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( ENTROPY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_SEED SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_SEED::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_SEED::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SEED_bit_cg[bt]) this.SEED_bit_cg[bt].sample(SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_SIGN_RND SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_SIGN_RND::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_SIGN_RND::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SIGN_RND_bit_cg[bt]) this.SIGN_RND_bit_cg[bt].sample(SIGN_RND.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SIGN_RND.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_MSG SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_MSG::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_MSG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MSG_bit_cg[bt]) this.MSG_bit_cg[bt].sample(MSG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MSG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_VERIFY_RES SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_VERIFY_RES::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLDSA_VERIFY_RES::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERIFY_RES_bit_cg[bt]) this.VERIFY_RES_bit_cg[bt].sample(VERIFY_RES.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERIFY_RES.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_EXTERNAL_MU SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_EXTERNAL_MU::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(EXTERNAL_MU_bit_cg[bt]) this.EXTERNAL_MU_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*EXTERNAL_MU*/   );
        end
    endfunction

    function void abr_reg__MLDSA_EXTERNAL_MU::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(EXTERNAL_MU_bit_cg[bt]) this.EXTERNAL_MU_bit_cg[bt].sample(EXTERNAL_MU.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( EXTERNAL_MU.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_MSG_STROBE SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_MSG_STROBE::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(STROBE_bit_cg[bt]) this.STROBE_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[3:0]/*STROBE*/   );
        end
    endfunction

    function void abr_reg__MLDSA_MSG_STROBE::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(STROBE_bit_cg[bt]) this.STROBE_bit_cg[bt].sample(STROBE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( STROBE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_CTX_CONFIG SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_CTX_CONFIG::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTX_SIZE_bit_cg[bt]) this.CTX_SIZE_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[7:0]/*CTX_SIZE*/   );
        end
    endfunction

    function void abr_reg__MLDSA_CTX_CONFIG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTX_SIZE_bit_cg[bt]) this.CTX_SIZE_bit_cg[bt].sample(CTX_SIZE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CTX_SIZE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLDSA_CTX SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLDSA_CTX::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTX_bit_cg[bt]) this.CTX_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*CTX*/   );
        end
    endfunction

    function void abr_reg__MLDSA_CTX::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTX_bit_cg[bt]) this.CTX_bit_cg[bt].sample(CTX.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CTX.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_READ_CTRL_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_read_ctrl_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(data[0 + bt]);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(data[1 + bt]);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(data[6 + bt]);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(data[7 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*read_en*/  ,  data[5:1]/*read_entry*/  ,  data[6:6]/*pcr_hash_extend*/  ,  data[31:7]/*rsvd*/   );
        end
    endfunction

    function void kv_read_ctrl_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(read_en_bit_cg[bt]) this.read_en_bit_cg[bt].sample(read_en.get_mirrored_value() >> bt);
            foreach(read_entry_bit_cg[bt]) this.read_entry_bit_cg[bt].sample(read_entry.get_mirrored_value() >> bt);
            foreach(pcr_hash_extend_bit_cg[bt]) this.pcr_hash_extend_bit_cg[bt].sample(pcr_hash_extend.get_mirrored_value() >> bt);
            foreach(rsvd_bit_cg[bt]) this.rsvd_bit_cg[bt].sample(rsvd.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( read_en.get_mirrored_value()  ,  read_entry.get_mirrored_value()  ,  pcr_hash_extend.get_mirrored_value()  ,  rsvd.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- KV_STATUS_REG SAMPLE FUNCTIONS -----------------------*/
    function void kv_status_reg::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(data[0 + bt]);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(data[1 + bt]);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(data[2 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[0:0]/*READY*/  ,  data[1:1]/*VALID*/  ,  data[9:2]/*ERROR*/   );
        end
    endfunction

    function void kv_status_reg::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
            foreach(ERROR_bit_cg[bt]) this.ERROR_bit_cg[bt].sample(ERROR.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()  ,  ERROR.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_NAME SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_NAME::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_NAME::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(NAME_bit_cg[bt]) this.NAME_bit_cg[bt].sample(NAME.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( NAME.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_VERSION SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_VERSION::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_VERSION::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(VERSION_bit_cg[bt]) this.VERSION_bit_cg[bt].sample(VERSION.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( VERSION.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_CTRL SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_CTRL::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_CTRL::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(CTRL_bit_cg[bt]) this.CTRL_bit_cg[bt].sample(CTRL.get_mirrored_value() >> bt);
            foreach(ZEROIZE_bit_cg[bt]) this.ZEROIZE_bit_cg[bt].sample(ZEROIZE.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( CTRL.get_mirrored_value()  ,  ZEROIZE.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_STATUS SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_STATUS::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_STATUS::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(READY_bit_cg[bt]) this.READY_bit_cg[bt].sample(READY.get_mirrored_value() >> bt);
            foreach(VALID_bit_cg[bt]) this.VALID_bit_cg[bt].sample(VALID.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( READY.get_mirrored_value()  ,  VALID.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_SEED_D SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_SEED_D::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_SEED_D::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SEED_bit_cg[bt]) this.SEED_bit_cg[bt].sample(SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_SEED_Z SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_SEED_Z::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_SEED_Z::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(SEED_bit_cg[bt]) this.SEED_bit_cg[bt].sample(SEED.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( SEED.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_MSG SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_MSG::sample(uvm_reg_data_t  data,
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

    function void abr_reg__MLKEM_MSG::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(MSG_bit_cg[bt]) this.MSG_bit_cg[bt].sample(MSG.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( MSG.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__MLKEM_SHARED_KEY SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__MLKEM_SHARED_KEY::sample(uvm_reg_data_t  data,
                                                   uvm_reg_data_t  byte_en,
                                                   bit             is_read,
                                                   uvm_reg_map     map);
        m_current = get();
        m_data    = data;
        m_is_read = is_read;
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(data[0 + bt]);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( data[31:0]/*KEY*/   );
        end
    endfunction

    function void abr_reg__MLKEM_SHARED_KEY::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(KEY_bit_cg[bt]) this.KEY_bit_cg[bt].sample(KEY.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( KEY.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__global_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__global_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_en_bit_cg[bt]) this.error_en_bit_cg[bt].sample(error_en.get_mirrored_value() >> bt);
            foreach(notif_en_bit_cg[bt]) this.notif_en_bit_cg[bt].sample(notif_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_en.get_mirrored_value()  ,  notif_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__error_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__error_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_en_bit_cg[bt]) this.error_internal_en_bit_cg[bt].sample(error_internal_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_EN_T SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__notif_intr_en_t::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__notif_intr_en_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_en_bit_cg[bt]) this.notif_cmd_done_en_bit_cg[bt].sample(notif_cmd_done_en.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_en.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_DD3DCF0A SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__global_intr_t_agg_sts_dd3dcf0a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__GLOBAL_INTR_T_AGG_STS_E6399B4A SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__global_intr_t_agg_sts_e6399b4a::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(agg_sts_bit_cg[bt]) this.agg_sts_bit_cg[bt].sample(agg_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( agg_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_T_ERROR_INTERNAL_STS_83ADAB02 SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__error_intr_t_error_internal_sts_83adab02::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_sts_bit_cg[bt]) this.error_internal_sts_bit_cg[bt].sample(error_internal_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_T_NOTIF_CMD_DONE_STS_1C68637E SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__notif_intr_t_notif_cmd_done_sts_1c68637e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_sts_bit_cg[bt]) this.notif_cmd_done_sts_bit_cg[bt].sample(notif_cmd_done_sts.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_sts.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__ERROR_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__error_intr_trig_t::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__error_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(error_internal_trig_bit_cg[bt]) this.error_internal_trig_bit_cg[bt].sample(error_internal_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( error_internal_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__NOTIF_INTR_TRIG_T SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__notif_intr_trig_t::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__notif_intr_trig_t::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(notif_cmd_done_trig_bit_cg[bt]) this.notif_cmd_done_trig_bit_cg[bt].sample(notif_cmd_done_trig.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( notif_cmd_done_trig.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_60DDFF93 SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__intr_count_t_cnt_60ddff93::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__intr_count_t_cnt_60ddff93::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_T_CNT_BE67D6D5 SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__intr_count_t_cnt_be67d6d5::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__intr_count_t_cnt_be67d6d5::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(cnt_bit_cg[bt]) this.cnt_bit_cg[bt].sample(cnt.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( cnt.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_15E6ED7E SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__intr_count_incr_t_pulse_15e6ed7e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

    /*----------------------- ABR_REG__INTR_BLOCK_T__INTR_COUNT_INCR_T_PULSE_6173128E SAMPLE FUNCTIONS -----------------------*/
    function void abr_reg__intr_block_t__intr_count_incr_t_pulse_6173128e::sample(uvm_reg_data_t  data,
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

    function void abr_reg__intr_block_t__intr_count_incr_t_pulse_6173128e::sample_values();
        if (get_coverage(UVM_CVR_REG_BITS)) begin
            foreach(pulse_bit_cg[bt]) this.pulse_bit_cg[bt].sample(pulse.get_mirrored_value() >> bt);
        end
        if (get_coverage(UVM_CVR_FIELD_VALS)) begin
            this.fld_cg.sample( pulse.get_mirrored_value()   );
        end
    endfunction

`endif