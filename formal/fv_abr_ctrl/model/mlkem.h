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

#ifndef MLKEM_H
#define MLKEM_H


#include <array>
#include "Interfaces.h"


#define ADDR_BITS          15
#define IMMEDIATE_BITS     16
#define SIPO_CHUNK_SIZE    64
#define SIPO_MAX_SIZE   20736
#define EK_NUM_BYTES      1568
#define CT_NUM_BYTES      1568

#define ADDR_TYPE sc_biguint<ADDR_BITS>                                     // Address type used in the design 

#define ADDR_PORT(addr_name) shared_in<ADDR_TYPE> addr_name##_in

#define GET_ADDR(addr_name) \
  ADDR_TYPE addr_name; \
  addr_name##_in->get(addr_name)

#define ADDRS_PORT(addrs_name, size) shared_in<std::array<ADDR_TYPE, size>> addrs_name##_in

#define GET_ADDRS(addrs_name, size) \
  std::array<ADDR_TYPE, size> addrs_name; \
  addrs_name##_in->get(addrs_name)

#define WAIT_UNTIL_DONE(done_port_name, state_name) \
  do { \
    insert_state(state_name); \
    done_port_name->get(subcomponent_done); \
  } while (!subcomponent_done)

#define WAIT_UNTIL_DONE_EX(done_port_name,sig_name, state_name) \
  do { \
    insert_state(state_name); \
    if(sig_name){ \
      subcomponent_done = true;\
    }\
    else {\
    done_port_name->get(subcomponent_done); \
    }\
  } while (!subcomponent_done)

  #define WAIT_UNTIL_DONE_SAMPLE(done_port_name, state_name,piso_vld_in,piso_data_in,register) \
  do { \
    insert_state(state_name); \
    piso_vld_in -> get(piso_vld);\
    piso_data_in -> get(sampled_value);\
    if(piso_vld){\
      register = sampled_value.range(511,0);\
    }\
    done_port_name->get(subcomponent_done); \
  } while (!subcomponent_done)

#define WAIT_FOR_SUBS(done_port_name1,done_port_name2, state_name) \
  do { \
    insert_state(state_name); \
    done_port_name1->get(subcomponent_done_1); \
    done_port_name2->get(subcomponent_done_2); \
  } while (!(subcomponent_done_1 && subcomponent_done_2 ))

enum class InstructionType {
  NoOp,
  MlkemKeygen,
  MlkemkeygenDecap,
  MlkemEncap,
  MlkemDecap
};

enum class SamplerMode {
  Sha512 = 0,
  Sha256 = 2,
  Cbd = 7,
  Shake256 = 1,
  RejBounded = 5,
  RejSampler = 3,
  ExpMask = 4,
  SampleInBall = 6
};

enum class NttMode {
  PwmSampler = 5,
  PwmAccuSampler = 6,
  PwmAccum = 4,
  Ntt = 1,
  Intt = 2,
  Pwa = 7,
  Pwm = 3,
  Pws = 8,
  None = 0
};

struct FromApiType {
  InstructionType instr;
  std::array<sc_biguint<32>,8>               seed;
  std::array<sc_biguint<32>,8>               seed_z;
  sc_biguint<256>               rho;
  sc_biguint<512>               sigma;
  sc_biguint<256>               sigma_z;
  sc_biguint<512> tr;
};

struct ToApiType {
  sc_biguint<512> tr;
  sc_biguint<39168> sk_out;
};

struct RegsType {
  sc_biguint<256>               rho;
  sc_biguint<512>               sigma;
  sc_biguint<256>               sigma_z;
};

struct ToSamplerType {
  SamplerMode mode;
  ADDR_TYPE destination;
};

struct NttType {
  NttMode mode;
  ADDR_TYPE operand1;
  ADDR_TYPE operand2;
  ADDR_TYPE destination;
  bool masking_en;
  bool shuffle_en;
};

struct RegsApiType {
  bool encaps_wr_ack;
  bool decaps_wr_ack;
  bool api_ek_reg_wr_dec;
  bool api_dk_reg_wr_dec;
  sc_uint<6> api_ek_reg_waddr;
  sc_uint<6> api_dk_reg_waddr;
  sc_biguint<32> api_ek_reg_wdata;
  sc_biguint<32> api_dk_reg_wdata;
};

struct toCompressType {
  sc_uint<2> mode;
  sc_uint<3> poly;
  bool compare_mode_o;
  ADDR_TYPE src0;
  ADDR_TYPE src1;
  ADDR_TYPE dest;
};

struct to_keccakType{
  sc_biguint<SIPO_CHUNK_SIZE> data;
  sc_uint<8> strobe;
};

struct toDeCompressType {
  sc_uint<2> mode;
  sc_uint<3> poly;
  ADDR_TYPE src0;
  ADDR_TYPE src1;
  ADDR_TYPE dest;
};

sc_biguint<SIPO_CHUNK_SIZE> getChunk(sc_biguint<SIPO_MAX_SIZE> whole_value, sc_uint<16> chunk_idx)  {

//  for (sc_uint<16> current_chunk_idx = 0; current_chunk_idx < chunk_idx && current_chunk_idx < 324; ++current_chunk_idx) {
    whole_value >>= (SIPO_CHUNK_SIZE * chunk_idx);
//  }

  return whole_value.range(SIPO_CHUNK_SIZE - 1, 0);
}

sc_biguint<SIPO_CHUNK_SIZE> func_concat_seed(std::array<sc_biguint<32>,8> whole_value, sc_uint<3> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[((chunk_idx << 1)|1)];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}


SC_MODULE(mlkem_abr_ctrl) {
 public:
  SC_CTOR(mlkem_abr_ctrl) {
    SC_THREAD(ctrl)
  }

  // Interface to the API registers
  shared_in<FromApiType> api_in;
  master_out<ToApiType> api_out;

  // Different constant register IDs; used as operands for certain operations
  ADDR_PORT(mlkem_rho_sigma_reg_id);
  ADDR_PORT(mlkem_sigma_id);
  ADDR_PORT(mlkem_rho_id);
  ADDR_PORT(mlkem_as0_addr);
  ADDR_PORT(mlkem_ek_addr);
  ADDR_PORT(mlkem_dk_addr);
  
  ADDR_PORT(mlkem_k_r_reg_id);
  ADDR_PORT(mlkem_msg_mem_addr);
  ADDR_PORT(mlkem_k_reg_id);
  ADDR_PORT(mlkem_tr_reg_id);
  ADDR_PORT(mlkem_c1_addr);
  ADDR_PORT(mlkem_c2_addr);
  ADDR_PORT(mlkem_src_dk_mem);
  ADDR_PORT(mlkem_src_ek_mem);
  ADDR_PORT(mlkem_src_c1_mem);
  ADDR_PORT(mlkem_src_c2_mem);
  ADDR_PORT(mlkem_src_msg_mem);
  ADDR_PORT(su_addr);
  ADDR_PORT(su_masked_addr);
  ADDR_PORT(v_addr);
  ADDR_PORT(ay_addr);
  ADDR_PORT(as_addr);
  ADDR_PORT(ty_addr);
  ADDR_PORT(ty_masked_addr);
  ADDR_PORT(e2_addr);
  ADDR_PORT(mu_addr);
  // Various memory addresses
  ADDRS_PORT(s_addrs,4);
  ADDRS_PORT(e_addrs,4);
  ADDRS_PORT(y_addrs,4);
  ADDRS_PORT(t_addrs,4);
  ADDRS_PORT(u_addrs,4);
  ADDRS_PORT(up_addrs,4);

  master_out<to_keccakType> to_keccak;
  shared_in<bool> to_keccak_rdy;
  shared_in<sc_biguint<1600>> from_keccak_piso;
  shared_in<bool> from_keccak_piso_vld_in;

  blocking_out<ToSamplerType> to_sampler;
  shared_in<bool> sampler_done_in;

  blocking_out<NttType> to_ntt;
  shared_in<bool> ntt_done_in;

  blocking_out<toCompressType> to_compress;
  shared_in<bool> compress_done_in;

  blocking_out<toDeCompressType> to_decompress;
  shared_in<bool> decompress_done_in;

  shared_out<bool> sha3_start_o;
  shared_out<bool> msg_start_o;
  shared_in<RegsApiType> regs_api_in;

 private:
  RegsType registers;
  RegsApiType regs_api;



  [[noreturn]] void ctrl() {
    sc_uint<16> sipo_chunk_idx;
    to_keccakType to_keccak_reg;
    FromApiType from_api;
    ToApiType to_api;
    bool subcomponent_done            = false;
    bool subcomponent_done_1          = false;
    bool subcomponent_done_2          = false;
    bool unused                       = false;
    bool mlkem_keygen_decaps_process  = false;
    bool mlkem_decaps_end_process     = false;
    bool ntt_sample_done              = false;
    sc_biguint<256> sigma_reg = 0, tr_reg = 0,rho_reg = 0;
    regs_api = {false,false,false,false,0,0,0,0};
    bool piso_vld = false;
    sha3_start_o -> set(false);
    msg_start_o -> set(false);
    sc_biguint<64> sk_ram_data = 0;
    sc_biguint<1600> sampled_value = 0, intermediate_value = 0;
    sc_uint<4> N = 0;
    sc_uint<4> cbd_idx = 0;

    while (true) {
      // Wait for a new top-level command
      do {
        insert_state("idle");
        api_in->get(from_api);
        regs_api_in->get(regs_api);

      } while (from_api.instr == InstructionType::NoOp);
      GET_ADDR(mlkem_rho_sigma_reg_id);
      GET_ADDR(mlkem_sigma_id);
      GET_ADDR(mlkem_rho_id);
      GET_ADDR(mlkem_as0_addr);
      GET_ADDR(mlkem_ek_addr);
      GET_ADDR(mlkem_dk_addr);
      GET_ADDR(mlkem_k_r_reg_id);
      GET_ADDR(mlkem_msg_mem_addr);
      GET_ADDR(mlkem_k_reg_id);
      GET_ADDR(mlkem_tr_reg_id);
      GET_ADDR(mlkem_c1_addr);
      GET_ADDR(mlkem_c2_addr);
      GET_ADDR(mlkem_src_dk_mem);
      GET_ADDR(mlkem_src_ek_mem);
      GET_ADDR(mlkem_src_c1_mem);
      GET_ADDR(mlkem_src_c2_mem);
      GET_ADDR(mlkem_src_msg_mem);
      GET_ADDR(su_addr);
      GET_ADDR(su_masked_addr);
      GET_ADDR(v_addr);
      GET_ADDR(ay_addr);
      GET_ADDR(as_addr);
      GET_ADDR(ty_addr);
      GET_ADDR(ty_masked_addr);
      GET_ADDR(e2_addr);
      GET_ADDR(mu_addr);
      // Various memory addresses
      GET_ADDRS(s_addrs,4);
      GET_ADDRS(e_addrs,4);
      GET_ADDRS(y_addrs,4);
      GET_ADDRS(t_addrs,4);
      GET_ADDRS(u_addrs,4);
      GET_ADDRS(up_addrs,4);

      // Work off the sequence of computations to perform the current command
      if (from_api.instr == InstructionType::MlkemKeygen || from_api.instr == InstructionType::MlkemkeygenDecap) {
        /////////////////////////////////////
        // Algorithm 13 Step 1: G(d||K)
        // DUV abr_seq: MLKEM_KG_S + 0
        mlkem_keygen_decaps_process = false;
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_keygen_rnd_seed_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true); 
        // rnd_seed = Keccak(entropy || counter)
        insert_state("mlkem_keygen_rnd_seed_start");
        msg_start_o -> set(false);
        api_in->get(from_api);
        insert_state("mlkem_keygen_write_seed_init");
        to_keccak_reg.data = func_concat_seed(from_api.seed, sipo_chunk_idx.range(1,0));//seed_d_reg from the abr_reg sampler_Src offset
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);//seed_d_reg from the abr_reg sampler_Src offset
        
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
          api_in->get(from_api);
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_write_seed");
          to_keccak_reg.data = func_concat_seed(from_api.seed, sipo_chunk_idx.range(1,0));//seed_d_reg from the abr_reg sampler_Src offset
          to_keccak_reg.strobe = 0xff; 
          to_keccak->master_write(to_keccak_reg);//seed_d_reg from the abr_reg sampler_Src offset
        }
        WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_write_seed_immediate");
        to_keccak_reg.data = 0x0004; // additional immediate value
        to_keccak_reg.strobe = 0x01; // since only first byte is
        to_keccak->master_write(to_keccak_reg); // additional immediate value 
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_write_seed_msg_done");
        sipo_chunk_idx = 0;
        to_sampler->try_write({ .mode = SamplerMode::Sha512, .destination = mlkem_rho_sigma_reg_id },
            unused, "mlkem_keygen_seed_sha_sampling_start");
        WAIT_UNTIL_DONE_SAMPLE(sampler_done_in, "mlkem_keygen_seed_sha_sampling", 
          from_keccak_piso_vld_in, from_keccak_piso, intermediate_value);
        sigma_reg = intermediate_value.range(511,256);
        rho_reg = intermediate_value.range(255,0);
        /////////////////////
        // step 2: N <- 0
        // step 8 to 15: covering CBD
        // for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++) 9: ▷ generate 𝐬 ∈ (ℤ256𝑞)𝑘
        //  9: 𝐬[𝑖] ← SamplePolyCBD𝜂1 (PRF𝜂1 (𝜎, 𝑁 )) ▷ 𝐬[𝑖] ∈ ℤ256 sampled from CBD
        //  10: 𝑁 ← 𝑁 + 1
        //  11: end for
        //  12: for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++)  ▷ generate 𝐞 ∈ (ℤ256𝑞)𝑘
        //  13: 𝐞[𝑖] ← SamplePolyCBD𝜂1 (PRF𝜂1 (𝜎, 𝑁 ))  ▷ 𝐞[𝑖] ∈ ℤ256 sampled from CBD
        //  14: 𝑁 ← 𝑁 + 1
        //  15: end for
        // DUV abr_seq: MLKEM_KG_S + 1 to MLKEM_KG_S + 8
        N = 0;
        for(N =0 ;N < 8 ;++N){
          sha3_start_o -> set(true);
          msg_start_o -> set(false);
          insert_state("mlkem_keygen_cbd_SHA3_START");
          sha3_start_o -> set(false);
          msg_start_o -> set(true); 
          insert_state("mlkem_keygen_cbd_msg_start");
          msg_start_o -> set(false);
          sipo_chunk_idx = 0;
          insert_state("mlkem_keygen_cbd_write_msg_init");
          to_keccak_reg.data = getChunk(sigma_reg, sipo_chunk_idx.range(1,0));
          to_keccak_reg.strobe = 0xff; // since only first 8
          to_keccak->master_write(to_keccak_reg);
          
          for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
            WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_cbd_write_msg");
            to_keccak_reg.data = getChunk(sigma_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_cbd_write_immediate");
          to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>(N);
          to_keccak_reg.strobe = 0x01; // since only first 4 bytes
          to_keccak->master_write(to_keccak_reg);
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_cbd_write_msg_done");
          sipo_chunk_idx = 0;
          to_sampler->try_write({ .mode = SamplerMode::Cbd, .destination = (N < 4? s_addrs.at(N) : e_addrs.at(sc_uint<2>(N-4))) },
              unused, "mlkem_keygen_cbd_sampling_start");

          WAIT_UNTIL_DONE(sampler_done_in, "mlkem_keygen_cbd_sampling");
       
        }
        N = 0;
        ////////////////////////////////////////
        // 16: 𝐬 ← NTT(𝐬)̂ ▷ run NTT 𝑘 times (once for each coordinate of 𝐬)
        // 17: ̂ 𝐞 ← NTT(𝐞)▷ run NTT 𝑘 times
        // DuV abr_seq: MLKEM_KG_S + 9 to MLKEM_KG_S + 16
        sc_uint<4> mlkem_keygen_ntt_idx = 0;
        for (mlkem_keygen_ntt_idx = 0; mlkem_keygen_ntt_idx < 8; ++mlkem_keygen_ntt_idx) {
          insert_state("mlkem_keygen_ntt_idle");
          
          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 =( mlkem_keygen_ntt_idx < 4 ?s_addrs.at(mlkem_keygen_ntt_idx):e_addrs.at(sc_uint<2>(mlkem_keygen_ntt_idx-4))) , .operand2 = 0,
              .destination = (mlkem_keygen_ntt_idx < 4 ?s_addrs.at(mlkem_keygen_ntt_idx):e_addrs.at(sc_uint<2>(mlkem_keygen_ntt_idx-4))), .masking_en = false, .shuffle_en = true}, unused, "mlkem_keygen_ntt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_keygen_ntt");
        }
        ////////////////////////////////
        // Step 3 to 7: 
        // for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++) ▷ generate matrix 𝐀∈ (ℤ256 ̂𝑞 )𝑘×𝑘
        // 4: for (𝑗 ← 0; 𝑗 < 𝑘; 𝑗 ++)
        //  5: 𝐀[𝑖, 𝑗] ← SampleNTT(𝜌‖𝑗‖𝑖) ▷ 𝑗 and 𝑖 are bytes 33 and 34 of the input
        // 6: end for
        // 7: end for
        // And Step 18: 
        //  ̂ 18: 𝐭 ← 𝐀 ∘ 𝐬 + ̂ 𝐞̂ 
        // DUV abr_seq: MLKEM_KG_S + 17 to MLKEM_KG_S + 36
        mlkem_keygen_ntt_idx = 0;
        sc_uint<3> mlkem_keygen_pw_idx = 0;
        for (mlkem_keygen_pw_idx = 0; mlkem_keygen_pw_idx < 4; ++mlkem_keygen_pw_idx) {
          sha3_start_o -> set(true);
          msg_start_o -> set(false);
          insert_state("mlkem_keygen_pwm_write_rho_SHA3_START");
          sha3_start_o -> set(false);
          msg_start_o -> set(true);
          insert_state("mlkem_keygen_pwm_write_rho_start");
          msg_start_o -> set(false);
          sipo_chunk_idx = 0;
          insert_state("mlkem_keygen_pwm_write_rho_init");
          to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
          to_keccak_reg.strobe = 0xff; // since only first 8
          to_keccak->master_write(to_keccak_reg);
          for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_pwm_write_rho");
              to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
              to_keccak_reg.strobe = 0xff; 
              to_keccak->master_write(to_keccak_reg);
            }
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_pwm_write_immediate");
          to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>(mlkem_keygen_pw_idx == 0? sc_biguint<SIPO_CHUNK_SIZE>(0) : (sc_biguint<SIPO_CHUNK_SIZE>(mlkem_keygen_pw_idx) << sc_biguint<SIPO_CHUNK_SIZE>(8)));
          to_keccak_reg.strobe = 0x03; // since only first byte is
          to_keccak->master_write(to_keccak_reg);
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_pwm_write_immediate_msg_done");
          sipo_chunk_idx = 0;
          to_sampler->try_write({ .mode = SamplerMode::RejSampler,
                .destination = as_addr },
                unused, "mlkem_keygen_pwm_rejection_sampling_start");

          to_ntt->try_write({ .mode = (NttMode::PwmSampler),
                .operand1 = mlkem_rho_id,
                .operand2 = s_addrs.at(0), .destination = as_addr, .masking_en = false, .shuffle_en = false }, unused, "mlkem_keygen_pwm_ntt_start");

          WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "mlkem_keygen_pwm");
          sc_uint<3>  mlkem_keygen_pwa_idx = 0;
          for(mlkem_keygen_pwa_idx = 0; mlkem_keygen_pwa_idx < 3; ++mlkem_keygen_pwa_idx) {
            sha3_start_o -> set(true);
            msg_start_o -> set(false);
            insert_state("mlkem_keygen_pwm_a_write_rho_SHA3_START");
            sha3_start_o -> set(false);
            msg_start_o -> set(true);
            insert_state("mlkem_keygen_pwm_a_write_rho_start");
            msg_start_o -> set(false);
            sipo_chunk_idx = 0;
            insert_state("mlkem_keygen_pwm_a_write_rho_init");
            to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
            for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_pwm_a_write_rho");
              to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
              to_keccak_reg.strobe = 0xff;
              to_keccak->master_write(to_keccak_reg);
            }
            
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_pwm_a_write_immediate");
            to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>((sc_biguint<SIPO_CHUNK_SIZE>(mlkem_keygen_pw_idx) << sc_biguint<SIPO_CHUNK_SIZE>(8)) | (mlkem_keygen_pwa_idx+1));
            to_keccak_reg.strobe = 0x03; // since only first byte is
            to_keccak->master_write(to_keccak_reg);
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_pwm_a_write_immediate_msg_done");
            sipo_chunk_idx = 0;
            to_sampler->try_write({ .mode = SamplerMode::RejSampler,
                .destination = as_addr },
                unused, "mlkem_keygen_pwm_a_rejection_sampling_start");

            to_ntt->try_write({ .mode = (NttMode::PwmAccuSampler),
                .operand1 = mlkem_rho_id,
                .operand2 = s_addrs.at(sc_uint<2>(mlkem_keygen_pwa_idx+1)), .destination = as_addr, .masking_en = false, .shuffle_en = false  }, unused, "mlkem_keygen_pwm_a_start");

            WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "mlkem_keygen_pwm_a");
          }
          mlkem_keygen_pwa_idx = 0;
          // Here is the addition of step 18 being done.
          insert_state("mlkem_Keygen_pwa_idle");
          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = as_addr, .operand2 = e_addrs.at(mlkem_keygen_pw_idx),
              .destination = t_addrs.at(mlkem_keygen_pw_idx), .masking_en = false, .shuffle_en = true   }, unused, "mlkem_Keygen_pwa_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_Keygen_pwa");

        }
        mlkem_keygen_pw_idx = 0;
        //////////////////////////
        // step 19: MLKEM_KG_S + 37
        // 19: ekPKE ← ByteEncode12(𝐭)‖𝜌 ▷ run ByteEncode12 𝑘 times, then append 𝐀-seed
       // DUV abr_seq: 
        insert_state("mlkem_keygen_compress_ek_idle");
        to_compress->try_write({ .mode = 3, .poly = 4 , .compare_mode_o = false, .src0 = t_addrs.at(0) ,.src1 = 0 ,.dest = mlkem_ek_addr  }, unused, "mlkem_keygen_compress_ek_start");
        /////////////////////////////
        // step 20: MLKEM_KG_S + 38
        // 20: dkPKE ← ByteEncode12(𝐬) ̂ ▷ run ByteEncode12 𝑘 times
        WAIT_UNTIL_DONE(compress_done_in, "mlkem_keygen_compress_ek");

        insert_state("mlkem_keygen_compress_dk_idle");
        to_compress->try_write({ .mode = 3, .poly = 4 , .compare_mode_o = false , .src0 = s_addrs.at(0) ,.src1 = 0 ,.dest = mlkem_dk_addr   }, unused, "mlkem_keygen_compress_dk_start");

        WAIT_UNTIL_DONE(compress_done_in, "mlkem_keygen_compress_dk");
      ////////////////////////////////
      // Algorithm 16. step 3:
      // 3: dk ← (dkPKE‖ek‖H(ek)‖𝑧) ▷ KEM decaps key includes PKE decryption key
      // DUV abr_seq: MLKEM_KG_S + 39
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_keygen_SHA256_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("mlkem_keygen_write_ek_START");
        msg_start_o -> set(false);
        sipo_chunk_idx = 0;
        insert_state("mlkem_keygen_write_ek_init");
        to_keccak_reg.data = sk_ram_data;
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (; sipo_chunk_idx < (EK_NUM_BYTES/8)+1; ++sipo_chunk_idx) { 
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_keygen_write_ek");
          if(sipo_chunk_idx < ((EK_NUM_BYTES/8)-4)){
            to_keccak_reg.data = sk_ram_data;
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
          else{
            to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = ((sipo_chunk_idx == (EK_NUM_BYTES/8)) ?0x00: 0xff); // since only first 8
          to_keccak->master_write(to_keccak_reg);
          }
        }
            
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_keygen_write_ek_msg_done");//: Strobe 0
        sipo_chunk_idx = 0;
        
        to_sampler->try_write({ .mode = SamplerMode::Sha256,
                .destination = mlkem_tr_reg_id },
                unused, "mlkem_keygen_ek_sampling_start");
        WAIT_UNTIL_DONE(sampler_done_in, "mlkem_keygen_ek_sampling");

        mlkem_keygen_decaps_process = (from_api.instr == InstructionType::MlkemkeygenDecap);
      }

    
      if(from_api.instr == InstructionType::MlkemDecap || (from_api.instr == InstructionType::MlkemkeygenDecap && mlkem_keygen_decaps_process )) {
        //////////////////////////////////
        // This step is to ensure that
        // Input to the decaps is valid if not error is triggered
        // DUV abr_Seq: MLKEM_DECAPS_S + 0

        mlkem_keygen_decaps_process = false;
        mlkem_decaps_end_process = false;
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_decap_SHA256_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("mlkem_decap_write_ek_START");
        msg_start_o -> set(false);
        sipo_chunk_idx = 0;
        insert_state("mlkem_decap_write_ek_init");
        to_keccak_reg.data = sk_ram_data;
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (; sipo_chunk_idx < (EK_NUM_BYTES/8)+1; ++sipo_chunk_idx) { 
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_decap_write_ek");
          if(sipo_chunk_idx < ((EK_NUM_BYTES/8)-4)){
            to_keccak_reg.data = sk_ram_data;
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
          else{
            to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = ((sipo_chunk_idx == (EK_NUM_BYTES/8)) ?0x00: 0xff); // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_decap_write_ek_msg_done");//: Strobe 0
        sipo_chunk_idx = 0;
        
        to_sampler->try_write({ .mode = SamplerMode::Sha256,
                .destination = mlkem_tr_reg_id },
                unused, "mlkem_decap_ek_sampling_start");

        WAIT_UNTIL_DONE(sampler_done_in, "mlkem_decap_ek_sampling");
        //////////////////////////
        // Algorithm 15. step  5
        // 5: 𝐬 ← ByteDecode12(dkPKE)
        // DUV abr_seq: MLKEM_DECAPS_S + 1
        insert_state("mlkem_decap_decompress_s0_idle");     
        to_decompress->try_write({ .mode = 03, .poly = 04, .src0 = mlkem_src_dk_mem ,.src1 = 0 ,.dest = s_addrs.at(0) }, unused, "mlkem_decap_decompress_s0_start");

        WAIT_UNTIL_DONE(decompress_done_in, "mlkem_decap_decompress_s0");
        //////////////////////////
        // Algorithm 15. step  3
        //3: 𝐮′ ← Decompress𝑑𝑢(ByteDecode𝑑𝑢(c1))
        // DUV abr_seq: MLKEM_DECAPS_S + 2
        insert_state("mlkem_decap_decompress_u0_idle");
        to_decompress->try_write({ .mode = 02, .poly = 04, .src0 = mlkem_src_c1_mem ,.src1 = 0 ,.dest = u_addrs.at(0) }, unused, "mlkem_decap_decompress_u0_start");

        WAIT_UNTIL_DONE(decompress_done_in, "mlkem_decap_decompress_u0");
        //////////////////////////
        // Algorithm 15. step  4
        //3: v′ ← Decompress𝑑v(ByteDecode𝑑v(c2))
        // DUV abr_seq: MLKEM_DECAPS_S + 3
        insert_state("mlkem_decap_decompress_v_idle");
        to_decompress->try_write({ .mode = 01, .poly = 01, .src0 = mlkem_src_c2_mem ,.src1 = 0 ,.dest = v_addr }, unused, "mlkem_decap_decompress_v_start");

        WAIT_UNTIL_DONE(decompress_done_in, "mlkem_decap_decompress_v");
        ///////////////////////////
        // step 6:
        // 𝑤 ← 𝑣′− NTT−1(𝐬⊺̂ ∘ NTT(𝐮′)) 
        // DUV abr_seq: MLKEM_DECAPS_S + 4 to MLKEM_DECAPS_S + 13
        // First NTT of u and pwm of a then inverse ntt atlast
        // PWS i.e point wise substraction
        sc_uint<3> mlkem_decap_ntt_idx = 0;
        for (mlkem_decap_ntt_idx = 0; mlkem_decap_ntt_idx < 4; ++mlkem_decap_ntt_idx) {
          insert_state("mlkem_decap_ntt_idle");
          
          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = u_addrs.at(mlkem_decap_ntt_idx) , .operand2 = 0,
              .destination = up_addrs.at(mlkem_decap_ntt_idx), .masking_en = false, .shuffle_en = true    }, unused, "mlkem_decap_ntt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_decap_ntt");
        }
        mlkem_decap_ntt_idx = 0;

        insert_state("mlkem_decap_pwm_su_idle");
        to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = s_addrs.at(0), .operand2 = up_addrs.at(0),
              .destination = su_masked_addr, .masking_en = true, .shuffle_en = true   }, unused, "mlkem_decap_pwm_su_start");

        WAIT_UNTIL_DONE(ntt_done_in, "mlkem_decap_pwm_su");
        sc_uint<2> mlkem_decap_pwma_idx = 0;
        for (mlkem_decap_pwma_idx = 0; mlkem_decap_pwma_idx < 3; ++mlkem_decap_pwma_idx) {
          insert_state("mlkem_decap_pwma_su_idle");
          to_ntt->try_write({ .mode = NttMode::PwmAccum, .operand1 = s_addrs.at(sc_uint<2>(mlkem_decap_pwma_idx+1)), .operand2 = up_addrs.at(sc_uint<2>(mlkem_decap_pwma_idx+1)),
              .destination = su_masked_addr, .masking_en = true, .shuffle_en = true   }, unused, "mlkem_decap_pwma_su_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_decap_pwma_su");
        }
        mlkem_decap_pwma_idx = 0;
        insert_state("mlkem_decap_intt_su_idle");
        to_ntt->try_write({ .mode = NttMode::Intt, .operand1 =su_masked_addr, .operand2 = 0,
              .destination = su_addr, .masking_en = true, .shuffle_en = true  }, unused, "mlkem_decap_intt_su_start");

        WAIT_UNTIL_DONE(ntt_done_in, "mlkem_decap_intt_su");

        insert_state("mlkem_decap_pws_su_idle");
        to_ntt->try_write({ .mode = NttMode::Pws, .operand1 = su_addr, .operand2 = v_addr,
              .destination = v_addr, .masking_en = false, .shuffle_en = true  }, unused, "mlkem_decap_pws_su_start");

        WAIT_UNTIL_DONE(ntt_done_in, "mlkem_decap_pws_su");
        ///////////////////////////////
        // step 7:
        // 𝑚 ← ByteEncode1(Compress1(𝑤)) 
        // DUV abr_seq: MLKEM_DECAPS_S + 14
        insert_state("mlkem_decap_compress_msg_idle");
        to_compress->try_write({ .mode = 0, .poly = 1 , .compare_mode_o = false, .src0 = v_addr ,.src1 = 0 ,.dest = mlkem_msg_mem_addr   }, unused, "mlkem_decap_compress_msg_start");
        WAIT_UNTIL_DONE(compress_done_in, "mlkem_decap_compress_msg");
        mlkem_decaps_end_process = true;
      }

      if(from_api.instr == InstructionType::MlkemEncap || mlkem_decaps_end_process) {
         ///////////////////////////////
        // Algorithm 14. step 2
        // 𝐭 ← ByteDecode12(ekPKE[0 ∶ 384𝑘]) ▷ run ByteDecode12 𝑘 times to decode 𝐭 ∈ (ℤ256𝑞
        // DUV abr_seq: MLKEM_ENCAPS_S + 0
        
        to_decompress->try_write({ .mode = 03 , .poly = 04, .src0 = mlkem_src_ek_mem,.src1 = 0,.dest = t_addrs.at(0) }, unused, "mlkem_encap_decompress_t0_start");
        WAIT_UNTIL_DONE(decompress_done_in, "mlkem_encap_decompress_t0");
         ///////////////////////////////
        // Input check pg no. 36 FIPS 203 (7.1)
        // DUV abr_seq: MLKEM_ENCAPS_S + 1
        to_compress->try_write({ .mode = 03 , .poly = 04 , .compare_mode_o = !mlkem_decaps_end_process, .src0 = t_addrs.at(0) ,.src1 = 0 ,.dest = mlkem_ek_addr   }, unused, "mlkem_encap_compress_first_start");
        WAIT_UNTIL_DONE(compress_done_in, "mlkem_encap_compress_first");
        ///////////////////////////////
        // Algorithm 17. step 1
        // 1: (𝐾, 𝑟) ← G(𝑚‖H(ek))  ▷ derive shared secret key 𝐾 and randomness 𝑟
        // DUV abr_seq: MLKEM_ENCAPS_S + 2 to MLKEM_ENCAPS_S + 4
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_encap_SHA256_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("mlkem_encap_write_ek_START");
        msg_start_o -> set(false);
        sipo_chunk_idx = 0;
        insert_state("mlkem_encap_write_ek_init");
        to_keccak_reg.data = sk_ram_data;
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (; sipo_chunk_idx < (EK_NUM_BYTES/8)+1; ++sipo_chunk_idx) { 
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_write_ek");
          if(sipo_chunk_idx < ((EK_NUM_BYTES/8)-4)){
            to_keccak_reg.data = sk_ram_data;
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
          else{
            to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = ((sipo_chunk_idx == (EK_NUM_BYTES/8)) ?0x00: 0xff); // since only first 8
            to_keccak->master_write(to_keccak_reg);
          }
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_ek_msg_done"); //: Strobe 0
        sipo_chunk_idx = 0;
        
        to_sampler->try_write({ .mode = SamplerMode::Sha256,
                .destination = mlkem_tr_reg_id },
                unused, "mlkem_encap_ek_sampling_start");
        WAIT_UNTIL_DONE_SAMPLE(sampler_done_in, "mlkem_encap_ek_sampling", 
          from_keccak_piso_vld_in, from_keccak_piso, intermediate_value);
        tr_reg = intermediate_value.range(255,0);
        
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_encap_ld_SHA512_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("mlkem_encap_write_msg_START");
        msg_start_o -> set(false);
        sipo_chunk_idx = 0;
        insert_state("mlkem_encap_write_msg_init");
        to_keccak_reg.data = sk_ram_data;
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (; sipo_chunk_idx < 5; ++sipo_chunk_idx) { 
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_write_msg");
          to_keccak_reg.data = sk_ram_data;
          to_keccak_reg.strobe = ((sipo_chunk_idx == (4)) ?0x00: 0xff); // since only first 8
          to_keccak->master_write(to_keccak_reg);
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_msg_done"); //: strobe 0
        sipo_chunk_idx = 0;

        insert_state("mlkem_encap_write_msg_wait");

        insert_state("mlkem_encap_write_tr_msg_init");
        to_keccak_reg.data = getChunk(tr_reg,sipo_chunk_idx.range(1,0));
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 5; ++sipo_chunk_idx) { // Rohith: Because the design takes one extra byte and passes strobe for the last msg valid bytes
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_tr_msg");
          to_keccak_reg.data = getChunk(tr_reg,sipo_chunk_idx.range(1,0));
          to_keccak_reg.strobe = ((sipo_chunk_idx == (4)) ?0x00: 0xff); // since only first 8
          to_keccak->master_write(to_keccak_reg);
        }
        sipo_chunk_idx= sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_tr_msg_done");// : strobe 0
        sipo_chunk_idx = 0;
        
        to_sampler->try_write({ .mode = SamplerMode::Sha512, .destination = mlkem_k_r_reg_id }, unused,
            "mlkem_encap_sha512");
        
        WAIT_UNTIL_DONE_SAMPLE(sampler_done_in, "mlkem_encap_sha512_done", 
          from_keccak_piso_vld_in, from_keccak_piso, intermediate_value);
        sigma_reg = intermediate_value.range(511,256);
        /////////////////////
        // Algorithm 14. step 9 to 17
        // 9: for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++) ▷ generate 𝐲 ∈ (ℤ256𝑞)𝑘
        // 10: 𝐲[𝑖] ← SamplePolyCBD𝜂1 (PRF𝜂1 (𝑟, 𝑁 )) ▷ 𝐲[𝑖] ∈ ℤ256 sampled from CBD
        // 11: 𝑁 ← 𝑁 + 1
        // 12: end for
        // 13: for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++) ▷ generate 𝐞𝟏 ∈ (ℤ256𝑞)𝑘
        // 14: 𝐞𝟏[𝑖] ← SamplePolyCBD𝜂2 (PRF𝜂2 (𝑟, 𝑁 )) ▷ 𝐞𝟏[𝑖] ∈ ℤ256 sampled from CBD𝑞
        // 15: 𝑁 ← 𝑁 + 1
        // 16: end for
        // 17: 𝑒2 ← SamplePolyCBD𝜂2 (PRF𝜂2 (𝑟, 𝑁 ))
        // DUV abr_seq: MLKEM_ENCAPS_S + 5 to MLKEM_ENCAPS_S + 13
        cbd_idx = 0;
        for(cbd_idx =0 ;cbd_idx < 9 ;++cbd_idx){
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("mlkem_encap_y_e1_e2_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true); 
        
        insert_state("mlkem_encap_y_e1_e2_msg_start");
        msg_start_o -> set(false);
        sipo_chunk_idx = 0;
        insert_state("mlkem_encap_y_e1_e2_write_msg_init");
        to_keccak_reg.data = getChunk(sigma_reg, sipo_chunk_idx.range(1,0));
        to_keccak_reg.strobe = 0xff; // since only first 8
        to_keccak->master_write(to_keccak_reg);
        for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
          WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_y_e1_e2_write");
          to_keccak_reg.data = getChunk(sigma_reg, sipo_chunk_idx.range(1,0));
          to_keccak_reg.strobe = 0xff; // since only first 8
          to_keccak->master_write(to_keccak_reg);
        }
        WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_y_e1_e2_write_immediate");
        to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>(cbd_idx);
        to_keccak_reg.strobe = 0x01; // since only first byte is
        to_keccak->master_write(to_keccak_reg);
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_y_e1_e2_write_msg_done");
        sipo_chunk_idx = 0;
        to_sampler->try_write({ .mode = SamplerMode::Cbd, .destination = cbd_idx < 4? y_addrs.at(cbd_idx) : ((cbd_idx== 8) ? e2_addr: e_addrs.at(sc_uint<2>(cbd_idx-4))) },
            unused, "mlkem_encap_y_e1_e2_sha_sampling_start");
        
        WAIT_UNTIL_DONE(sampler_done_in, "mlkem_encap_y_e1_e2_sha_sampling");
        }
        cbd_idx= 0;

        ////////////////////////////////////
        // step 18:
        // 18: ̂ 𝐲 ← NTT(𝐲) ▷ run NTT 𝑘 times
        // DUV abr_seq: MLKEM_ENCAPS_S + 14 to MLKEM_ENCAPS_S + 17
        
        sc_uint<3> mlkem_encap_ntt_y_idx = 0;
        for (mlkem_encap_ntt_y_idx = 0; mlkem_encap_ntt_y_idx < 4; ++mlkem_encap_ntt_y_idx) {
          insert_state("mlkem_encap_ntt_y_idle");
          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = y_addrs.at(mlkem_encap_ntt_y_idx) , .operand2 = 0,
              .destination = y_addrs.at(mlkem_encap_ntt_y_idx), .masking_en = false, .shuffle_en = true }, unused, "mlkem_encap_ntt_y_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_ntt_y");
        }
        mlkem_encap_ntt_y_idx = 0;
        ///////////////////////////
        // Steps: 4 to 8 and 19 combined
        // 19: 𝐮 ← NTT−1(𝐀 ̂ ⊺ ∘ 𝐲) + 𝐞𝟏 ▷ run NTT−1 𝑘 timeŝ
        // 4: for (𝑖 ← 0; 𝑖 < 𝑘; 𝑖 ++) ▷ re-generate matrix 𝐀 ∈ (ℤ256𝑞 )𝑘×𝑘 sampled in Alg. 13
        // 5: for (𝑗 ← 0; 𝑗 < 𝑘; 𝑗 ++)
        // 6: 𝐀[𝑖, 𝑗] ← SampleNTT(𝜌‖𝑗‖𝑖) ▷ 𝑗 and 𝑖 are bytes 33 and 34 of the input
        // 7: end for
        // 8: end for
        // DUV abr_seq : MLKEM_ENCAPS_S + 18 to MLKEM_ENCAPS_S + 46

        sc_uint<3> mlkem_encap_pw_idx = 0;
        for (mlkem_encap_pw_idx = 0; mlkem_encap_pw_idx < 4; ++mlkem_encap_pw_idx) {
          sha3_start_o -> set(true);
          msg_start_o -> set(false);
          insert_state("mlkem_encap_pwm_write_rho_SHA3_START");
          sha3_start_o -> set(false);
          msg_start_o -> set(true);
          insert_state("mlkem_encap_pwm_write_rho_start");
          msg_start_o -> set(false);
          sipo_chunk_idx = 0;
          insert_state("mlkem_encap_pwm_write_rho_init");
          to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
          to_keccak_reg.strobe = 0xff; // since only first 8
          to_keccak->master_write(to_keccak_reg);
            for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_pwm_write_rho");
              to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
              to_keccak_reg.strobe = 0xff;
              to_keccak->master_write(to_keccak_reg);
            }
            
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_pwm_write_immediate");
          to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>(mlkem_encap_pw_idx);
          to_keccak_reg.strobe = 0x03; // since only first byte is
          to_keccak->master_write(to_keccak_reg);
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_pwm_write_immediate_msg_done");
          sipo_chunk_idx = 0;
          to_sampler->try_write({ .mode = SamplerMode::RejSampler,
                .destination = ay_addr },
                unused, "mlkem_encap_pwm_rejection_sampling_start");

          to_ntt->try_write({ .mode = (NttMode::PwmSampler),
                .operand1 = mlkem_rho_id,
                .operand2 = y_addrs.at(0), .destination = ay_addr, .masking_en = true, .shuffle_en = false  }, unused, "mlkem_encap_pwm_ntt_start");

          WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "mlkem_encap_pwm");
          sc_uint<3>  mlkem_encap_pwa_idx = 0;
          for(mlkem_encap_pwa_idx = 0; mlkem_encap_pwa_idx < 3; ++mlkem_encap_pwa_idx) {
            sha3_start_o -> set(true);
            msg_start_o -> set(false);
            insert_state("mlkem_encap_pwm_a_write_rho_SHA3_START");
            sha3_start_o -> set(false);
            msg_start_o -> set(true);
            insert_state("mlkem_encap_pwm_a_write_rho_start");
            msg_start_o -> set(false);
            sipo_chunk_idx = 0;
            insert_state("mlkem_encap_pwm_a_write_rho_init");
            to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
            for (; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_pwm_a_write_rho");
              to_keccak_reg.data = getChunk(rho_reg, sipo_chunk_idx.range(1,0));
              to_keccak_reg.strobe = 0xff;
              to_keccak->master_write(to_keccak_reg);
            }
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_pwm_a_write_immediate");
            to_keccak_reg.data = sc_biguint<SIPO_CHUNK_SIZE>((sc_biguint<SIPO_CHUNK_SIZE>(mlkem_encap_pwa_idx+1) << sc_biguint<SIPO_CHUNK_SIZE>(8)) | mlkem_encap_pw_idx);
            to_keccak_reg.strobe = 0x03; // since only first byte is
            to_keccak->master_write(to_keccak_reg);
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_pwm_a_write_immediate_msg_done");
            sipo_chunk_idx = 0;
            to_sampler->try_write({ .mode = SamplerMode::RejSampler,
                .destination = ay_addr },
                unused, "mlkem_encap_pwm_a_rejection_sampling_start");
            to_ntt->try_write({ .mode = (NttMode::PwmAccuSampler),
                .operand1 = mlkem_rho_id,
                .operand2 = y_addrs.at(mlkem_encap_pwa_idx+1), .destination = ay_addr, .masking_en = true, .shuffle_en = false  }, unused, "mlkem_encap_pwm_a_ntt_start");

            WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "mlkem_encap_pwm_a");
          }
          mlkem_encap_pwa_idx = 0;
          insert_state("mlkem_encap_intt_idle");

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = ay_addr, .operand2 = 0,
              .destination =ay_addr, .masking_en = true, .shuffle_en = true  }, unused, "mlkem_encap_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_intt");
          insert_state("mlkem_encap_pwa_idle");
          
          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = ay_addr, .operand2 = e_addrs.at(mlkem_encap_pw_idx),
              .destination = u_addrs.at(mlkem_encap_pw_idx), .masking_en = false, .shuffle_en = true  }, unused, "mlkem_encap_pwa_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_pwa");

          }
          mlkem_encap_pw_idx = 0;
          insert_state("mlkem_encap_pwm_ty_idle");
          
          to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = t_addrs.at(0), .operand2 = y_addrs.at(0),
              .destination = ty_masked_addr, .masking_en = true, .shuffle_en = true  }, unused, "mlkem_encap_pwm_ty_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_pwm_ty");
          sc_uint<3> mlkem_encap_pwma_ty_idx = 0;
          for(mlkem_encap_pwma_ty_idx = 0; mlkem_encap_pwma_ty_idx < 3; ++mlkem_encap_pwma_ty_idx) {
          insert_state("mlkem_encap_pwma_ty_idle");
          
          to_ntt->try_write({ .mode = NttMode::PwmAccum, .operand1 = t_addrs.at(sc_uint<2>(mlkem_encap_pwma_ty_idx+1)), .operand2 =  y_addrs.at(sc_uint<2>(mlkem_encap_pwma_ty_idx+1)),
              .destination = ty_masked_addr, .masking_en = true, .shuffle_en = true  }, unused, "mlkem_encap_pwma_ty_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_pwma_ty");
          }
          mlkem_encap_pwma_ty_idx = 0;
          insert_state("mlkem_encap_intt_v_idle");
          
          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = ty_masked_addr, .operand2 = 0,
              .destination = v_addr,.masking_en = true,.shuffle_en = true}, unused, "mlkem_encap_intt_v_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_intt_v");
          insert_state("mlkem_encap_decompress_mu_idle");
          /////////////////////////////
          // step 20:
          // 20: 𝜇 ← Decompress1(ByteDecode1(𝑚))
          // DUV abr_seq: MLKEM_ENCAPS_S + 47
          // 
          to_decompress->try_write({ .mode = 0, .poly = 1,.src0 = mlkem_src_msg_mem ,.src1 = 0, .dest = mu_addr }, unused, "mlkem_encap_decompress_mu_start");

          WAIT_UNTIL_DONE(decompress_done_in, "mlkem_encap_decompress_mu");
          /////////////////////////////
          // step 21:
          // 21: 𝑣 ← NTT−1(𝐭⊺̂ ∘ 𝐲) + 𝑒2 + 𝜇 
          // DUV abr_seq: MLKEM_ENCAPS_S + 47 and 48
          // 
          insert_state("mlkem_encap_pwa_e2_idle");
  
          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = mu_addr, .operand2 = e2_addr,
              .destination = e2_addr,.masking_en = false,.shuffle_en = true }, unused, "mlkem_encap_pwa_e2_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_pwa_e2");

          insert_state("mlkem_encap_pwa_v_idle");
          
          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = v_addr, .operand2 = e2_addr,
              .destination = v_addr,.masking_en = false,.shuffle_en = true }, unused, "mlkem_encap_pwa_v_start");

          WAIT_UNTIL_DONE(ntt_done_in, "mlkem_encap_pwa_v");
          /////////////////////////////
          // step 22:
          // 22: 𝑐1 ← ByteEncode𝑑𝑢(Compress𝑑𝑢(𝐮))
          // MLKEM_ENCAPS_S + 50
             insert_state("mlkem_encap_compress_c1_idle");
          
          to_compress->try_write({ .mode = 02 , .poly = 04 , .compare_mode_o = ((from_api.instr == InstructionType::MlkemkeygenDecap)||(from_api.instr == InstructionType::MlkemDecap))
            , .src0 = u_addrs.at(0) ,.src1 = 0 ,.dest = mlkem_c1_addr  }, unused, "mlkem_encap_compress_c1_start");

          WAIT_UNTIL_DONE(compress_done_in, "mlkem_encap_compress_c1");
            /////////////////////////////
          // step 23:
          // 23: 𝑐2 ← ByteEncode𝑑v(Compress𝑑v(v))
            // MLKEM_ENCAPS_S + 51
          insert_state("mlkem_encap_compress_c2_idle");
          
          to_compress->try_write({ .mode = 01, .poly = 01 , .compare_mode_o = ((from_api.instr == InstructionType::MlkemkeygenDecap)||(from_api.instr == InstructionType::MlkemDecap)) 
           , .src0 = v_addr ,.src1 = 0 ,.dest = mlkem_c2_addr }, unused, "mlkem_encap_compress_c2_start");

          WAIT_UNTIL_DONE(compress_done_in, "mlkem_encap_compress_c2");
          insert_state("mlkem_encap_end");
          ///////////////////////////////
          // Algorithm 18. step 7 to 11
          // 6:7: 𝐾 ← J(𝑧‖𝑐)
          // 8: 𝑐′ ← K-PKE.Encrypt(ekPKE, 𝑚′, 𝑟′) ▷ re-encrypt using the derived randomness 𝑟′
          // 9: if 𝑐 ≠ 𝑐′ then
          // 10: 𝐾′ ← 𝐾̄ ▷ if ciphertexts do not match, “implicitly reject”
          // 11: end if
          // 12: return 𝐾′
          // DUV abr_seq: MLKEM_DECAPS_CHK + 0 to MLKEM_DECAPS_E
          if(mlkem_decaps_end_process){
            sha3_start_o -> set(true);
            msg_start_o -> set(false);
            insert_state("mlkem_encap_ld_SHAKE256_START");
            sha3_start_o -> set(false);
            msg_start_o -> set(true);
            insert_state("mlkem_encap_write_msg_256_START");
            msg_start_o -> set(false);
            sipo_chunk_idx = 0;
            insert_state("mlkem_encap_write_msg_256_init");
            to_keccak_reg.data = func_concat_seed(from_api.seed_z, sipo_chunk_idx.range(1,0));
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);
            for (; sipo_chunk_idx < 5; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "mlkem_encap_write_msg_256");
              to_keccak_reg.data = func_concat_seed(from_api.seed_z, sipo_chunk_idx.range(1,0));
              to_keccak_reg.strobe = ((sipo_chunk_idx == (4)) ?0x00: 0xff); // since only first 8
              to_keccak->master_write(to_keccak_reg);
            }
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_msg_256_done"); // : strobe zero
            sipo_chunk_idx = 0;

            insert_state("mlkem_encap_write_msg_256_wait");
            insert_state("mlkem_encap_write_ct_msg_256_init");
            to_keccak_reg.data = sk_ram_data;
            to_keccak_reg.strobe = 0xff; // since only first 8
            to_keccak->master_write(to_keccak_reg);

             for (; sipo_chunk_idx < (CT_NUM_BYTES/8)+1; ++sipo_chunk_idx) { // Rohith: Because the design takes one extra byte and passes strobe for the last msg valid bytes
              WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_ct_msg_256");
                to_keccak_reg.data = (sk_ram_data);
                to_keccak_reg.strobe = ((sipo_chunk_idx == (CT_NUM_BYTES/8)) ?0x00: 0xff); // since only first 8
                to_keccak->master_write(to_keccak_reg);
            }
            sipo_chunk_idx= sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"mlkem_encap_write_ct_msg_done"); // : strobe 0
            sipo_chunk_idx = 0;
            //(mlkem_k_r_reg_id);
            to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = mlkem_k_reg_id }, unused,
            "mlkem_encap_ct_shake256");

            WAIT_UNTIL_DONE(sampler_done_in, "mlkem_encap_ct_shake256_done");
          }
        }
    }
  }
};

#endif