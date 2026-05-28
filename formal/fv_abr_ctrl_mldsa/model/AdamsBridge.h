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

#ifndef ADAMSBRIDGE_H
#define ADAMSBRIDGE_H


#include <array>
#include "Interfaces.h"


#define ADDR_BITS          15
#define IMMEDIATE_BITS     16
#define SIPO_CHUNK_SIZE    64
#define SIPO_MAX_SIZE   20736

#define ADDR_TYPE sc_biguint<ADDR_BITS>

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
  Keygen,
  Sign,
  Verify,
  KeygenSign
};

enum class SamplerMode {
  Shake256 = 1,
  RejBounded = 5,
  RejSampler = 3,
  ExpMask = 4,
  SampleInBall = 6
};

enum class NttMode {
  PwmSampler = 5,
  PwmAccuSampler = 6,
  Ntt = 1,
  Intt = 2,
  Pwa = 7,
  Pwm = 3,
  Pws = 8 
};

struct FromApiType {
  InstructionType instr;
  std::array<sc_biguint<32>,8> seed;
  std::array<sc_biguint<32>,8> sign_rnd;
  sc_biguint<512> tr;
  std::array<sc_biguint<32>,648> pk;
  sc_biguint<39168> sk_in;
};

struct ToApiType {
  sc_biguint<512> tr;
  sc_biguint<39168> sk_out;
};

struct RegsType {
  sc_biguint<256>               rho;
  sc_biguint<512>               rho_prime;
  sc_biguint<256>               K;
  sc_biguint<512>               mu;
  sc_biguint<16>                kappa;
  std::array<sc_biguint<32>,16> c;
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
};

struct Power2RoundType {
  ADDR_TYPE t_addr;
};

struct SkEncodeType {
  ADDR_TYPE coeff_addr;
};

struct SkDecodeType {
  ADDR_TYPE source_operand;
  ADDR_TYPE destination_addr;
};

struct NormCheckType {
  sc_biguint<IMMEDIATE_BITS> immediate;
  ADDR_TYPE source_addr;
};

struct SigEncodeType {
  ADDR_TYPE source_addr;
  sc_biguint<ADDR_BITS> immediate;
};

struct MakehintType {
  ADDR_TYPE source_addr;
};

struct DecomposeType {
  ADDR_TYPE source_addr;
  ADDR_TYPE destination;
};

struct PkDecodeType {
  ADDR_TYPE destination;
};

struct SigDecodeType {
  ADDR_TYPE destination;
};

struct UseHintType {
  ADDR_TYPE operand1;
  ADDR_TYPE operand2;
};

sc_biguint<SIPO_CHUNK_SIZE> getChunk(sc_biguint<SIPO_MAX_SIZE> whole_value, sc_uint<16> chunk_idx)  {

  for (sc_uint<16> current_chunk_idx = 0; current_chunk_idx < chunk_idx && current_chunk_idx < 324; ++current_chunk_idx) {
    whole_value >>= SIPO_CHUNK_SIZE;
  }

  return whole_value.range(SIPO_CHUNK_SIZE - 1, 0);
}

sc_biguint<SIPO_CHUNK_SIZE> func_concat_seed(std::array<sc_biguint<32>,8> whole_value, sc_uint<3> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[((chunk_idx << 1)|1)];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}
sc_biguint<SIPO_CHUNK_SIZE> func_concat_pk(std::array<sc_biguint<32>,648> whole_value, sc_uint<3> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[((chunk_idx << 1)|1)];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}

sc_biguint<SIPO_CHUNK_SIZE> func_concat_sig_c(std::array<sc_biguint<32>,16> whole_value, sc_uint<3> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[((chunk_idx << 1)|1)];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}
sc_biguint<SIPO_CHUNK_SIZE> func_concat_msg_p(std::array<sc_biguint<32>,17> whole_value, sc_uint<4> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[((chunk_idx << 1)|1)];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}
sc_biguint<SIPO_CHUNK_SIZE> func_concat(std::array<sc_biguint<32>,10> whole_value, sc_uint<3> chunk_idx) {

  sc_biguint<SIPO_CHUNK_SIZE> temp;

  temp.range((SIPO_CHUNK_SIZE/2) - 1, 0) = whole_value[(chunk_idx << 1)];
  temp.range(SIPO_CHUNK_SIZE - 1, (SIPO_CHUNK_SIZE/2)) = whole_value[(chunk_idx << 1)|1];

  return temp.range(SIPO_CHUNK_SIZE - 1, 0);

}
const sc_biguint<IMMEDIATE_BITS> norm_check_z_immediate = 0;
const sc_biguint<IMMEDIATE_BITS> norm_check_r0_immediate = 1;
const sc_biguint<IMMEDIATE_BITS> norm_check_ct0_immediate = 2;


SC_MODULE(AdamsBridge) {
 public:
  SC_CTOR(AdamsBridge) {
    SC_THREAD(ctrl)
  }

  // Interface to the API registers
  shared_in<FromApiType> api_in;
  master_out<ToApiType> api_out;

  // Different constant register IDs; used as operands for certain operations
  ADDR_PORT(lfsr_seed_reg_id);
  ADDR_PORT(rho_k_reg_id);
  ADDR_PORT(tr_reg_id);
  ADDR_PORT(mu_reg_id);
  ADDR_PORT(rho_prime_reg_id);
  ADDR_PORT(sig_c_reg_id);
  ADDR_PORT(verify_res_reg_id);

  // Various memory addresses
  ADDRS_PORT(s1_addrs, 7);
  ADDRS_PORT(s2_addrs, 8);
  ADDR_PORT(temp_addr);
  ADDRS_PORT(s1_ntt_addrs, 7);
  ADDR_PORT(as_addr);
  ADDR_PORT(rho_id);
  ADDR_PORT(as_intt_addr);
  ADDRS_PORT(t_addrs, 8);
  ADDRS_PORT(y_addrs, 7);
  ADDRS_PORT(y_ntt_addrs, 7);
  ADDR_PORT(ay0_addr);
  ADDRS_PORT(w0_addrs, 8);
  ADDRS_PORT(z_addrs, 7);
  ADDR_PORT(c_addr);
  ADDR_PORT(c_ntt_addr);
  ADDRS_PORT(z_ntt_addrs, 7);
  ADDR_PORT(az_addr);
  ADDR_PORT(ct_addr);
  ADDR_PORT(hint_r_addr);

  shared_in<bool> y_valid_in;
  shared_out<bool> set_y_valid_out;
  shared_in<bool> w0_valid_in;
  shared_out<bool> set_w0_valid_out;
  shared_in<bool> c_valid_in;
  shared_out<bool> set_c_valid_out;
  shared_in<sc_biguint<512>> entropy_in;
  shared_in<sc_biguint<64>> counter_in;
  shared_in<std::array<sc_biguint<32>,17>> msg_prime_in;
  master_out<sc_biguint<SIPO_CHUNK_SIZE>> to_keccak;
  //shared_out<sc_biguint<SIPO_CHUNK_SIZE>> some_keccak;
  shared_in<bool> to_keccak_rdy;
  //shared_in<bool> keccak_done_in;
  shared_in<sc_biguint<1600>> from_keccak_piso;
  shared_in<bool> from_keccak_piso_vld_in;
  blocking_out<ToSamplerType> to_sampler;
  shared_in<bool> sampler_done_in;
  blocking_out<NttType> to_ntt;
  shared_in<bool> ntt_done_in;
  blocking_out<Power2RoundType> to_power_2_round;
  shared_in<bool> power_2_round_done_in;
  blocking_out<SkEncodeType> to_sk_encode;
  shared_in<bool> sk_encode_done_in;
  blocking_out<DecomposeType> to_decompose;
  shared_in<bool> decompose_done_in;
  blocking_out<PkDecodeType> to_pk_decode;
  shared_in<bool> pk_decode_done_in;
  blocking_out<SigDecodeType> to_sig_decode_z;
  shared_in<bool> sig_decode_z_done_in;
  blocking_out<NormCheckType> to_norm_check;
  shared_in<bool> norm_check_done_in;
  blocking_out<SigDecodeType> to_sig_decode_h;
  shared_in<bool> sig_decode_h_done_in;
  blocking_out<UseHintType> to_use_hint;
  shared_in<bool> use_hint_done_in;
  shared_in<bool> from_ext_mu_mode_in;
  shared_in<bool> from_keygen_jump_in;
  shared_out<bool> enable_lfsr;
  shared_in<bool> sig_vld_chk_done_in;
  shared_out<bool> sha3_start_o;
  shared_out<bool> msg_start_o;
  shared_in<sc_uint<3>> sampler_offset_f;
  shared_in<std::array<sc_biguint<32>,10>> pk_ram_data;
  shared_in<sc_biguint<512>> from_ext_mu;

 private:
  RegsType registers;



  [[noreturn]] void ctrl() {
    sc_uint<16> sipo_chunk_idx;
    FromApiType from_api;
    ToApiType to_api;
    bool subcomponent_done = false;
    bool subcomponent_done_1 = false;
    bool subcomponent_done_2 = false;
    bool unused = false;
    bool ntt_sample_done = false;
    bool some_rdy_reg = false;
    bool some_validty_reg = false;
    bool piso_vld = false;
    bool ext_mu_mode_in = false;
    bool keygen_jump = false;
    registers.rho       = 0;
    registers.rho_prime = 0;
    registers.K         = 0;
    registers.mu        = 0;
    registers.kappa     = 0;
    registers.c[0]      = 0;
    sha3_start_o -> set(false);
    msg_start_o -> set(false);
    sc_biguint<512> entropy = 0;
    sc_biguint<64> counter = 0;
    sc_biguint<1600> sampled_value = 0;

    while (true) {
      // Wait for a new top-level command
      do {
        insert_state("idle");
        api_in->get(from_api);

      } while (from_api.instr == InstructionType::NoOp);

      // Work off the sequence of computations to perform the current command
      if (from_api.instr == InstructionType::Keygen || from_api.instr == InstructionType::KeygenSign) {
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_rnd_seed_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true); 
        // rnd_seed = Keccak(entropy || counter)
        insert_state("keygen_rnd_seed_start");
        msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) { // Rohith: Because the design takes one extra byte and passes strobe for the last msg valid bytes
          entropy_in->get(entropy);
          WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_entropy");
          to_keccak -> master_write(getChunk(entropy,sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_entropy_msg_done");
        sipo_chunk_idx = 0;
        insert_state("keygen_rnd_seed_wait");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 2; ++sipo_chunk_idx) { // Rohith: Because the design takes one extra byte and passes strobe for the last msg valid bytes
          counter_in->get(counter);
          WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_counter");
          to_keccak->master_write(getChunk(counter,0));
        }
        sipo_chunk_idx= sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_counter_msg_done");
        sipo_chunk_idx = 0;

        GET_ADDR(lfsr_seed_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = lfsr_seed_reg_id }, unused,
            "keygen_sample_rnd_seed_start");

        WAIT_UNTIL_DONE(sampler_done_in, "keygen_sample_rnd_seed");

        enable_lfsr->set(true);
        insert_state("keygen_rnd_seed_lfsr");
        enable_lfsr->set(false);
        insert_state("keygen_rnd_seed_done");
        // Expand the seed to p, p', and K
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_expand_seed_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("keygen_expand_seed_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
          api_in->get(from_api);
           WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_write_seed");
          to_keccak->master_write(func_concat_seed(from_api.seed, sipo_chunk_idx.range(1,0)));
        }
       WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_write_seed_immediate");
       to_keccak->master_write(0x0708);
       sipo_chunk_idx = sipo_chunk_idx + 1;
       WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_seed_msg_done");
       sipo_chunk_idx = 0;

        GET_ADDR(rho_k_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = rho_k_reg_id },
            unused, "keygen_expand_seed_sampling_start");
         do { 
           insert_state("keygen_expand_seed_sampling"); 
           from_keccak_piso->get(sampled_value);
           from_keccak_piso_vld_in -> get(piso_vld);
             registers.rho = piso_vld ? sampled_value.range(255, 0):registers.rho ;
             registers.rho_prime = piso_vld ? sampled_value.range(767, 256): registers.rho_prime;
             registers.K = piso_vld ?sampled_value.range(1023, 768):registers.K;    
           sampler_done_in->get(subcomponent_done); 
         } while (!subcomponent_done);
      
        // Compute s1 and s2
        sc_uint<16> rejbounded_counter = 0;

        for (; rejbounded_counter < 7; ++rejbounded_counter) {
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_write_rejbounded_input_s1_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
          insert_state("keygen_write_rejbounded_input_s1_start");
           msg_start_o -> set(false);
          for (sipo_chunk_idx = 0; sipo_chunk_idx < 8; ++sipo_chunk_idx) { 
            WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_write_rejbounded_input_s1");
            to_keccak->master_write(getChunk(registers.rho_prime, sipo_chunk_idx.range(2,0)));
          }
      
          WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_write_rejbounded_immediate_s1");
          to_keccak->master_write(static_cast<sc_biguint<SIPO_CHUNK_SIZE>>(rejbounded_counter));
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_rejbounded_immediate_s1_msg_done");
          sipo_chunk_idx = 0;

          GET_ADDRS(s1_addrs, 7);
          to_sampler->try_write({ .mode = SamplerMode::RejBounded, .destination = s1_addrs.at(rejbounded_counter) },
              unused, "keygen_rejbounded_s1_start");
             

          WAIT_UNTIL_DONE(sampler_done_in, "keygen_rejbounded_s1");
        }

        for (rejbounded_counter = 7; rejbounded_counter < 15; ++rejbounded_counter) {
           sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_write_rejbounded_input_s2_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
          insert_state("keygen_write_rejbounded_input_s2_start");
           msg_start_o -> set(false);
          for (sipo_chunk_idx = 0; sipo_chunk_idx < 8; ++sipo_chunk_idx) { 
            WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_rejbounded_input_s2");
            to_keccak->master_write(getChunk(registers.rho_prime, sipo_chunk_idx.range(2,0)));
          }
          
          WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_write_rejbounded_immediate_s2");
          to_keccak->master_write(static_cast<sc_biguint<SIPO_CHUNK_SIZE>>(rejbounded_counter));
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_write_rejbounded_immediate_s2_msg_done");
          sipo_chunk_idx = 0;
          GET_ADDRS(s2_addrs, 8);
          to_sampler->try_write({ .mode = SamplerMode::RejBounded, .destination = s2_addrs.at(rejbounded_counter - 7) },
              unused, "keygen_rejbounded_s2_start");

          WAIT_UNTIL_DONE(sampler_done_in, "keygen_rejbounded_s2");
        }

        rejbounded_counter = 0;
        
        // Compute NTT(s1)
        sc_uint<3> keygen_ntt_s1_idx = 0;
        for (keygen_ntt_s1_idx = 0; keygen_ntt_s1_idx < 7; ++keygen_ntt_s1_idx) {
          insert_state("Keygen_ntt_s1_idle");
          GET_ADDRS(s1_addrs, 7);
          GET_ADDR(temp_addr);
          GET_ADDRS(s1_ntt_addrs, 7);

          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = s1_addrs.at(keygen_ntt_s1_idx), .operand2 = temp_addr,
              .destination = s1_ntt_addrs.at(keygen_ntt_s1_idx) }, unused, "keygen_ntt_s1_start");

          WAIT_UNTIL_DONE(ntt_done_in, "keygen_ntt_s1");
        }
        keygen_ntt_s1_idx = 0;

        // Do the following 8 times to compute the 8 values for t
        sc_uint<8> keygen_t_idx = 0;
        for (keygen_t_idx = 0; keygen_t_idx < 8; ++keygen_t_idx) {
          // Compute A * NTT(s1)
          sc_uint<8> keygen_pwm_a_idx = 0;
          for (keygen_pwm_a_idx = 0; keygen_pwm_a_idx < 7; ++keygen_pwm_a_idx) {
             sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_pwm_a_write_rho_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
            insert_state("keygen_pwm_a_write_rho_start");
             msg_start_o -> set(false);
            for (sipo_chunk_idx = 0; sipo_chunk_idx < 4; ++sipo_chunk_idx) { 
              WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_pwm_a_write_rho");
              to_keccak->master_write(getChunk(registers.rho, sipo_chunk_idx.range(1,0)));
            }
            
            WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_pwm_a_write_immediate");
            to_keccak->master_write((static_cast<sc_biguint<64>>(keygen_t_idx) << 8) | keygen_pwm_a_idx);
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_pwm_a_write_immediate_msg_done");
            sipo_chunk_idx = 0;
             GET_ADDRS(s1_ntt_addrs, 7);
            GET_ADDR(as_addr);
            GET_ADDR(rho_id);

            to_sampler->try_write({ .mode = SamplerMode::RejSampler,
                .destination = as_addr /* It is directly forwareded to the ntt component, not sure what to put here */ },
                unused, "keygen_pwm_a_rejection_sampling_start");

            //WAIT_UNTIL_DONE(sampler_done_in, "keygen_pwm_a_rejection_sampling");

           
            to_ntt->try_write({ .mode = (keygen_pwm_a_idx > 0 ? NttMode::PwmAccuSampler : NttMode::PwmSampler),
                .operand1 = rho_id /* Is directly taken from the sampler, not sure what to put here */,
                .operand2 = s1_ntt_addrs.at(keygen_pwm_a_idx), .destination = as_addr }, unused, "keygen_pwm_a_start");

            WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "keygen_pwm_a");
          }
          keygen_pwm_a_idx = 0;
          // NTT inverse of As1
          insert_state("keygen_intt_a_idle");
          GET_ADDR(as_addr);
          GET_ADDR(temp_addr);
          GET_ADDR(as_intt_addr);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = as_addr, .operand2 = temp_addr,
              .destination = as_intt_addr }, unused, "keygen_intt_a_start");

          WAIT_UNTIL_DONE(ntt_done_in, "keygen_intt_a");

          as_intt_addr_in->get(as_intt_addr);
          GET_ADDRS(s2_addrs, 8);
          GET_ADDRS(t_addrs, 8);
          // "+", in t = As1 + s2
          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = as_intt_addr, .operand2 = s2_addrs.at(keygen_t_idx),
              .destination = t_addrs.at(keygen_t_idx) }, unused, "keygen_compute_t_start");

          WAIT_UNTIL_DONE(ntt_done_in, "keygen_compute_t");
        }
        keygen_t_idx = 0;

        // Compute t0 and t1 and pkencode it is part of power2round
        GET_ADDRS(t_addrs, 8);
        Power2RoundType to_power_2_round_data = { .t_addr = t_addrs.at(0) };
        to_power_2_round->try_write(to_power_2_round_data, unused, "keygen_power_2_round_start");

        WAIT_UNTIL_DONE(power_2_round_done_in, "keygen_power_2_round");

        // Compute tr
          sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("keygen_compute_tr_write_pk_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        //insert_state("keygen_pwm_a_write_rho_MSG_START");
       
        insert_state("keygen_compute_tr_write_pk_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 325; ++sipo_chunk_idx) { // Rohith: Because the design takes one extra byte and passes strobe for the last msg valid bytes
          api_in->get(from_api);
          
          sc_biguint<SIPO_CHUNK_SIZE> pk_msg_data;
          sc_uint<3> sampler_offset_reg;
          std::array<sc_biguint<32>,10> pk_ram_data_reg;
          //if(sipo_chunk_idx!=0){
          WAIT_UNTIL_DONE(to_keccak_rdy, "keygen_compute_tr_write_pk");
          if(sipo_chunk_idx >= 4){
            sampler_offset_f -> get(sampler_offset_reg);
            pk_ram_data -> get(pk_ram_data_reg);
            pk_msg_data = (func_concat(pk_ram_data_reg,sampler_offset_reg));;
          }
          else {
            pk_msg_data = func_concat_pk(from_api.pk, sipo_chunk_idx.range(1,0));
          }
          to_keccak->master_write(pk_msg_data);
        }
        sipo_chunk_idx = sipo_chunk_idx+1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"keygen_compute_tr_write_pk_msg_done");
        sipo_chunk_idx = 0;

        GET_ADDR(tr_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = tr_reg_id },
            unused, "keygen_compute_tr_sampling_start");

        //WAIT_UNTIL_DONE(sampler_done_in, "keygen_compute_tr_sampling");
        do { 
          insert_state("keygen_compute_tr_sampling"); 
          from_keccak_piso->get(sampled_value);
          from_keccak_piso_vld_in -> get(piso_vld);
          to_api.tr = piso_vld ? sampled_value.range(511, 0):to_api.tr ;
          api_out->master_write(to_api);
          sampler_done_in->get(subcomponent_done); 
        } while (!subcomponent_done);
        // Compute sk
        GET_ADDRS(s1_addrs, 7);
        // Check the destination as well
        to_sk_encode->try_write({ .coeff_addr = s1_addrs.at(0) }, unused, "keygen_sk_encode_start");

        WAIT_UNTIL_DONE(sk_encode_done_in, "keygen_sk_encode");

        insert_state("keygen_jump_sign");
        //from_keygen_jump_in -> get (keygen_jump);
        if(!(from_api.instr == InstructionType::KeygenSign) && from_api.instr == InstructionType::Keygen){
          insert_state("keygen_end_state");
        }
      }


      api_in->get(from_api);
      if (from_api.instr == InstructionType::Sign) {
        // rnd_seed = Keccak(entropy | counter)
          sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_rnd_seed_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("sign_rnd_seed_start");
        msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          //sc_biguint<512> entropy;
          entropy_in->get(entropy);
          //if(sipo_chunk_idx!=0) {
          WAIT_UNTIL_DONE(to_keccak_rdy, "sign_write_entropy");
          to_keccak->master_write(getChunk(entropy, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_write_entropy_msg_done");
        sipo_chunk_idx = 0;
        insert_state("sign_rnd_seed_wait");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 2; ++sipo_chunk_idx) {
          //sc_biguint<64> counter;
          counter_in->get(counter);
          WAIT_UNTIL_DONE(to_keccak_rdy, "sign_write_counter");
          to_keccak->master_write(getChunk(counter,0));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_write_counter_msg_done");
        sipo_chunk_idx = 0;

        GET_ADDR(lfsr_seed_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = lfsr_seed_reg_id },
            unused, "sign_sample_rnd_seed_start");

        WAIT_UNTIL_DONE(sampler_done_in, "sign_sample_rnd_seed");

        enable_lfsr->set(true);
        insert_state("sign_rnd_seed_lfsr");
        enable_lfsr->set(false);
      }

      api_in->get(from_api);
      if (from_api.instr == InstructionType::Sign || from_api.instr == InstructionType::KeygenSign) {
        // µ = H(tr | M, 512)
        insert_state("sign_compute_mu_idle");
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_compute_mu_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("sign_compute_mu_start");
        msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          api_in->get(from_api);
          WAIT_UNTIL_DONE(to_keccak_rdy, "sign_compute_mu_write_tr");
          to_keccak->master_write(getChunk(from_api.tr, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_mu_write_tr_msg_done");
        sipo_chunk_idx = 0;
        insert_state("sign_compute_mu_wait");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          std::array<sc_biguint<32>,17> msg_prime;
          msg_prime_in->get(msg_prime);
          WAIT_UNTIL_DONE(to_keccak_rdy, "sign_compute_mu_write_msg_prime");
          to_keccak->master_write(func_concat_msg_p(msg_prime, sipo_chunk_idx.range(3,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_mu_write_msg_prime_msg_done");
        sipo_chunk_idx = 0;

        GET_ADDR(mu_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = mu_reg_id },
            unused, "sign_compute_mu_sampling_start");

        sc_biguint<1600> sampled_value;
        sc_biguint<512> ext_mu;
        do { 
          insert_state("sign_compute_mu_sampling"); 
          from_ext_mu->get(ext_mu);
          registers.mu = ext_mu;
          sampler_done_in->get(subcomponent_done); 
        } while (!subcomponent_done);
        
        //from_ext_mu->get(ext_mu);
        //registers.mu = ext_mu.range(511, 0);

        // p' = Keccak(K | rnd | µ)
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_compute_rho_prime_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("sign_compute_rho_prime_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 5; ++sipo_chunk_idx) {
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_rho_prime_write_K");
          to_keccak->master_write(getChunk(registers.K, sipo_chunk_idx.range(1,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_rho_prime_write_K_msg_done");
        sipo_chunk_idx = 0;
        insert_state("sign_compute_rho_prime_wait_0");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 5; ++sipo_chunk_idx) {
          api_in->get(from_api);
          WAIT_UNTIL_DONE(to_keccak_rdy, "sign_compute_rho_prime_write_sign_rnd");
          to_keccak->master_write(func_concat_seed(from_api.sign_rnd, sipo_chunk_idx.range(1,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_rho_prime_write_sign_rnd_msg_done");
        sipo_chunk_idx = 0;
        insert_state("sign_compute_rho_prime_wait_1");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_rho_prime_write_mu");
          to_keccak->master_write(getChunk(registers.mu, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_rho_prime_write_mu_msg_done");
        sipo_chunk_idx = 0;

       GET_ADDR(rho_prime_reg_id);
       to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = rho_prime_reg_id },
           unused, "sign_compute_rho_prime_sampling_start");

       //WAIT_UNTIL_DONE(sampler_done_in, "sign_compute_rho_prime_sampling");
       do { 
        insert_state("sign_compute_rho_prime_sampling"); 
        from_keccak_piso->get(sampled_value);
        from_keccak_piso_vld_in -> get(piso_vld);
        registers.rho_prime = piso_vld? sampled_value.range(511, 0):registers.rho_prime;
        sampler_done_in->get(subcomponent_done); 
      } while (!subcomponent_done);

        bool y_valid = false;
        bool w0_valid = false;
        bool sig_vld_chk_done = false;
        bool jump_if_invalid = false;
        sc_uint<1> vld_lcl = 0;
        sc_uint<1> vld_lcl_w0 = 0;
        sc_uint<8> sign_expand_mask_idx;
        sc_uint<8> sign_ntt_y_idx;
        ADDR_TYPE lfsr_seed_reg_id,sig_c_reg_id;
        std::array<ADDR_TYPE, 8> w0_addrs;
        sc_uint<8> sign_compute_w0_idx;
         bool c_valid;
        while(!jump_if_invalid){
        do {
          insert_state("sign_wait_for_y_and_w0_clear");
          y_valid_in->get(y_valid);
          w0_valid_in->get(w0_valid);
          sig_vld_chk_done_in -> get(sig_vld_chk_done);
          vld_lcl = sig_vld_chk_done ? sc_uint<1>(1) : sc_uint<1>(0);
        } while ((y_valid || w0_valid)&& !sig_vld_chk_done);
        switch (vld_lcl)
        {
        case 1:
          break;
        case 0:
            // lfsr_seed = Keccak(re_entropy | counter)
             sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_compute_lfsr_seed_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        //insert_state("sign_compute_lfsr_seed_MSG_START");
       
        insert_state("sign_compute_lfsr_seed_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          sc_biguint<512> entropy;
          entropy_in->get(entropy);
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_lfsr_seed_write_entropy");
          to_keccak->master_write(getChunk(entropy, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
       WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_lfsr_seed_write_entropy_msg_done");
        sipo_chunk_idx = 0;
        insert_state("sign_compute_lfsr_seed_wait");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 2; ++sipo_chunk_idx) {
        sc_biguint<64> counter;
        counter_in->get(counter);
        WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_lfsr_seed_write_counter");
        to_keccak->master_write(getChunk(counter,0));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
         WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_lfsr_seed_write_counter_msg_done");
        sipo_chunk_idx = 0;
        //GET_ADDR(lfsr_seed_reg_id);
        lfsr_seed_reg_id_in -> get(lfsr_seed_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = lfsr_seed_reg_id },
            unused, "sign_compute_lfsr_seed_sampling_start");

        WAIT_UNTIL_DONE(sampler_done_in, "sign_compute_lfsr_seed_sampling");

        enable_lfsr->set(true);
        insert_state("sign_compute_lfsr_seed_lfsr");
        enable_lfsr->set(false);
        insert_state("sign_expand_mask_done");
        // y = ExpandMask(p', kappa)
        sign_expand_mask_idx = 0;
        for (sign_expand_mask_idx = 0; sign_expand_mask_idx < 7; ++sign_expand_mask_idx) {
          
              sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_expand_mask_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
          insert_state("sign_expand_mask_start");
          msg_start_o -> set(false);
          for (sipo_chunk_idx = 0; sipo_chunk_idx < 8; ++sipo_chunk_idx) {
            WAIT_UNTIL_DONE(to_keccak_rdy,"sign_expand_mask_write_rho_prime");
            to_keccak->master_write(getChunk(registers.rho_prime, sipo_chunk_idx.range(2,0)));
          }
          
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_expand_mask_write_kappa_immediate");
          to_keccak->master_write((registers.kappa + sign_expand_mask_idx) & 0xFFFF);
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_expand_mask_write_kappa_immediate_msg_done");
          sipo_chunk_idx = 0;
          GET_ADDRS(y_addrs, 7);
          to_sampler->try_write({ .mode = SamplerMode::ExpMask, .destination = y_addrs.at(sign_expand_mask_idx) },
              unused, "sign_expand_mask_sampling_start");

          WAIT_UNTIL_DONE(sampler_done_in, "sign_expand_mask_sampling");
        }
        sign_expand_mask_idx = 0;

        // NTT(Y)
        sign_ntt_y_idx = 0;
       
        for (sign_ntt_y_idx = 0; sign_ntt_y_idx < 7; ++sign_ntt_y_idx) {
          insert_state("sign_ntt_y_idle");
          GET_ADDRS(y_addrs, 7);
          GET_ADDR(temp_addr);
          GET_ADDRS(y_ntt_addrs, 7);

          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = y_addrs.at(sign_ntt_y_idx), .operand2 = temp_addr,
              .destination = y_ntt_addrs.at(sign_ntt_y_idx) }, unused, "sign_ntt_y_start");

          WAIT_UNTIL_DONE(ntt_done_in, "sign_ntt_y");
        }
        sign_ntt_y_idx = 0;

        do {
          insert_state("sign_wait_for_w0_clear");
          w0_valid_in->get(w0_valid);
          sig_vld_chk_done_in -> get(sig_vld_chk_done);
          vld_lcl_w0 = sig_vld_chk_done ? sc_uint<1>(1) : sc_uint<1>(0);
        } while (w0_valid && !sig_vld_chk_done);
        switch (vld_lcl_w0)
        {
        case 1:
          //jump_if_invalid = true;
          break;
        case 0:
          sign_compute_w0_idx = 0;
          for (sign_compute_w0_idx = 0; sign_compute_w0_idx < 8; ++sign_compute_w0_idx) {
            sc_uint<8> sign_compute_w0_y_idx = 0;
          for (sign_compute_w0_y_idx = 0; sign_compute_w0_y_idx < 7; ++sign_compute_w0_y_idx) {
                sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_compute_w0_pwm_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
            insert_state("sign_compute_w0_pwm_start");
             msg_start_o -> set(false);
            for (sipo_chunk_idx = 0; sipo_chunk_idx < 4; ++sipo_chunk_idx) {
              WAIT_UNTIL_DONE(to_keccak_rdy, "sign_compute_w0_pwm_write_rho");
              to_keccak->master_write(getChunk(registers.rho, sipo_chunk_idx.range(1,0)));     
            }
            
            WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_w0_pwm_write_immediate");
            to_keccak->master_write(static_cast<sc_biguint<64>>(sign_compute_w0_idx) << 8 |
                static_cast<sc_biguint<64>>(sign_compute_w0_y_idx));
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"sign_compute_w0_pwm_write_immediate_msg_done");
            sipo_chunk_idx = 0;
            GET_ADDR(rho_id);
            GET_ADDRS(y_ntt_addrs, 7);
            GET_ADDR(ay0_addr);
            to_sampler->try_write({ .mode = SamplerMode::RejSampler, .destination = ay0_addr },
                unused, "sign_compute_w0_pwm_sampling_start");

            //WAIT_UNTIL_DONE(sampler_done_in, "sign_compute_w0_pwm_sampling");

            to_ntt->try_write({ .mode = (sign_compute_w0_y_idx > 0) ? NttMode::PwmAccuSampler : NttMode::PwmSampler,
                .operand1 = rho_id, .operand2 = y_ntt_addrs.at(sign_compute_w0_y_idx), .destination = ay0_addr },
                unused, "sign_compute_w0_pwm_samp_ntt");

             WAIT_FOR_SUBS(ntt_done_in,sampler_done_in, "sign_compute_w0_pwm");
          }
          sign_compute_w0_y_idx = 0;
          insert_state("sign_compute_w0_intt_idle");
          GET_ADDR(ay0_addr);
          GET_ADDR(temp_addr);
          GET_ADDRS(w0_addrs, 8);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = ay0_addr, .operand2 = temp_addr,
              .destination = w0_addrs.at(sign_compute_w0_idx) }, unused, "sign_compute_w0_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "sign_compute_w0_intt");
          }
          sign_compute_w0_idx = 0;

          set_y_valid_out->set(true);
          insert_state("sign_set_y_valid");
          set_y_valid_out->set(false);

        // Load mu
        insert_state("sign_load_mu_idle");
            sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_load_mu_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
          insert_state("sign_load_mu_start");
           msg_start_o -> set(false);
          for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
            WAIT_UNTIL_DONE(to_keccak_rdy,"sign_load_mu");
            to_keccak->master_write(getChunk(registers.mu, sipo_chunk_idx.range(2,0)));
          }
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_load_mu_msg_done");
          sipo_chunk_idx = 0;
          insert_state("sign_load_mu_wait");

          // Decompose(w)
          //GET_ADDRS(w0_addrs, 8);
          w0_addrs_in -> get(w0_addrs);
          to_decompose->try_write({ .source_addr = w0_addrs.at(0), .destination = w0_addrs.at(0) }, unused, "sign_decompose_w_start");

          WAIT_UNTIL_DONE(decompose_done_in, "sign_decompose_w");

          set_w0_valid_out->set(true);
          insert_state("sign_set_w0_valid");
          set_w0_valid_out->set(false);

          c_valid = false;
          do {
            insert_state("sign_wait_for_c_clear");
            c_valid_in->get(c_valid);
          } while (c_valid);

          //GET_ADDR(sig_c_reg_id);
          sig_c_reg_id_in->get(sig_c_reg_id);
          to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = sig_c_reg_id },
            unused, "sign_compute_c_start");

          //WAIT_UNTIL_DONE(sampler_done_in, "sign_compute_c");
          do { 
            insert_state("sign_compute_c"); 
            from_keccak_piso->get(sampled_value);
            from_keccak_piso_vld_in -> get(piso_vld);
              for(int i=0;i<16;++i){
                  registers.c[i] = piso_vld ? sampled_value.range(32*(i+1),32*i): registers.c[i];
              
            }
            sampler_done_in->get(subcomponent_done); 
          } while (!subcomponent_done);
         
           sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("sign_sample_in_ball_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
       
          insert_state("sign_sample_in_ball_start");
           msg_start_o -> set(false);
          for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
            WAIT_UNTIL_DONE(to_keccak_rdy,"sign_sample_in_ball_write_c");
            to_keccak->master_write(func_concat_sig_c(registers.c, sipo_chunk_idx.range(2,0)));
          }
          sipo_chunk_idx = sipo_chunk_idx + 1;
          WAIT_UNTIL_DONE(to_keccak_rdy,"sign_sample_in_ball_write_c_msg_done");
          sipo_chunk_idx = 0;
      
          to_sampler->try_write({ .mode = SamplerMode::SampleInBall, .destination = 0 },
            unused, "sign_sample_in_ball_sampling_start");

          WAIT_UNTIL_DONE(sampler_done_in, "sign_sample_in_ball_sampling");

          set_c_valid_out->set(true);
          insert_state("sign_set_c_valid");
          set_c_valid_out->set(false);
          insert_state("sign_end_of_challenge");
          sig_vld_chk_done_in -> get(sig_vld_chk_done);
          if(!sig_vld_chk_done){
          //insert_state("increment_kappa");
          registers.kappa += 7;
          jump_if_invalid = false;
          }
          else {
            jump_if_invalid = true;
          }
        break;
        
        default:
          break;
        }
        
        break;
        default:
          break;
        }
      
       
        jump_if_invalid = (vld_lcl_w0==1)?true: jump_if_invalid;
      }
      insert_state("sign_end_state");
      }
      

      api_in->get(from_api);
      if (from_api.instr == InstructionType::Verify) {
        GET_ADDRS(t_addrs, 8);
        to_pk_decode->try_write({ .destination = t_addrs.at(0) }, unused, "verify_pk_decode_start");

        WAIT_UNTIL_DONE(pk_decode_done_in, "verify_pk_decode");

        GET_ADDRS(z_addrs, 7);
        to_sig_decode_z->try_write({ .destination = z_addrs.at(0) }, unused, "verify_sig_decode_z_start");

        WAIT_UNTIL_DONE(sig_decode_z_done_in, "verify_sig_decode_z");

        sc_uint<8> verify_norm_check_idx = 0;
        for (verify_norm_check_idx = 0; verify_norm_check_idx < 7; ++verify_norm_check_idx) {
          z_addrs_in->get(z_addrs);

          to_norm_check->try_write({ .immediate = norm_check_z_immediate, .source_addr = z_addrs.at(verify_norm_check_idx) },
              unused, "verify_norm_check_start");

          WAIT_UNTIL_DONE(norm_check_done_in, "verify_norm_check");
        }
        verify_norm_check_idx = 0;
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("verify_compute_tr_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
    
        insert_state("verify_compute_tr_start");
         msg_start_o -> set(false);
        //no check for chunk idx 325 as in rtl starts from 1
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 325; ++sipo_chunk_idx) {
          api_in->get(from_api);
          
           sc_biguint<SIPO_CHUNK_SIZE> pk_msg_data;
          sc_uint<3> sampler_offset_reg;
          std::array<sc_biguint<32>,10> pk_ram_data_reg;
          WAIT_UNTIL_DONE(to_keccak_rdy, "verify_compute_tr_write_pk");
          if(sipo_chunk_idx >= 4){
            sampler_offset_f -> get(sampler_offset_reg);
            pk_ram_data -> get(pk_ram_data_reg);
            pk_msg_data = (func_concat(pk_ram_data_reg,sampler_offset_reg));;
          }
          else {
            pk_msg_data = func_concat_pk(from_api.pk, sipo_chunk_idx.range(1,0));
          }
          to_keccak->master_write(pk_msg_data);  
        }
        sipo_chunk_idx = sipo_chunk_idx+1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_tr_write_pk_msg_done");
        sipo_chunk_idx = 0;

        GET_ADDR(tr_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = tr_reg_id },
            unused, "verify_compute_tr_sampling_start");

        //WAIT_UNTIL_DONE(sampler_done_in, "verify_compute_tr_sampling");
        sc_biguint<1600> sampled_value;
        do { 
          insert_state("verify_compute_tr_sampling"); 
          from_keccak_piso->get(sampled_value);
          from_keccak_piso_vld_in -> get(piso_vld);
          if(piso_vld){
            to_api.tr = sampled_value.range(511, 0);
            api_out->master_write(to_api);
          }
          sampler_done_in->get(subcomponent_done); 
        } while (!subcomponent_done);
        
        insert_state("verify_check_mode");
        from_ext_mu_mode_in -> get(ext_mu_mode_in);
        if(!ext_mu_mode_in){
        // µ = H(tr | M, 512)
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("verify_compute_mu_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("verify_compute_mu_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          api_in->get(from_api);
          WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_mu_write_tr");
          to_keccak->master_write(getChunk(from_api.tr, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_mu_write_tr_msg_done");
        sipo_chunk_idx = 0;
        insert_state("verify_compute_mu_wait");
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          std::array<sc_biguint<32>,17> msg_prime;
          msg_prime_in->get(msg_prime);
          WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_mu_write_msg_prime");
          to_keccak->master_write(func_concat_msg_p(msg_prime, sipo_chunk_idx.range(3,0)));
        }
         sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_mu_write_msg_prime_msg_done");
        sipo_chunk_idx = 0;
        GET_ADDR(mu_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = mu_reg_id },
            unused, "verify_compute_mu_sampling_start");

        //WAIT_UNTIL_DONE(sampler_done_in, "verify_compute_mu_sampling");
        sc_biguint<512> ext_mu;
        do { 
          insert_state("verify_compute_mu_sampling"); 
          from_ext_mu->get(ext_mu);
          registers.mu = ext_mu;
          sampler_done_in->get(subcomponent_done); 
        } while (!subcomponent_done);
      
      }

        // c = SampleInBall(c~1)
        sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("verify_sample_in_ball_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        insert_state("verify_sample_in_ball_start");
        msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          WAIT_UNTIL_DONE(to_keccak_rdy, "verify_sample_in_ball_write_c");
          to_keccak->master_write(func_concat_sig_c(registers.c, sipo_chunk_idx.range(2,0)));
        }
         sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"verify_sample_in_ball_write_c_msg_done");
        
        sipo_chunk_idx = 0;
        //insert_state("verify_sample_in_ball_wait"); // Not required doesn't go to wait state

        to_sampler->try_write({ .mode = SamplerMode::SampleInBall, .destination = 0 },
            unused, "verify_sample_in_ball_sampling_start");

        WAIT_UNTIL_DONE(sampler_done_in, "verify_sample_in_ball_sampling");

        // c^ = NTT(c)
        GET_ADDR(c_addr);
        GET_ADDR(temp_addr);
        GET_ADDR(c_ntt_addr);

        to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = c_addr, .operand2 = temp_addr, .destination = c_ntt_addr },
            unused, "verify_ntt_c_start");

        WAIT_UNTIL_DONE(ntt_done_in, "verify_ntt_c");

        // t1 = NTT(t1)
        sc_uint<8> verify_ntt_t_idx = 0;
        for (verify_ntt_t_idx = 0; verify_ntt_t_idx < 8; ++verify_ntt_t_idx) {
          t_addrs_in->get(t_addrs);
          temp_addr_in->get(temp_addr);

          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = t_addrs.at(verify_ntt_t_idx), .operand2 = temp_addr,
              .destination = t_addrs.at(verify_ntt_t_idx) }, unused, "verify_ntt_t_start");

          WAIT_UNTIL_DONE(ntt_done_in, "verify_ntt_t");
        }
        verify_ntt_t_idx = 0;

        // z = NTT(z)
        sc_uint<8> verify_ntt_z_idx = 0;
        for (verify_ntt_z_idx = 0; verify_ntt_z_idx < 7; ++verify_ntt_z_idx) {
          z_addrs_in->get(z_addrs);
          temp_addr_in->get(temp_addr);
          GET_ADDRS(z_ntt_addrs, 7);

          to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = z_addrs.at(verify_ntt_z_idx), .operand2 = temp_addr,
              .destination = z_ntt_addrs.at(verify_ntt_z_idx) }, unused, "verify_ntt_z_start");

          WAIT_UNTIL_DONE(ntt_done_in, "verify_ntt_z");
        }
        verify_ntt_z_idx = 0;

        // Compute w0
        sc_uint<8> verify_compute_w0_idx = 0;
        for (verify_compute_w0_idx = 0; verify_compute_w0_idx < 8; ++verify_compute_w0_idx) {
          // Compute az
          sc_uint<8> verify_compute_az_idx = 0;
          for (verify_compute_az_idx = 0; verify_compute_az_idx < 7; ++verify_compute_az_idx) {
             sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("verify_compute_az_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        //insert_state("verify_compute_az_MSG_START");
        
            insert_state("verify_compute_az_start");
            msg_start_o -> set(false);
            for (sipo_chunk_idx = 0; sipo_chunk_idx < 4; ++sipo_chunk_idx) {
              WAIT_UNTIL_DONE(to_keccak_rdy, "verify_compute_az_write_rho");
              to_keccak->master_write(getChunk(registers.rho, sipo_chunk_idx.range(1,0)));
            }
           
            WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_az_write_immediate");
            to_keccak->master_write((static_cast<sc_biguint<64>>(verify_compute_w0_idx) << 8) | verify_compute_az_idx);
            sipo_chunk_idx = sipo_chunk_idx + 1;
            WAIT_UNTIL_DONE(to_keccak_rdy,"verify_compute_az_write_immediate_msg_done");
            sipo_chunk_idx = 0;
            GET_ADDR(rho_id);

            GET_ADDRS(z_ntt_addrs, 7);
            GET_ADDR(az_addr);
            to_sampler->try_write({ .mode = SamplerMode::RejSampler, .destination = az_addr },
                unused, "verify_compute_az_sampling_start");

           // WAIT_UNTIL_DONE(sampler_done_in, "verify_compute_az_sampling");


            to_ntt->try_write({ .mode = (verify_compute_az_idx > 0 ? NttMode::PwmAccuSampler : NttMode::PwmSampler),
                .operand1 = rho_id, .operand2 = z_ntt_addrs.at(verify_compute_az_idx),
                .destination = az_addr }, unused, "verify_compute_az_pwm_start");
            WAIT_FOR_SUBS(sampler_done_in,ntt_done_in, "verify_compute_az_pwm");
          }
          verify_compute_az_idx = 0;

          c_ntt_addr_in->get(c_ntt_addr);
          t_addrs_in->get(t_addrs);
          GET_ADDR(ct_addr);

          to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = c_ntt_addr, .operand2 = t_addrs.at(verify_compute_w0_idx),
              .destination = ct_addr }, unused, "verify_compute_w0_pwm_start");

          WAIT_UNTIL_DONE(ntt_done_in, "verify_compute_w0_pwm");

          ct_addr_in->get(ct_addr);
          GET_ADDR(az_addr);

          to_ntt->try_write({ .mode = NttMode::Pws, .operand1 = ct_addr, .operand2 = az_addr, .destination = az_addr },
              unused, "verify_compute_w0_pws_start");

          WAIT_UNTIL_DONE(ntt_done_in, "verify_compute_w0_pws");
          insert_state("verify_compute_w0_intt_idle");
          az_addr_in->get(az_addr);
          temp_addr_in->get(temp_addr);
          GET_ADDRS(w0_addrs, 8);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = az_addr, .operand2 = temp_addr,
              .destination = w0_addrs.at(verify_compute_w0_idx) }, unused, "verify_compute_w0_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "verify_compute_w0_intt");
        }
        verify_compute_w0_idx = 0;

        GET_ADDR(hint_r_addr);
        to_sig_decode_h->try_write({ .destination = hint_r_addr }, unused, "verify_sig_decode_h_start");

        WAIT_UNTIL_DONE(sig_decode_h_done_in, "verify_sig_decode_h");
         sha3_start_o -> set(true);
        msg_start_o -> set(false);
        insert_state("verify_load_mu_SHA3_START");
        sha3_start_o -> set(false);
        msg_start_o -> set(true);
        //insert_state("verify_load_mu_MSG_START");
       
        insert_state("verify_load_mu_start");
         msg_start_o -> set(false);
        for (sipo_chunk_idx = 0; sipo_chunk_idx < 9; ++sipo_chunk_idx) {
          WAIT_UNTIL_DONE(to_keccak_rdy,"verify_load_mu");
          to_keccak->master_write(getChunk(registers.mu, sipo_chunk_idx.range(2,0)));
        }
        sipo_chunk_idx = sipo_chunk_idx + 1;
        WAIT_UNTIL_DONE(to_keccak_rdy,"verify_load_mu_msg_done");
        sipo_chunk_idx = 0;
        insert_state("verify_load_mu_wait");

        GET_ADDRS(w0_addrs, 8);
        hint_r_addr_in->get(hint_r_addr);
        to_use_hint->try_write({ .operand1 = w0_addrs.at(0), .operand2 = hint_r_addr }, unused, "verify_use_hint_start");

        WAIT_UNTIL_DONE(use_hint_done_in, "verify_use_hint");

        GET_ADDR(verify_res_reg_id);
        to_sampler->try_write({ .mode = SamplerMode::Shake256, .destination = verify_res_reg_id },
            unused, "verify_mu_sampling_start");

        WAIT_UNTIL_DONE(sampler_done_in, "verify_mu_sampling");
        insert_state("verify_end_state");
      }
    }
  }
};

/*
SC_MODULE(AdamsBridgeSecondary) {
 public:
  SC_CTOR(AdamsBridgeSecondary) {
    SC_THREAD(behavior)
  }

  ADDR_PORT(sk_s1_offset);

  // Various memory addresses
  ADDRS_PORT(s1_addrs, 7);
  ADDRS_PORT(t_addrs, 8);
  ADDR_PORT(temp_addr);
  ADDRS_PORT(s2_addrs, 8);
  ADDR_PORT(c_addr);
  ADDR_PORT(c_ntt_addr);
  ADDR_PORT(cs1_addr);
  ADDRS_PORT(y_addrs, 7);
  ADDR_PORT(z_addr);
  ADDRS_PORT(ct_addrs, 8);
  ADDR_PORT(cs2_addr);
  ADDRS_PORT(w0_addrs, 8);
  ADDR_PORT(r0_addr);
  ADDRS_PORT(hint_r_addrs, 8);

  // Refine this to be the start of a signing operation, i.e. either the start of a pure signing operation or the start
  // of the signing part of the combined keygen + sign operation
  shared_in<bool> sign_start_in;
  shared_in<bool> c_valid_in;
  shared_in<bool> y_valid_in;
  shared_out<bool> clear_y_valid_out;
  shared_in<bool> w0_valid_in;
  shared_out<bool> clear_w0_valid_out;
  blocking_out<SkDecodeType> to_sk_decode;
  shared_in<bool> sk_decode_done_in;
  blocking_out<NttType> to_ntt;
  shared_in<bool> ntt_done_in;
  blocking_out<NormCheckType> to_norm_check;
  shared_in<bool> norm_check_done_in;
  shared_in<bool> norm_check_invalid;
  blocking_out<SigEncodeType> to_sig_encode;
  shared_in<bool> sig_encode_done_in;
  blocking_out<MakehintType> to_makehint;
  shared_in<bool> makehint_done_in;
  shared_in<bool> makehint_invalid_in;


 private:
  bool signature_valid;

  [[noreturn]] void behavior() {
    bool subcomponent_done = false;
    bool unused = false;

    while (true) {
      bool start_sign = false;
      do {
        insert_state("secondary_idle");
        sign_start_in->get(start_sign);
      } while (!start_sign);

      GET_ADDR(sk_s1_offset);
      GET_ADDRS(s1_addrs, 7);

      to_sk_decode->try_write({ .source_operand = sk_s1_offset, .destination_addr = s1_addrs.at(0) }, unused,
          "secondary_sk_decode_start");

      WAIT_UNTIL_DONE(sk_decode_done_in, "secondary_sk_decode");

      // NTT(t0)
      sc_uint<8> t_ntt_idx = 0;
      for (t_ntt_idx = 0; t_ntt_idx < 8; ++t_ntt_idx) {
        GET_ADDRS(t_addrs, 8);
        GET_ADDR(temp_addr);

        to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = t_addrs.at(t_ntt_idx), .operand2 = temp_addr,
            .destination = t_addrs.at(t_ntt_idx) }, unused, "secondary_ntt_t_start");

        WAIT_UNTIL_DONE(ntt_done_in, "secondary_ntt_t");
      }
      t_ntt_idx = 0;

      // NTT(s1)
      sc_uint<8> s1_ntt_idx = 0;
      for (s1_ntt_idx = 0; s1_ntt_idx < 7; ++s1_ntt_idx) {
        s1_addrs_in->get(s1_addrs);
        GET_ADDR(temp_addr);

        to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = s1_addrs.at(s1_ntt_idx), .operand2 = temp_addr,
            .destination = s1_addrs.at(s1_ntt_idx) }, unused, "secondary_ntt_s1_start");

        WAIT_UNTIL_DONE(ntt_done_in, "secondary_ntt_s1");
      }
      s1_ntt_idx = 0;

      // NTT(s2)
      sc_uint<8> s2_ntt_idx = 0;
      for (s2_ntt_idx = 0; s2_ntt_idx < 8; ++s2_ntt_idx) {
        GET_ADDRS(s2_addrs, 8);
        GET_ADDR(temp_addr);

        to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = s2_addrs.at(s2_ntt_idx), .operand2 = temp_addr,
            .destination = s2_addrs.at(s2_ntt_idx) }, unused, "secondary_ntt_s2_start");

        WAIT_UNTIL_DONE(ntt_done_in, "secondary_ntt_s2");
      }
      s2_ntt_idx = 0;

      do {
        bool c_valid = false;
        do {
          insert_state("secondary_wait_for_c");
          c_valid_in->get(c_valid);
        } while (!c_valid);

        signature_valid = true;

        // NTT(c)
        GET_ADDR(c_addr);
        GET_ADDR(temp_addr);
        GET_ADDR(c_ntt_addr);

        to_ntt->try_write({ .mode = NttMode::Ntt, .operand1 = c_addr, .operand2 = temp_addr, .destination = c_ntt_addr },
            unused, "secondary_ntt_c_start");

        WAIT_UNTIL_DONE(ntt_done_in, "secondary_ntt_c");

        bool y_valid = false;
        bool w0_valid = false;
        do {
          insert_state("secondary_wait_for_y_and_w0");
          y_valid_in->get(y_valid);
          w0_valid_in->get(w0_valid);
        } while (!y_valid || !w0_valid);

        sc_uint<8> compute_z_idx = 0;
        for (compute_z_idx = 0; compute_z_idx < 7; ++compute_z_idx) {
          c_ntt_addr_in->get(c_ntt_addr);
          s1_addrs_in->get(s1_addrs);
          GET_ADDR(cs1_addr);

          to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = c_ntt_addr, .operand2 = s1_addrs.at(compute_z_idx),
              .destination = cs1_addr }, unused, "secondary_z_pwm_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_z_pwm");

          cs1_addr_in->get(cs1_addr);
          temp_addr_in->get(temp_addr);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = cs1_addr, .operand2 = temp_addr, .destination = cs1_addr },
              unused, "secondary_z_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_z_intt");

          GET_ADDRS(y_addrs, 7);
          cs1_addr_in->get(cs1_addr);
          GET_ADDR(z_addr);

          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = y_addrs.at(compute_z_idx), .operand2 = cs1_addr,
              .destination = z_addr }, unused, "secondary_z_pwa_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_z_pwa");

          z_addr_in->get(z_addr);
          to_norm_check->try_write({ .immediate = norm_check_z_immediate, .source_addr = z_addr }, unused,
              "secondary_z_norm_check_start");

          WAIT_UNTIL_DONE(norm_check_done_in, "secondary_z_norm_check");

          bool norm_check_is_invalid;
          norm_check_invalid->get(norm_check_is_invalid);
          signature_valid = signature_valid && !norm_check_is_invalid;

          z_addr_in->get(z_addr);

          to_sig_encode->try_write({ .source_addr = z_addr, .immediate = compute_z_idx * 0x40 }, unused,
              "secondary_z_sig_encode_start");

          WAIT_UNTIL_DONE(sig_encode_done_in, "secondary_z_sig_encode");
        }
        compute_z_idx = 0;

        clear_y_valid_out->set(true);
        insert_state("secondary_clear_y_valid");
        clear_y_valid_out->set(false);

        sc_uint<8> compute_ct_idx = 0;
        for (compute_ct_idx = 0; compute_ct_idx < 7; ++compute_ct_idx) {
          c_ntt_addr_in->get(c_ntt_addr);
          GET_ADDRS(t_addrs, 8);
          GET_ADDRS(ct_addrs, 8);

          to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = c_ntt_addr, .operand2 = t_addrs.at(compute_ct_idx),
              .destination = ct_addrs.at(compute_ct_idx) }, unused, "secondary_compute_ct_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_compute_ct");
        }
        compute_ct_idx = 0;

        sc_uint<8> compute_ct_intt_idx = 0;
        for (compute_ct_intt_idx = 0; compute_ct_intt_idx < 8; ++compute_ct_intt_idx) {
          GET_ADDRS(ct_addrs, 8);
          temp_addr_in->get(temp_addr);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = ct_addrs.at(compute_ct_intt_idx), .operand2 = temp_addr,
              .destination = ct_addrs.at(compute_ct_intt_idx) }, unused, "secondary_compute_ct_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_compute_ct_intt");
        }
        compute_ct_intt_idx = 0;

        do {
          insert_state("secondary_wait_for_w0");
          w0_valid_in->get(w0_valid);
        } while (!w0_valid);

        sc_uint<8> compute_r_idx = 0;
        for (compute_r_idx = 0; compute_r_idx < 8; ++compute_r_idx) {
          c_ntt_addr_in->get(c_ntt_addr);
          GET_ADDRS(s2_addrs, 8);
          GET_ADDR(cs2_addr);

          to_ntt->try_write({ .mode = NttMode::Pwm, .operand1 = c_ntt_addr, .operand2 = s2_addrs.at(compute_r_idx),
              .destination = cs2_addr }, unused, "secondary_r_pwm_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_r_pwm");

          cs2_addr_in->get(cs2_addr);
          temp_addr_in->get(temp_addr);

          to_ntt->try_write({ .mode = NttMode::Intt, .operand1 = cs2_addr, .operand2 = temp_addr, .destination = cs2_addr },
              unused, "secondary_r_intt_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_r_intt");

          cs2_addr_in->get(cs2_addr);
          GET_ADDRS(w0_addrs, 8);
          GET_ADDR(r0_addr);

          to_ntt->try_write({ .mode = NttMode::Pws, .operand1 = cs2_addr, .operand2 = w0_addrs.at(compute_r_idx),
              .destination = r0_addr }, unused, "secondary_r_pws_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_r_pws");

          r0_addr_in->get(r0_addr);

          to_norm_check->try_write({ .immediate = norm_check_r0_immediate, .source_addr = r0_addr }, unused,
              "secondary_r_norm_check_r0_start");

          WAIT_UNTIL_DONE(norm_check_done_in, "secondary_r_norm_check_r0");

          bool norm_check_is_invalid;
          norm_check_invalid->get(norm_check_is_invalid);
          signature_valid = signature_valid && !norm_check_is_invalid;

          GET_ADDRS(ct_addrs, 8);

          to_norm_check->try_write({ .immediate = norm_check_ct0_immediate, .source_addr = ct_addrs.at(compute_r_idx) },
              unused, "secondary_r_norm_check_ct0_start");

          WAIT_UNTIL_DONE(norm_check_done_in, "secondary_r_norm_check_ct0");

          norm_check_invalid->get(norm_check_is_invalid);
          signature_valid = signature_valid && !norm_check_is_invalid;

          r0_addr_in->get(r0_addr);
          ct_addrs_in->get(ct_addrs);
          GET_ADDRS(hint_r_addrs, 8);

          to_ntt->try_write({ .mode = NttMode::Pwa, .operand1 = r0_addr, .operand2 = ct_addrs.at(compute_r_idx),
              .destination = hint_r_addrs.at(compute_r_idx) }, unused, "secondary_r_pwa_start");

          WAIT_UNTIL_DONE(ntt_done_in, "secondary_r_pwa");
        }
        compute_r_idx = 0;

        clear_w0_valid_out->set(true);
        insert_state("secondary_clear_w0_valid");
        clear_w0_valid_out->set(false);

        GET_ADDRS(hint_r_addrs, 8);

        to_makehint->try_write({ .source_addr = hint_r_addrs.at(0) }, unused, "secondary_makehint_start");

        WAIT_UNTIL_DONE(makehint_done_in, "secondary_makehint");

        bool makehint_invalid = false;
        makehint_invalid_in->get(makehint_invalid);
        signature_valid = signature_valid && !makehint_invalid;
      } while (!signature_valid);
    }
  }
};
*/

#endif