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

#ifndef NTT_CTRL_PWO_PAIRWM_H
#define NTT_CTRL_PWO_PAIRWM_H

#include <array>
#include "Interfaces.h"

#define PWM_MODE 2
#define PWA_MODE 3
#define PWS_MODE 4
#define PAIRWM_MODE 5
#define PWO_READ_ADDR_STEP 1
#define PWO_WRITE_ADDR_STEP 1
#define UNMASKED_BF_LATENCY 10
//#define UNMASKED_BF_LATENCY 8
#define UNMASKED_PWM_LATENCY 5
#define MASKED_PWM_LATENCY 211
//#define MASKED_PWM_LATENCY 5
// INCR_PW_RD_ADDR_REG_SIZE = MASKED_PWM_LATENCY (211)(5) + 1
// #define INCR_PW_RD_ADDR_REG_SIZE 212
//#define INCR_PW_RD_ADDR_REG_SIZE 6
// MASKED_PWM_ACC_LATENCY = MASKED_PWM_LATENCY (211)(5) + MASKED_ADD_SUB_LATENCY (53)(5)
#define MASKED_PWM_ACC_LATENCY 264
//#define MASKED_PWM_ACC_LATENCY 10
// MASKED_INTT_WRBUF_LATENCY = MASKED_BF_STAGE1_LATENCY (266)(10) + (UNMASKED_BF_LATENCY (10)(8) / 2) + 3
#define MASKED_INTT_WRBUF_LATENCY 274
//#define MASKED_INTT_WRBUF_LATENCY 17
// BUF_RDPTR_REG_SIZE = 2 * MASKED_INTT_WRBUF_LATENCY (274)(17)
 #define BUF_RDPTR_REG_SIZE 548
//#define BUF_RDPTR_REG_SIZE 34
// CHUNK_COUNT_REG_SIZE = 4 * (MASKED_INTT_WRBUF_LATENCY (274)(17) - 2)
 #define CHUNK_COUNT_REG_SIZE 1088
//#define CHUNK_COUNT_REG_SIZE 60
// INCR_PW_RD_ADDR_REG_SIZE = MASKED_PWM_LATENCY (211)(5) + 1
 #define INCR_PW_RD_ADDR_REG_SIZE 212 //switched because incr_pw_rd_addr_reg sizes dont match between model and design
//#define INCR_PW_RD_ADDR_REG_SIZE 6
// MASKED_INTT_LATENCY = MASKED_BF_STAGE1_LATENCY (266)(10) + (UNMASKED_BF_LATENCY (10)(8) / 2)
 #define MASKED_INTT_LATENCY 271
//#define MASKED_INTT_LATENCY 14
// PW_RDEN_FSM_REG_SIZE = MASKED_PWM_LATENCY (211)(5) + 1
#define PW_RDEN_FSM_REG_SIZE 212
//#define PW_RDEN_FSM_REG_SIZE 6
#define INTT_WRBUF_LATENCY 13

//MLKEM parameters
#define MLKEM_MASKED_PAIRWM_LATENCY 23
#define MLKEM_UNMASKED_PAIRWM_LATENCY 4
#define MLKEM_MASKED_PAIRWM_ACC_LATENCY 24


enum class PwoReadStatesType {
  PwoReadIdle,
  PwoReadStage,
  PwoReadExec,
  PwoReadExecWait
};


enum class PwoWriteStatesType {
  PwoWriteIdle,
  PwoWriteStage,
  PwoWriteWait,
  PwoWriteMem
};


struct PwoMemAddrs {
  sc_uint<15> pw_base_addr_a;
  sc_uint<15> pw_base_addr_b;
  sc_uint<15> pw_base_addr_c;
};


sc_uint<2> getMemRdIndexOfst(sc_uint<2> index_count, sc_uint<2> index_rand_offset) { //no change
  return index_count + index_rand_offset;
}

sc_uint<15> getPwAddrRst(bool shuffle_en, sc_uint<4> chunk_rand_offset, sc_uint<15> base_addr) {
  if (shuffle_en) {
    return 4 * chunk_rand_offset + base_addr;
  }

  return base_addr;
}

sc_uint<15> getPwAddrIncrAbcWr(bool shuffle_en, sc_uint<15> addr_nxt, sc_uint<15> current_addr, sc_uint<15> addr_step) { //line 481-491, no change
  if (shuffle_en) {
    return addr_nxt;
  }

  return current_addr + addr_step;
}

sc_uint<15> getPwAddrAbcWr(bool rst_addr, bool incr_addr, sc_uint<15> addr_rst, sc_uint<15> addr_incr, //line 475-491, no change
  sc_uint<15> addr_default) {
  if (rst_addr) {
    return addr_rst;
  }

  if (incr_addr) {
    return addr_incr;
  }

  return addr_default;
}

sc_uint<15> getPwAddrCrd(bool rst_pw_addr, bool shuffle_en, bool pwm_mode, bool pairwm_mode, bool mlkem, bool accumulate, bool masking_en,
  sc_biguint<INCR_PW_RD_ADDR_REG_SIZE> incr_pw_rd_addr_reg, bool incr_pw_rd_addr, sc_uint<4> chunk_rand_offset,
  sc_uint<15> pw_base_addr_c, sc_uint<15> pw_mem_rd_addr_c_nxt, sc_uint<15> pw_mem_rd_addr_c) {
  if (rst_pw_addr) {
    return shuffle_en ? sc_uint<15>(pw_base_addr_c + 4 * chunk_rand_offset) : pw_base_addr_c;
  }

  if ((pwm_mode || pairwm_mode) && accumulate) { //changes in line 494 495
    if ((masking_en && (mlkem ? (shuffle_en ? incr_pw_rd_addr_reg[MASKED_PWM_LATENCY-(MLKEM_MASKED_PAIRWM_LATENCY-6)] : incr_pw_rd_addr_reg[MASKED_PWM_LATENCY-(MLKEM_MASKED_PAIRWM_LATENCY-6+1)]) : incr_pw_rd_addr_reg[0])) || (!masking_en && incr_pw_rd_addr)) {
      return pw_mem_rd_addr_c_nxt;
    }

    return pw_mem_rd_addr_c;
  }

  return 0;
}

sc_uint<15> getMaskedShuffledPwmMemWrAddrCnxtAccumulate(sc_uint<15> pw_base_addr_c, //line 420 no change
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_uint<2> masked_pwm_buf_rdptr_d3) {
  return pw_base_addr_c
      + 4 * chunk_count_reg.range(
        4 * (MASKED_INTT_LATENCY - MASKED_PWM_ACC_LATENCY - 3) + 3,
        4 * (MASKED_INTT_LATENCY - MASKED_PWM_ACC_LATENCY - 3))
      + PWO_WRITE_ADDR_STEP * masked_pwm_buf_rdptr_d3;
}

sc_uint<15> getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate(sc_uint<15> pw_base_addr_c, //new variable in line 423
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_uint<2> masked_pwm_buf_rdptr_d3) {
  return pw_base_addr_c
      + 4 * chunk_count_reg.range(
        4 * (0) + 3,
        4 * (0))
      + PWO_WRITE_ADDR_STEP * masked_pwm_buf_rdptr_d3;
}

sc_uint<15> getMaskedShuffledPwmMemWrAddrCnxt(sc_uint<15> pw_base_addr_c, //line 419 no change
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_uint<2> masked_pwm_buf_rdptr_d2) {
  return pw_base_addr_c
      + 4 * chunk_count_reg.range(
        4 * (MASKED_INTT_LATENCY - MASKED_PWM_LATENCY - 2) + 3,
        4 * (MASKED_INTT_LATENCY - MASKED_PWM_LATENCY - 2))
      + PWO_WRITE_ADDR_STEP * masked_pwm_buf_rdptr_d2;
}

sc_uint<15> getMlkemMaskedShuffledPwmMemWrAddrCnxt(sc_uint<15> pw_base_addr_c, //new variable in line 422
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_uint<2> masked_pwm_buf_rdptr_d3) { // d2 or d3?
  return pw_base_addr_c
      + 4 * chunk_count_reg.range(
        4 * (0) + 3,
        4 * (0))
      + PWO_WRITE_ADDR_STEP * masked_pwm_buf_rdptr_d3;
}

sc_uint<15> getShuffledPwMemWrAddrCnxt(bool pwm_mode, bool pwa_mode, bool pws_mode, bool pairwm_mode, bool accumulate, sc_uint<15> pw_base_addr_c,
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_biguint<BUF_RDPTR_REG_SIZE> buf_rdptr_reg) {
  if (pwm_mode && accumulate) { //no change
    return pw_base_addr_c
        + sc_uint<15>(4) * chunk_count_reg.range(4 * (UNMASKED_PWM_LATENCY - 2) + 3, 4 * (UNMASKED_PWM_LATENCY - 2))
        + sc_uint<15>(PWO_WRITE_ADDR_STEP)
        * buf_rdptr_reg.range(2 * (UNMASKED_PWM_LATENCY - 2) + 1, 2 * (UNMASKED_PWM_LATENCY - 2));
  }

  if (pwm_mode) {  //no change
    return pw_base_addr_c
        + sc_uint<15>(4) * chunk_count_reg.range(4 * (UNMASKED_PWM_LATENCY - 1) + 3, 4 * (UNMASKED_PWM_LATENCY - 1))
        + sc_uint<15>(PWO_WRITE_ADDR_STEP)
        * buf_rdptr_reg.range(2 * (UNMASKED_PWM_LATENCY - 1) + 1, 2 * (UNMASKED_PWM_LATENCY - 1));
  }

  if (pairwm_mode && accumulate) {  //added new logic in line 409
    return pw_base_addr_c
        + sc_uint<15>(4) * chunk_count_reg.range(4 * (MLKEM_UNMASKED_PAIRWM_LATENCY - 1) + 3, 4 * (MLKEM_UNMASKED_PAIRWM_LATENCY - 1))
        + sc_uint<15>(PWO_WRITE_ADDR_STEP)
        * buf_rdptr_reg.range(2 * (MLKEM_UNMASKED_PAIRWM_LATENCY - 1) + 1, 2 * (MLKEM_UNMASKED_PAIRWM_LATENCY - 1));
  }

  if (pairwm_mode) { //added new logic in line 409
    return pw_base_addr_c
        + sc_uint<15>(4) * chunk_count_reg.range(4 * (MLKEM_UNMASKED_PAIRWM_LATENCY) + 3, 4 * (MLKEM_UNMASKED_PAIRWM_LATENCY))
        + sc_uint<15>(PWO_WRITE_ADDR_STEP)
        * buf_rdptr_reg.range(2 * (MLKEM_UNMASKED_PAIRWM_LATENCY) + 1, 2 * (MLKEM_UNMASKED_PAIRWM_LATENCY));
  }
  if (pwa_mode || pws_mode) {
    return pw_base_addr_c //no change
      + sc_uint<15>(4) * chunk_count_reg.range(31, 28)
      + sc_uint<15>(PWO_WRITE_ADDR_STEP) * buf_rdptr_reg.range(15, 14);
  }
  
  return 0;
}

sc_uint<15> getPwAddrCwr(bool rst_pw_addr, bool incr_pw_wr_addr, bool shuffle_en, bool masking_en, bool accumulate, bool mlkem,
  sc_uint<4> chunk_rand_offset, sc_uint<15> pw_base_addr_c, sc_uint<15> masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate, sc_uint<15> mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate,
  sc_uint<15> masked_shuffled_pw_mem_wr_addr_c_nxt, sc_uint<15> mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt, sc_uint<15> shuffled_pw_mem_wr_addr_c_nxt,
  sc_uint<15> pw_mem_wr_addr_c) {
  if (rst_pw_addr) { //line 479, no change
    if (shuffle_en) {
      return 4 * chunk_rand_offset + pw_base_addr_c;
    }

    return pw_base_addr_c;
  }

  if (incr_pw_wr_addr) { //line 504 added mlkem cases
    if (masking_en && shuffle_en) {
      if (accumulate) {
        if (mlkem) {
            return mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate;
        }

        return masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate;
      }
      if (mlkem) {
        return mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt;
      }
      return masked_shuffled_pw_mem_wr_addr_c_nxt;
    }

    if (shuffle_en) {
      return shuffled_pw_mem_wr_addr_c_nxt;
    }

    return pw_mem_wr_addr_c + PWO_WRITE_ADDR_STEP;
  }

  return pw_mem_wr_addr_c;
}

sc_uint<15> getPwAddrNxt(sc_uint<15> base_addr, sc_uint<4> chunk_count, sc_uint<15> step, sc_uint<15> offset) { //line 398, no change
  return base_addr + 4 * chunk_count + step * offset;
}

sc_uint<15> getPwAddrCnxt(bool pwm_mode, bool pairwm_mode, bool mlkem, bool accumulate, bool shuffle_en, bool masking_en, sc_uint<15> rd_addr_c,
  sc_uint<15> masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate, sc_uint<15> mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate,
  sc_uint<15> shuffled_pw_mem_rd_addr_c_nxt_accumulate) {
  if ((pwm_mode || pairwm_mode) && accumulate) { //line 430 added pairwm_mode case 
    if (shuffle_en) {
      if (masking_en) {
        if (mlkem) { //line 435 added mlkem case
            return mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate;
        }
        return masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate;
      }

      return shuffled_pw_mem_rd_addr_c_nxt_accumulate;
    }

    return rd_addr_c + PWO_READ_ADDR_STEP;
  }

  return 0;
}

sc_biguint<BUF_RDPTR_REG_SIZE> getBufRdptrReg(bool masking_en, bool butterfly_ready, bool accumulate,
  bool incr_pw_rd_addr, bool pwm_mode, bool pairwm_mode, bool masked_pwm_exec_in_progres,
  sc_biguint<BUF_RDPTR_REG_SIZE> buf_rdptr_reg, sc_uint<2> mem_rd_index_ofst) {
  sc_biguint<BUF_RDPTR_REG_SIZE> new_buf_rdptr_reg = 0;

  if (!masking_en && (butterfly_ready || incr_pw_rd_addr)) {
    new_buf_rdptr_reg = (static_cast<sc_biguint<BUF_RDPTR_REG_SIZE>>(mem_rd_index_ofst) << 2 * UNMASKED_BF_LATENCY)
        | buf_rdptr_reg.range(2 * UNMASKED_BF_LATENCY + 1, 2);
  } else if (pwm_mode && masking_en && masked_pwm_exec_in_progres) {
    if (accumulate) {
      new_buf_rdptr_reg = (static_cast<sc_biguint<BUF_RDPTR_REG_SIZE>>(mem_rd_index_ofst) << 2 * MASKED_PWM_ACC_LATENCY)
          | buf_rdptr_reg.range(2 * MASKED_PWM_ACC_LATENCY + 1, 2);
    } else {
      new_buf_rdptr_reg = (static_cast<sc_biguint<BUF_RDPTR_REG_SIZE>>(mem_rd_index_ofst) << 2 * MASKED_PWM_LATENCY)
          | buf_rdptr_reg.range(2 * MASKED_PWM_LATENCY + 1, 2);
    }
  } else if (pairwm_mode && masking_en && masked_pwm_exec_in_progres) { //LINE 707 added pairwm_mode case
    if (accumulate) {
      new_buf_rdptr_reg = (static_cast<sc_biguint<BUF_RDPTR_REG_SIZE>>(mem_rd_index_ofst) << 2 * MLKEM_MASKED_PAIRWM_ACC_LATENCY)
          | buf_rdptr_reg.range(2 * MLKEM_MASKED_PAIRWM_ACC_LATENCY + 1, 2);
    } else {
      new_buf_rdptr_reg = (static_cast<sc_biguint<BUF_RDPTR_REG_SIZE>>(mem_rd_index_ofst) << 2 * MLKEM_MASKED_PAIRWM_LATENCY)
          | buf_rdptr_reg.range(2 * MLKEM_MASKED_PAIRWM_LATENCY + 1, 2);
    }
  } else {
    new_buf_rdptr_reg = 0;
  }

  return new_buf_rdptr_reg;
}


sc_biguint<INCR_PW_RD_ADDR_REG_SIZE> getIncrPwRdAddrReg(bool masking_en, bool pwm_mode, bool pairwm_mode,
  sc_biguint<INCR_PW_RD_ADDR_REG_SIZE> incr_pw_rd_addr_reg, bool incr_pw_rd_addr) {

  sc_biguint<INCR_PW_RD_ADDR_REG_SIZE> result = 0;

  if (masking_en && (pwm_mode || pairwm_mode)) {
    result = incr_pw_rd_addr_reg.range(INCR_PW_RD_ADDR_REG_SIZE - 1, 1);
    if (incr_pw_rd_addr) {
      result |= static_cast<sc_biguint<INCR_PW_RD_ADDR_REG_SIZE>>(1) << (INCR_PW_RD_ADDR_REG_SIZE - 1);
    }
    else {
      result |= (static_cast<sc_biguint<INCR_PW_RD_ADDR_REG_SIZE>>(0) << (INCR_PW_RD_ADDR_REG_SIZE - 1));
    }
  } else {
    result = incr_pw_rd_addr_reg;
  }

  return result;
}

sc_biguint<CHUNK_COUNT_REG_SIZE> getChunkCountReg(bool pwm_mode, bool pairwm_mode, bool accumulate, bool masking_en,
  bool masked_pwm_exec_in_progress, bool butterfly_ready, bool incr_pw_rd_addr,
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, sc_uint<4> chunk_count) {
  sc_biguint<CHUNK_COUNT_REG_SIZE> result = 0;

  if (pwm_mode && masking_en && masked_pwm_exec_in_progress) {
    result = (static_cast<sc_biguint<CHUNK_COUNT_REG_SIZE>>(chunk_count) << 4 * (MASKED_INTT_WRBUF_LATENCY - 3))
        | chunk_count_reg.range(4 * (MASKED_INTT_WRBUF_LATENCY - 3) + 3, 4);
  } else if (pairwm_mode && masking_en && masked_pwm_exec_in_progress) { // line 760, added pairwm_mode case
    if (accumulate) {
    result = (static_cast<sc_biguint<CHUNK_COUNT_REG_SIZE>>(chunk_count) << 4 * (MLKEM_MASKED_PAIRWM_ACC_LATENCY + 3)) // not sure where to put MASKED_INTT_LATENCY part
        | chunk_count_reg.range(4 * (MLKEM_MASKED_PAIRWM_ACC_LATENCY + 3) + 3, 4);
    }
    else {
      result = (static_cast<sc_biguint<CHUNK_COUNT_REG_SIZE>>(chunk_count) << 4 * (MLKEM_MASKED_PAIRWM_LATENCY + 3)) // not sure where to put MASKED_INTT_LATENCY part
          | chunk_count_reg.range(4 * (MLKEM_MASKED_PAIRWM_LATENCY + 3) + 3, 4);
    }
  } else if (butterfly_ready || incr_pw_rd_addr) {
    result = (static_cast<sc_biguint<CHUNK_COUNT_REG_SIZE>>(chunk_count) << 4 * UNMASKED_BF_LATENCY)
        | chunk_count_reg.range(4 * UNMASKED_BF_LATENCY + 3, 4);
  } else {
    result = chunk_count_reg;
  }

  return result;
}

sc_biguint<PW_RDEN_FSM_REG_SIZE> getPwRdenFsmReg(sc_biguint<PW_RDEN_FSM_REG_SIZE> pw_rden_fsm_reg,
  bool pw_rden_fsm) {
  return (static_cast<sc_biguint<PW_RDEN_FSM_REG_SIZE>>(pw_rden_fsm ? 1 : 0) << (PW_RDEN_FSM_REG_SIZE - 1))
      | pw_rden_fsm_reg.range(PW_RDEN_FSM_REG_SIZE - 1, 1);
}

std::array<sc_uint<7>, 8> getTwiddleRandOffsets(sc_uint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, //line 516 no change for gs but added design for pairwm_mode, should be added here or in pairwm_mode model?
  sc_uint<4> chunk_count, sc_uint<2> buf_count, bool pairwm_mode) {
  //int chunk_count_reg_idx_1 = 4 * UNMASKED_BF_LATENCY;

  return std::array<sc_uint<7>, 8>{
    (pairwm_mode ? sc_uint<7> (chunk_count * 4 + buf_count) : sc_uint<7> (((chunk_count_reg.range(43,40/*4 * UNMASKED_BF_LATENCY + 3, 4 * UNMASKED_BF_LATENCY) & 0x3*/)) * 4  + 0))),
    (((chunk_count_reg.range(43,40/*4 * UNMASKED_BF_LATENCY + 3, 4 * UNMASKED_BF_LATENCY) & 0x3)*/)& 0x3) * 4  + 0)),
    0,
    0,
    0,
    0,
    0,
    0
  };
}

sc_uint<7> getTwiddleAddrReg(bool incr, bool rst, sc_uint<7> incr_addr, sc_uint<7> default_addr) { //no change, line 570-573
  if (incr) {
    return incr_addr;
  }

  if (rst) {
    return sc_uint<7>(0);
  }

  return default_addr;
}

sc_uint<7> getTwiddleIncrAddr(bool shuffle_en, sc_uint<3> rounds_count, std::array<sc_uint<7>, 8> rand_offsets, //line 571, no change
  std::array<sc_uint<7>, 8> end_addrs, sc_uint<7> default_addr) {
  if (shuffle_en) {
    return rand_offsets[rounds_count];
  }

  if (default_addr == end_addrs[rounds_count]) {
    return sc_uint<7>(0);
  }

  return default_addr + 1;
}

SC_MODULE(ntt_ctrl_pwo_pairwm) {
public:
  SC_CTOR(ntt_ctrl_pwo_pairwm) {
    SC_THREAD(read)
    SC_THREAD(write)
    SC_THREAD(commons)
  }

  shared_in<sc_uint<3>> ntt_mode_in;
  shared_in<bool> ntt_enable_in;
  shared_in<bool> buf0_valid_in;
  shared_in<bool> butterfly_ready_in;
  shared_in<bool> sampler_valid_in;
  shared_in<bool> accumulate_in;
  shared_in<bool> shuffle_en_in;
  shared_in<PwoMemAddrs> pwo_mem_base_addr_in;
  shared_in<sc_uint<6>> random_in;
  shared_in<bool> masking_en_in;
  shared_in<bool> mlkem_in; //added mlkem input

  // Write custom property, as bf_enable combinationally depends on shuffle_en
  // shared_out<bool> bf_enable_out;
  shared_out<sc_uint<3>> opcode_out;
  shared_out<bool> masking_en_ctrl_out;
  shared_out<bool> buf_wren_out;
  shared_out<bool> buf_rden_out;
  shared_out<sc_uint<2>> buf_wrptr_out;
  shared_out<sc_uint<2>> buf_rdptr_out;
  shared_out<bool> mem_rd_en_out;
  shared_out<bool> mem_wr_en_out;
  shared_out<bool> buf_wr_rst_count_out;
  shared_out<bool> buf_rd_rst_count_out;
  shared_out<sc_uint<15>> pw_mem_rd_addr_a_out;
  shared_out<sc_uint<15>> pw_mem_rd_addr_b_out;
  shared_out<sc_uint<15>> pw_mem_rd_addr_c_out;
  shared_out<sc_uint<15>> pw_mem_wr_addr_c_out;
  // Write custom property, as pw_rden combinationally depends on shuffle_en
  // shared_out<bool> pw_rden_out;
  // Write custom property, as pw_wren combinationally depends on shuffle_en
  // shared_out<bool> pw_wren_out;
  // Write custom property, as pw_shared_mem_rden_out combinationally depends on shuffle_en, masking_en, and accumulate
  // shared_out<bool> pw_shared_mem_rden_out;
  // Write custom property, as busy combinationally depends on both processes
  // shared_out<bool> busy_out;
  shared_out<bool> done_out;

  // Write a custom property for this signal, as it combinationally depends on both processes
  shared_in<bool> rst_rounds_in;


private:
  PwoReadStatesType read_state;
  PwoWriteStatesType write_state;

  sc_uint<3> rounds_count;
  sc_uint<7> rd_valid_count;
  sc_uint<7> wr_valid_count;
  sc_uint<2> index_count;
  sc_uint<2> index_rand_offset;
  sc_uint<4> chunk_count;
  sc_uint<2> buf_count;
  sc_uint<4> chunk_rand_offset;
  sc_uint<15> pw_mem_rd_addr_a_reg;
  sc_uint<15> pw_mem_rd_addr_b_reg;
  sc_uint<15> pw_mem_rd_addr_c_reg;
  sc_uint<15> pw_mem_wr_addr_c_reg;
  sc_uint<3> bf_enable_reg;
  sc_uint<3> bf_enable_reg_dummy;
  sc_uint<7> twiddle_addr_reg;
  sc_uint<7> twiddle_addr_reg_d2;
  sc_uint<7> twiddle_addr_reg_d3;
  sc_uint<7> twiddle_addr_reg_d3_dummy;

  sc_biguint<INCR_PW_RD_ADDR_REG_SIZE> incr_pw_rd_addr_reg;
  sc_biguint<BUF_RDPTR_REG_SIZE> buf_rdptr_reg;
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg;
  sc_biguint<PW_RDEN_FSM_REG_SIZE> pw_rden_fsm_reg;

  bool pw_rden_reg;
  bool pw_rden_reg_dummy;
  bool pw_wren_reg;
  bool pw_wren_reg_dummy;
  bool shuffled_pw_rden_fsm_reg;
  bool shuffled_pw_rden_fsm_reg_dummy;
  bool incr_twiddle_addr_reg;

  [[noreturn]] void read() {
    read_state = PwoReadStatesType::PwoReadIdle;

    PwoReadStatesType next_state = PwoReadStatesType::PwoReadIdle;
    bool incr_pw_rd_addr = false;
    bool bf_enable_fsm = false;
    bool pw_rden_fsm = false;

    while (true) {
      if (read_state == PwoReadStatesType::PwoReadIdle) {
        insert_state("read_idle");
        next_state = PwoReadStatesType::PwoReadIdle;
        incr_pw_rd_addr = false;
        bf_enable_fsm = false;
        pw_rden_fsm = false;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = PwoReadStatesType::PwoReadStage;
        }
      } else if (read_state == PwoReadStatesType::PwoReadStage) {
        insert_state("read_stage");
        next_state = PwoReadStatesType::PwoReadStage;
        incr_pw_rd_addr = false;
        bf_enable_fsm = false;
        pw_rden_fsm = false;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (rounds_count == 1 && !ntt_enable) {
          next_state = PwoReadStatesType::PwoReadIdle;
        } else if (write_state == PwoWriteStatesType::PwoWriteStage && rounds_count != 1) {
          next_state = PwoReadStatesType::PwoReadExec;
        }
      } else if (read_state == PwoReadStatesType::PwoReadExec) {
        insert_state("read_exec");
        next_state = PwoReadStatesType::PwoReadExec;

        bool sampler_valid = false;
        sampler_valid_in->get(sampler_valid);

        incr_pw_rd_addr = sampler_valid;
        bf_enable_fsm = sampler_valid;
        pw_rden_fsm = sampler_valid;

        if (!sampler_valid && rd_valid_count < 0x40) {
          next_state = PwoReadStatesType::PwoReadExecWait;
        } else if (rd_valid_count >= 0x3F) {
          next_state = PwoReadStatesType::PwoReadStage;
        }
      } else {
        // if (read_state == PwoReadStatesType::PwoReadExecWait) {
        insert_state("read_exec_wait");
        next_state = PwoReadStatesType::PwoReadExecWait;

        bool sampler_valid = false;
        sampler_valid_in->get(sampler_valid);

        incr_pw_rd_addr = sampler_valid;
        bf_enable_fsm = sampler_valid;
        pw_rden_fsm = sampler_valid;

        if (sampler_valid) {
          next_state = PwoReadStatesType::PwoReadExec;
        }
      }

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool sampler_valid = false;
      sampler_valid_in->get(sampler_valid);

      bool accumulate = false;
      accumulate_in->get(accumulate);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      bool masking_en = false;
      masking_en_in->get(masking_en);

      bool mlkem = false; //added mlkem input
      mlkem_in->get(mlkem);

      PwoMemAddrs base_addrs;
      pwo_mem_base_addr_in->get(base_addrs);

      sc_uint<3> ntt_mode;
      ntt_mode_in->get(ntt_mode);

      bool pwm_mode = ntt_mode == PWM_MODE;
      bool pairwm_mode = mlkem && (ntt_mode == PAIRWM_MODE);

      std::array<sc_uint<7>, 8> twiddle_rand_offset_array = getTwiddleRandOffsets(chunk_count_reg,
        chunk_count,
        buf_count,
        pairwm_mode);

      std::array<sc_uint<7>, 8> twiddle_end_addr_array = {
        63, 15, 3, 0, 0, 0, 0, 0
      };

      std::array<sc_uint<7>, 8> twiddle_offset_array = {
        (pairwm_mode ? sc_uint<7>(21) : sc_uint<7>(0)), 64, 80, 84, 0, 0, 0, 0
      };
      twiddle_addr_reg_d3_dummy = twiddle_addr_reg_d3_dummy + twiddle_addr_reg_d3;
      twiddle_addr_reg_d3 = twiddle_addr_reg_d2;
      /*twiddle_addr_reg_d2 = shuffle_en ? pairwm_mode ? 
            (twiddle_rand_offset_array[rounds_count] + sc_uint<2> ((index_count + index_rand_offset) % 4) + twiddle_offset_array[rounds_count])
          : (twiddle_rand_offset_array[rounds_count] + twiddle_offset_array[rounds_count])
          : (twiddle_addr_reg + twiddle_offset_array[rounds_count]);*/
      twiddle_addr_reg_d2 = !shuffle_en ? (twiddle_addr_reg + twiddle_offset_array[rounds_count]) : (shuffle_en && pairwm_mode) ? 
            (twiddle_rand_offset_array[rounds_count] + sc_uint<2> ((index_count + index_rand_offset) % 4) + twiddle_offset_array[rounds_count])
          : (twiddle_rand_offset_array[rounds_count] + twiddle_offset_array[rounds_count]);
      

      twiddle_addr_reg = getTwiddleAddrReg(incr_twiddle_addr_reg,
        read_state == PwoReadStatesType::PwoReadIdle
        || (read_state == PwoReadStatesType::PwoReadStage && !butterfly_ready),
        getTwiddleIncrAddr(shuffle_en,
          rounds_count,
          twiddle_rand_offset_array,
          twiddle_end_addr_array,
          twiddle_addr_reg),
        twiddle_addr_reg);

      incr_twiddle_addr_reg = (read_state == PwoReadStatesType::PwoReadExec || read_state == PwoReadStatesType::PwoReadExecWait) && (pairwm_mode && sampler_valid);

      rd_valid_count = (read_state == PwoReadStatesType::PwoReadIdle || read_state == PwoReadStatesType::PwoReadStage)
          ? sc_uint<7>(0)
          : (sampler_valid ? sc_uint<7>(rd_valid_count + 1) : rd_valid_count);

      bf_enable_reg_dummy = bf_enable_reg + bf_enable_reg_dummy;
      bf_enable_reg = (bf_enable_reg << 1) | (bf_enable_fsm ? sc_uint<3>(1) : sc_uint<3>(0));

      sc_uint<2> mem_rd_index_ofst = getMemRdIndexOfst(index_count, index_rand_offset);

      sc_uint<15> pw_mem_rd_addr_a_nxt = getPwAddrNxt(base_addrs.pw_base_addr_a,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> pw_mem_rd_addr_b_nxt = getPwAddrNxt(base_addrs.pw_base_addr_b,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> shuffled_pw_mem_rd_addr_c_nxt_accumulate = base_addrs.pw_base_addr_c + 4 * chunk_count
          + PWO_READ_ADDR_STEP * mem_rd_index_ofst;
      sc_uint<15> masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate = (pwm_mode && masking_en)
          ? sc_uint<15>(base_addrs.pw_base_addr_c
            + 4 * static_cast<sc_uint<4>>(chunk_count_reg.range(
              4 * (MASKED_INTT_LATENCY - MASKED_PWM_LATENCY) + 3,
              4 * (MASKED_INTT_LATENCY - MASKED_PWM_LATENCY)))
            + PWO_READ_ADDR_STEP * static_cast<sc_uint<2>>(buf_rdptr_reg.range(
              2 * (MASKED_PWM_ACC_LATENCY - MASKED_PWM_LATENCY) + 1,
              2 * (MASKED_PWM_ACC_LATENCY - MASKED_PWM_LATENCY))))
          : sc_uint<15>(0);

        sc_uint<15> mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate = (pairwm_mode && masking_en) //line 428, mlkem new variable assignment
                ? sc_uint<15>(base_addrs.pw_base_addr_c
                    + 4 * static_cast<sc_uint<4>>(chunk_count_reg.range(
                    4 * ((MLKEM_MASKED_PAIRWM_ACC_LATENCY+3)-(MLKEM_MASKED_PAIRWM_LATENCY-6)) + 3,
                    4 * ((MLKEM_MASKED_PAIRWM_ACC_LATENCY+3)-(MLKEM_MASKED_PAIRWM_LATENCY-6))))
                    + PWO_READ_ADDR_STEP * static_cast<sc_uint<2>>(buf_rdptr_reg.range(
                    2 * (MLKEM_MASKED_PAIRWM_ACC_LATENCY-(MLKEM_MASKED_PAIRWM_LATENCY-6)) + 1,
                    2 * (MLKEM_MASKED_PAIRWM_ACC_LATENCY-(MLKEM_MASKED_PAIRWM_LATENCY-6)))))
                : sc_uint<15>(0);

      sc_uint<15> pw_mem_rd_addr_c_nxt = getPwAddrCnxt(pwm_mode,
        pairwm_mode,
        mlkem, //added mlkem input
        accumulate,
        shuffle_en,
        masking_en,
        pw_mem_rd_addr_c_reg,
        masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate,
        mlkem_masked_shuffled_pw_mem_rd_addr_c_nxt_accumulate,
        shuffled_pw_mem_rd_addr_c_nxt_accumulate);

      bool rst_pw_addr =
          write_state == PwoWriteStatesType::PwoWriteIdle || write_state == PwoWriteStatesType::PwoWriteStage;

      pw_mem_rd_addr_a_reg = getPwAddrAbcWr(rst_pw_addr,
        incr_pw_rd_addr,
        getPwAddrRst(shuffle_en, chunk_rand_offset, base_addrs.pw_base_addr_a),
        getPwAddrIncrAbcWr(shuffle_en, pw_mem_rd_addr_a_nxt, pw_mem_rd_addr_a_reg, PWO_READ_ADDR_STEP),
        pw_mem_rd_addr_a_reg);
      pw_mem_rd_addr_a_out->set(pw_mem_rd_addr_a_reg);

      pw_mem_rd_addr_b_reg = getPwAddrAbcWr(rst_pw_addr,
        incr_pw_rd_addr,
        getPwAddrRst(shuffle_en, chunk_rand_offset, base_addrs.pw_base_addr_b),
        getPwAddrIncrAbcWr(shuffle_en, pw_mem_rd_addr_b_nxt, pw_mem_rd_addr_b_reg, PWO_READ_ADDR_STEP),
        pw_mem_rd_addr_b_reg);
      pw_mem_rd_addr_b_out->set(pw_mem_rd_addr_b_reg);

      pw_mem_rd_addr_c_reg = getPwAddrCrd(rst_pw_addr,
        shuffle_en,
        pwm_mode,
        pairwm_mode,
        mlkem, //added mlkem input
        accumulate,
        masking_en,
        incr_pw_rd_addr_reg,
        incr_pw_rd_addr,
        chunk_rand_offset,
        base_addrs.pw_base_addr_c,
        pw_mem_rd_addr_c_nxt,
        pw_mem_rd_addr_c_reg);
      pw_mem_rd_addr_c_out->set(pw_mem_rd_addr_c_reg);

      pw_rden_reg_dummy = pw_rden_reg_dummy && pw_rden_reg;
      pw_rden_reg = pw_rden_fsm;
      shuffled_pw_rden_fsm_reg_dummy = shuffled_pw_rden_fsm_reg_dummy && shuffled_pw_rden_fsm_reg;
      shuffled_pw_rden_fsm_reg = (mlkem ? 
                                  (pw_rden_fsm_reg.range(211-(MLKEM_MASKED_PAIRWM_LATENCY-6+1), 211-(MLKEM_MASKED_PAIRWM_LATENCY-6+1)) != 0x0)
                                   : (pw_rden_fsm_reg & 0x1) != 0x0); //line 1178, added mlkem case
      pw_rden_fsm_reg = getPwRdenFsmReg(pw_rden_fsm_reg, pw_rden_fsm);

      bool masked_pwm_exec_in_progress = masking_en && (pwm_mode || pairwm_mode) //line 795, added pairwm_mode case
          && ((read_state != PwoReadStatesType::PwoReadIdle && read_state != PwoReadStatesType::PwoReadStage)
            || (write_state != PwoWriteStatesType::PwoWriteIdle && write_state != PwoWriteStatesType::PwoWriteStage));

      buf_rdptr_reg = getBufRdptrReg(masking_en,
        butterfly_ready,
        accumulate,
        incr_pw_rd_addr,
        pwm_mode,
        pairwm_mode,
        masked_pwm_exec_in_progress,
        buf_rdptr_reg,
        mem_rd_index_ofst);

      chunk_count_reg = getChunkCountReg(pwm_mode,
        pairwm_mode,
        accumulate,
        masking_en,
        masked_pwm_exec_in_progress,
        butterfly_ready,
        incr_pw_rd_addr,
        chunk_count_reg,
        chunk_count);

      incr_pw_rd_addr_reg = getIncrPwRdAddrReg(masking_en, pwm_mode, pairwm_mode, incr_pw_rd_addr_reg, incr_pw_rd_addr);

      read_state = next_state;
    }
  }

  [[noreturn]] void write() {
    write_state = PwoWriteStatesType::PwoWriteIdle;
    sc_uint<2> masked_pwm_buf_rdptr_d1 = 0;
    sc_uint<2> masked_pwm_buf_rdptr_d2 = 0;
    sc_uint<2> masked_pwm_buf_rdptr_d3 = 0;

    PwoWriteStatesType next_state;
    bool incr_rounds = false;
    bool latch_chunk_rand_offset = false;
    bool rst_pw_addr = false;

    while (true) {
      if (write_state == PwoWriteStatesType::PwoWriteIdle) {
        insert_state("write_idle");
        next_state = PwoWriteStatesType::PwoWriteIdle;
        incr_rounds = false;
        latch_chunk_rand_offset = false;
        rst_pw_addr = true;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = PwoWriteStatesType::PwoWriteStage;
          latch_chunk_rand_offset = true;
        }
      } else if (write_state == PwoWriteStatesType::PwoWriteStage) {
        insert_state("write_stage");
        incr_rounds = false;
        latch_chunk_rand_offset = false;
        rst_pw_addr = true;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        if (rounds_count == 1) {
          next_state = PwoWriteStatesType::PwoWriteIdle;
        } else if (shuffle_en) {
          next_state = PwoWriteStatesType::PwoWriteMem;
        } else {
          next_state = PwoWriteStatesType::PwoWriteWait;
        }
      } else if (write_state == PwoWriteStatesType::PwoWriteWait) {
        insert_state("write_wait");
        next_state = PwoWriteStatesType::PwoWriteWait;
        incr_rounds = false;
        latch_chunk_rand_offset = false;
        rst_pw_addr = false;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        bool butterfly_ready = false;
        butterfly_ready_in->get(butterfly_ready);

        if (shuffle_en) {
          next_state = PwoWriteStatesType::PwoWriteStage;
          incr_rounds = true;
          latch_chunk_rand_offset = true;
        } else if (butterfly_ready) {
          next_state = PwoWriteStatesType::PwoWriteMem;
        }
      } else {
        // if (write_state == PwoWriteStatesType::PwoWriteMem) {
        insert_state("write_mem");
        next_state = PwoWriteStatesType::PwoWriteMem;
        incr_rounds = false;
        latch_chunk_rand_offset = false;
        rst_pw_addr = false;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        bool butterfly_ready = false;
        butterfly_ready_in->get(butterfly_ready);

        if ((!shuffle_en && !butterfly_ready && wr_valid_count < 0x40)
          || (shuffle_en && butterfly_ready && wr_valid_count == 0x3F)) {
          next_state = PwoWriteStatesType::PwoWriteWait;
        } else if (!shuffle_en && wr_valid_count == 0x40) {
          next_state = PwoWriteStatesType::PwoWriteStage;
          incr_rounds = true;
          latch_chunk_rand_offset = true;
        }
      }

      bool rst_rounds = false;
      rst_rounds_in->get(rst_rounds);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool sampler_valid = false;
      sampler_valid_in->get(sampler_valid);

      bool accumulate = false;
      accumulate_in->get(accumulate);

      bool masking_en = false;
      masking_en_in->get(masking_en);

      bool mlkem = false;
      mlkem_in->get(mlkem); //added mlkem input

      sc_uint<6> random;
      random_in->get(random);

      sc_uint<3> ntt_mode;
      ntt_mode_in->get(ntt_mode);

      PwoMemAddrs base_addrs;
      pwo_mem_base_addr_in->get(base_addrs);

      bool incr_pw_rd_addr = sampler_valid
          && (read_state == PwoReadStatesType::PwoReadExec || read_state == PwoReadStatesType::PwoReadExecWait);

      bool latch_index_rand_offset = incr_pw_rd_addr
          && ((read_state == PwoReadStatesType::PwoReadStage && write_state == PwoWriteStatesType::PwoWriteStage
              && rounds_count != 1)
            || index_count == 0x3);

      rounds_count = rst_rounds
          ? sc_uint<3>(0)
          : ((incr_rounds && rounds_count < 1)
            ? sc_uint<3>(rounds_count + 1)
            : (rounds_count == 1 ? sc_uint<3>(0) : rounds_count));
      done_out->set(rounds_count == 1);

      wr_valid_count = (write_state == PwoWriteStatesType::PwoWriteIdle
            || write_state == PwoWriteStatesType::PwoWriteStage)
          ? sc_uint<7>(0)
          : (butterfly_ready ? sc_uint<7>(wr_valid_count + 1) : wr_valid_count);

      pw_wren_reg_dummy = pw_wren_reg_dummy && pw_wren_reg;
      pw_wren_reg = (write_state == PwoWriteStatesType::PwoWriteMem && butterfly_ready)
          || (write_state == PwoWriteStatesType::PwoWriteWait && butterfly_ready && !shuffle_en);

      chunk_count = latch_chunk_rand_offset
          ? random.range(5, 2)
          : ((incr_pw_rd_addr && index_count == 0x3) ? sc_uint<4>(chunk_count + 1) : chunk_count);

      index_rand_offset = latch_index_rand_offset ? random.range(1, 0) : index_rand_offset;

      index_count = incr_pw_rd_addr ? sc_uint<2>(index_count + 1) : index_count;

      bool incr_pw_wr_addr = (write_state == PwoWriteStatesType::PwoWriteMem && butterfly_ready)
          || (write_state == PwoWriteStatesType::PwoWriteWait && (shuffle_en || butterfly_ready));

      sc_uint<15> masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate = getMaskedShuffledPwmMemWrAddrCnxtAccumulate(
        base_addrs.pw_base_addr_c,
        chunk_count_reg,
        masked_pwm_buf_rdptr_d3);

        sc_uint<15> mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate = getMlkemMaskedShuffledPwmMemWrAddrCnxtAccumulate(
        base_addrs.pw_base_addr_c,
        chunk_count_reg,
        masked_pwm_buf_rdptr_d3);

      sc_uint<15> masked_shuffled_pw_mem_wr_addr_c_nxt = getMaskedShuffledPwmMemWrAddrCnxt(base_addrs.pw_base_addr_c,
        chunk_count_reg,
        masked_pwm_buf_rdptr_d2);

        sc_uint<15> mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt = getMlkemMaskedShuffledPwmMemWrAddrCnxt(base_addrs.pw_base_addr_c,
        chunk_count_reg,
        masked_pwm_buf_rdptr_d3); //d2 or d3?

      bool pwm_mode = (ntt_mode == PWM_MODE);
      bool pwa_mode = (ntt_mode == PWA_MODE);
      bool pws_mode = (ntt_mode == PWS_MODE);
      bool pairwm_mode = mlkem && (ntt_mode == PAIRWM_MODE);

      sc_uint<15> shuffled_pw_mem_wr_addr_c_nxt = getShuffledPwMemWrAddrCnxt(pwm_mode, pwa_mode, pws_mode,
        pairwm_mode,
        accumulate,
        base_addrs.pw_base_addr_c,
        chunk_count_reg,
        buf_rdptr_reg);

      pw_mem_wr_addr_c_reg = getPwAddrCwr(rst_pw_addr,
        incr_pw_wr_addr,
        shuffle_en,
        masking_en,
        accumulate,
        mlkem, //added mlkem input
        chunk_rand_offset,
        base_addrs.pw_base_addr_c,
        masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate,
        mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt_accumulate,
        masked_shuffled_pw_mem_wr_addr_c_nxt,
        mlkem_masked_shuffled_pw_mem_wr_addr_c_nxt,
        shuffled_pw_mem_wr_addr_c_nxt,
        pw_mem_wr_addr_c_reg);
      pw_mem_wr_addr_c_out->set(pw_mem_wr_addr_c_reg);

      chunk_rand_offset = latch_chunk_rand_offset ? random.range(5, 2) : chunk_rand_offset;

      bool masked_pwm_exec_in_progress = masking_en && (pwm_mode || pairwm_mode) //line 795, added pairwm_mode case
          && ((read_state != PwoReadStatesType::PwoReadIdle && read_state != PwoReadStatesType::PwoReadStage)
            || (write_state != PwoWriteStatesType::PwoWriteIdle && write_state != PwoWriteStatesType::PwoWriteStage));

      masked_pwm_buf_rdptr_d3 = (((pwm_mode || pairwm_mode) && masking_en && masked_pwm_exec_in_progress) //line 713-715 added pairwm_mode case
        ? masked_pwm_buf_rdptr_d2
        : sc_uint<2>(0));
      masked_pwm_buf_rdptr_d2 = (((pwm_mode || pairwm_mode) && masking_en && masked_pwm_exec_in_progress)
        ? masked_pwm_buf_rdptr_d1
        : sc_uint<2>(0));
      masked_pwm_buf_rdptr_d1 = (((pwm_mode || pairwm_mode) && masking_en && masked_pwm_exec_in_progress)
        ? sc_uint<2>(buf_rdptr_reg.range(1, 0))
        : sc_uint<2>(0));

      write_state = next_state;
    }
  }

  [[noreturn]] void commons() {
    masking_en_ctrl_out->set(false);
    buf_wren_out->set(false);
    buf_rden_out->set(false);
    buf_wrptr_out->set(sc_uint<2>(0));
    buf_rdptr_out->set(sc_uint<2>(0));
    mem_rd_en_out->set(false);
    mem_wr_en_out->set(false);
    buf_wr_rst_count_out->set(true);
    buf_rd_rst_count_out->set(true);

    while (true) {
      insert_state();

      bool buf0_valid = false;
      buf0_valid_in->get(buf0_valid);

      buf_count = ((buf0_valid || (buf_count > 0 && buf_count < 3)) ? sc_uint<2>(buf_count + 1) : sc_uint<2>(0));
      buf_rdptr_out->set(buf_count);

      sc_uint<3> ntt_mode;
      ntt_mode_in->get(ntt_mode);
      opcode_out->set(ntt_mode);
    }
  }
};

#endif
