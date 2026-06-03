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

#ifndef NTT_CTRL_PWM_INTT_H
#define NTT_CTRL_PWM_INTT_H

#include <array>
#include "Interfaces.h"

// #define INTT_WRBUF_LATENCY 13
#define INTT_WRBUF_LATENCY 3
// #define MASKED_INTT_WRBUF_LATENCY 485
#define MASKED_INTT_WRBUF_LATENCY 22
// #define MASKED_PWM_LATENCY 211
#define MASKED_PWM_LATENCY 5
// #define BUF_WRPTR_REG_SIZE 970
#define BUF_WRPTR_REG_SIZE 44
// #define UNMASKED_BF_LATENCY 10
#define UNMASKED_BF_LATENCY 8
// #define CHUNK_COUNT_REG_SIZE 1932
#define CHUNK_COUNT_REG_SIZE 80
#define MEM_LAST_ADDR 63
#define PWO_READ_ADDR_STEP 1


enum class PwmInttReadStatesType {
  PwmInttReadIdle,
  PwmInttReadStage,
  PwmInttReadExec
};


enum class PwmInttWriteStatesType {
  PwmInttWriteIdle,
  PwmInttWriteStage,
  PwmInttWriteBuf,
  PwmInttWriteMem,
  PwmInttWriteWait
};


struct NttMemBaseAddrs {
  sc_uint<15> src_base_addr;
  sc_uint<15> interim_base_addr;
  sc_uint<15> dest_base_addr;
};


struct NttPwBaseAddrs {
  sc_uint<15> pw_base_addr_a;
  sc_uint<15> pw_base_addr_b;
  sc_uint<15> pw_base_addr_c;
};


sc_uint<15> getMemRdBaseAddr(sc_uint<3> rounds_count, NttMemBaseAddrs ntt_mem_base_addrs) {
  if (rounds_count == 0) {
    return sc_uint<15>(0);
  }

  if ((rounds_count & 1) != 0) {
    return ntt_mem_base_addrs.interim_base_addr;
  }

  return ntt_mem_base_addrs.dest_base_addr;
}

sc_uint<16> getShuffledMemRdAddrNxt(sc_uint<4> chunk_count, sc_uint<15> rd_addr_step, sc_uint<2> mem_rd_index_ofst,
  sc_uint<15> mem_rd_base_addr) {
  return 4 * chunk_count + rd_addr_step * mem_rd_index_ofst + mem_rd_base_addr;
}

sc_uint<16> getUnshuffledMemRdAddrNxt(sc_uint<15> mem_rd_addr, sc_uint<15> rd_addr_step) {
  return mem_rd_addr + rd_addr_step;
}

sc_uint<16> getMemRdAddrNxt(bool shuffle_en, sc_uint<3> rounds_count, sc_uint<16> shuffled_nxt,
  sc_uint<16> unshuffled_nxt) {
  if (shuffle_en && rounds_count > 0) {
    return shuffled_nxt;
  }

  return unshuffled_nxt;
}

sc_uint<15> getPwMemRdAddrNxt(sc_uint<15> base_addr, sc_uint<4> chunk_count, sc_uint<15> rd_addr_step,
  sc_uint<2> mem_rd_index_ofst) {
  return base_addr + 4 * chunk_count + rd_addr_step * mem_rd_index_ofst;
}

sc_uint<15> getPwMemRdRstAddr(bool shuffle_en, sc_uint<4> chunk_rand_offset, sc_uint<15> base_addr) {
  if (shuffle_en) {
    return 4 * chunk_rand_offset + base_addr;
  }

  return base_addr;
}

sc_uint<15> getPwMemRdIncrAddrAb(bool shuffle_en, sc_uint<15> addr_nxt, sc_uint<15> default_addr,
  sc_uint<15> addr_step) {
  if (shuffle_en) {
    return addr_nxt;
  }

  return default_addr + addr_step;
}

sc_uint<15> getPwMemRdAddrAb(bool rst_pw_addr, bool incr_pw_addr, sc_uint<15> rst_addr, sc_uint<15> incr_addr,
  sc_uint<15> default_addr) {
  if (rst_pw_addr) {
    return rst_addr;
  }

  if (incr_pw_addr) {
    return incr_addr;
  }

  return default_addr;
}

sc_uint<15> getPwMemRdShuffledIncrAddrC(bool accumulate, sc_uint<15> addr_nxt) {
  if (accumulate) {
    return addr_nxt;
  }

  return sc_uint<15>(0);
}

sc_uint<15> getPwMemRdUnshuffledIncrAddrC(bool accumulate, sc_uint<15> default_addr, sc_uint<15> addr_step) {
  if (accumulate) {
    return default_addr + addr_step;
  }

  return sc_uint<15>(0);
}

sc_uint<15> getPwMemRdAddrC(bool rst_pw_addr, bool incr_pw_addr, bool shuffle_en, sc_uint<15> rst_addr,
  sc_uint<15> incr_shuffled_addr, sc_uint<15> incr_unshuffled_addr, sc_uint<15> default_addr) {
  if (rst_pw_addr) {
    return rst_addr;
  }

  if (incr_pw_addr) {
    if (shuffle_en) {
      return incr_shuffled_addr;
    }

    return incr_unshuffled_addr;
  }

  return default_addr;
}

std::array<sc_uint<7>, 8> getTwiddleRandOffsets(sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg,
  sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg) {
  int chunk_count_reg_idx_0 = 4 * (MASKED_INTT_WRBUF_LATENCY - MASKED_PWM_LATENCY - 3);
  int buf_wrptr_reg_idx_0 = 2 * (MASKED_INTT_WRBUF_LATENCY - MASKED_PWM_LATENCY - 1);
  int chunk_count_reg_idx_1 = 4 * UNMASKED_BF_LATENCY;
  int buf_wrptr_reg_idx_1 = 2 * (INTT_WRBUF_LATENCY - 1);
  int buf_wrptr_reg_idx_2 = 2 * (INTT_WRBUF_LATENCY - 1);

  return std::array<sc_uint<7>, 8>{
    4 * chunk_count_reg.range(chunk_count_reg_idx_0 + 3, chunk_count_reg_idx_0)
    + buf_wrptr_reg.range(buf_wrptr_reg_idx_0 + 1, buf_wrptr_reg_idx_0),
    (chunk_count_reg.range(chunk_count_reg_idx_1 + 3, chunk_count_reg_idx_1) & 0x3) * 4
    + buf_wrptr_reg.range(buf_wrptr_reg_idx_1 + 1, buf_wrptr_reg_idx_1),
    sc_uint<7>(buf_wrptr_reg.range(buf_wrptr_reg_idx_2 + 1, buf_wrptr_reg_idx_2)),
    0,
    0,
    0,
    0,
    0
  };
}

sc_uint<7> getTwiddleIncrAddr(bool shuffle_en, sc_uint<3> rounds_count, std::array<sc_uint<7>, 8> rand_offsets,
  std::array<sc_uint<7>, 8> end_addrs, sc_uint<7> default_addr) {
  if (shuffle_en) {
    return rand_offsets[rounds_count];
  }

  if (default_addr == end_addrs[rounds_count]) {
    return sc_uint<7>(0);
  }

  return default_addr + 1;
}

sc_uint<7> getTwiddleAddrReg(bool incr, bool rst, sc_uint<7> incr_addr, sc_uint<7> default_addr) {
  if (incr) {
    return incr_addr;
  }

  if (rst) {
    return sc_uint<7>(0);
  }

  return default_addr;
}

sc_uint<7> getRdValidCount(PwmInttReadStatesType read_state, sc_uint<3> rounds_count, bool sampler_valid,
  sc_uint<7> rd_valid_count) {
  bool rst_rd_valid_count = read_state == PwmInttReadStatesType::PwmInttReadIdle
      || read_state == PwmInttReadStatesType::PwmInttReadStage;
  bool rd_data_valid = rounds_count > 0 ? read_state == PwmInttReadStatesType::PwmInttReadExec : sampler_valid;

  return (rst_rd_valid_count
    ? sc_uint<7>(0)
    : (rd_data_valid ? sc_uint<7>(rd_valid_count + 1) : rd_valid_count));
}

sc_uint<2> getIndexCount(PwmInttReadStatesType read_state, sc_uint<3> rounds_count, bool sampler_valid,
  sc_uint<2> index_count) {
  if (read_state == PwmInttReadStatesType::PwmInttReadExec && (rounds_count > 0 || sampler_valid)) {
    return index_count + 1;
  }

  return index_count;
}

sc_biguint<CHUNK_COUNT_REG_SIZE> concatChunkCountReg2(sc_biguint<CHUNK_COUNT_REG_SIZE> op_0, int offset_0,
  sc_biguint<CHUNK_COUNT_REG_SIZE> op_1) {
  sc_biguint<CHUNK_COUNT_REG_SIZE> result = 0;

  result = op_0 << offset_0;
  result |= op_1;

  return result;
}

sc_biguint<CHUNK_COUNT_REG_SIZE> getChunkCountReg(PwmInttReadStatesType read_state, bool butterfly_ready,
  sc_uint<3> rounds_count, sc_uint<4> chunk_count, sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg) {
  if (rounds_count == 0) {
    return concatChunkCountReg2(sc_biguint<CHUNK_COUNT_REG_SIZE>(chunk_count),
      CHUNK_COUNT_REG_SIZE - 4,
      chunk_count_reg.range(CHUNK_COUNT_REG_SIZE - 1, 4));
  }

  if (butterfly_ready || (rounds_count > 0 && read_state == PwmInttReadStatesType::PwmInttReadExec)) {
    return concatChunkCountReg2(sc_biguint<CHUNK_COUNT_REG_SIZE>(chunk_count),
      (4 * UNMASKED_BF_LATENCY),
      chunk_count_reg.range((4 * UNMASKED_BF_LATENCY) + 3, 4));
  }

  return chunk_count_reg;
}

sc_biguint<BUF_WRPTR_REG_SIZE> concatBufWrptrReg2(sc_biguint<BUF_WRPTR_REG_SIZE> op_0, int offset_0,
  sc_biguint<BUF_WRPTR_REG_SIZE> op_1) {
  sc_biguint<BUF_WRPTR_REG_SIZE> result = 0;

  result = op_0 << offset_0;
  result |= op_1;

  return result;
}

sc_biguint<BUF_WRPTR_REG_SIZE> getBufWrptrReg(PwmInttReadStatesType read_state, bool butterfly_ready,
  sc_uint<3> rounds_count, sc_uint<2> mem_rd_index_ofst, sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg) {
  if (rounds_count > 0 && (read_state == PwmInttReadStatesType::PwmInttReadExec || butterfly_ready)) {
    return concatBufWrptrReg2(sc_biguint<BUF_WRPTR_REG_SIZE>(mem_rd_index_ofst),
      (2 * INTT_WRBUF_LATENCY) - 2,
      buf_wrptr_reg.range((2 * INTT_WRBUF_LATENCY) - 1, 2));
  }

  if (rounds_count == 0) {
    return concatBufWrptrReg2(sc_biguint<BUF_WRPTR_REG_SIZE>(mem_rd_index_ofst),
      BUF_WRPTR_REG_SIZE - 2,
      buf_wrptr_reg.range(BUF_WRPTR_REG_SIZE - 1, 2));
  }

  return sc_biguint<BUF_WRPTR_REG_SIZE>(0);
}

sc_uint<2> getMemRdIndexOfst(sc_uint<2> index_count, sc_uint<2> index_rand_offset) {
  return index_count + index_rand_offset;
}

sc_uint<15> wraparoundMemAddr(sc_uint<16> new_addr, sc_uint<15> base_addr) {
  if (new_addr > (sc_uint<16>(base_addr) + MEM_LAST_ADDR)) {
    return new_addr - MEM_LAST_ADDR;
  }

  return new_addr;
}

sc_uint<2> getBufWrptr(bool shuffle_en, bool buf_wren_intt, sc_uint<2> buf_wrptr,
  sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg) {
  if (buf_wren_intt) {
    if (shuffle_en) {
      return sc_uint<2>(buf_wrptr_reg.range(1, 0));
    }

    return buf_wrptr + 1;
  }

  return buf_wrptr;
}

sc_uint<15> getMemWrAddr(bool rst_wr_addr, bool incr_mem_wr_addr, bool shuffle_en, NttMemBaseAddrs ntt_mem_base_addrs,
  sc_uint<4> rounds_count, sc_uint<4> chunk_rand_offset, sc_uint<15> mem_wr_addr, sc_uint<15> wr_addr_step) {
  sc_uint<15> mem_wr_base_addr = ((rounds_count & 1) == 1
    ? ntt_mem_base_addrs.dest_base_addr
    : ntt_mem_base_addrs.interim_base_addr);

  bool last_wr_addr = mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR);

  sc_uint<16> mem_wr_addr_nxt = mem_wr_addr + wr_addr_step;

  if (rst_wr_addr) {
    if (shuffle_en) {
      return mem_wr_base_addr + chunk_rand_offset;
    }

    return mem_wr_base_addr;
  }

  if (incr_mem_wr_addr) {
    if (shuffle_en && last_wr_addr) {
      return mem_wr_base_addr;
    }

    return wraparoundMemAddr(mem_wr_addr_nxt, mem_wr_base_addr);
  }

  return mem_wr_addr;
}

sc_uint<3> getRoundsCount(bool rst_rounds, bool incr_rounds, sc_uint<3> rounds_count) {
  if (rst_rounds) {
    return sc_uint<3>(0);
  }

  if (incr_rounds) {
    return rounds_count + 1;
  }

  if (rounds_count == 4) {
    return sc_uint<3>(0);
  }

  return rounds_count;
}

SC_MODULE(ntt_ctrl_pwm_intt) {
public:
  SC_CTOR(ntt_ctrl_pwm_intt) {
    SC_THREAD(read)
    SC_THREAD(write)
    SC_THREAD(common)
  }

  shared_in<bool> ntt_enable_in;
  shared_in<bool> butterfly_ready_in;
  shared_in<bool> buf0_valid_in;
  shared_in<bool> sampler_valid_in;
  shared_in<bool> accumulate_in;
  shared_in<NttMemBaseAddrs> ntt_mem_base_addr_in;
  shared_in<NttPwBaseAddrs> pwo_mem_base_addr_in;
  shared_in<bool> shuffle_en_in;
  shared_in<sc_uint<6>> random_in;

  shared_in<bool> rst_rounds_in;

  // Write a custom property, as 'bf_enable' combinationally depends on 'shuffle_en'
  // shared_out<bool> bf_enable_out;
  shared_out<sc_uint<3>> opcode_out;
  shared_out<bool> masking_en_ctrl_out;
  // Write a custom property, as 'buf_wren' combinationally depends on 'shuffle_en'
  // shared_out<bool> buf_wren_out;
  // Write a custom property, as 'buf_rden' combinationally depends on 'buf0_valid'
  // shared_out<bool> buf_rden_out;
  shared_out<sc_uint<2>> buf_wrptr_out;
  shared_out<sc_uint<2>> buf_rdptr_out;
  // Write a custom property, as 'twiddle_addr' combinationally depends on 'shuffle_en'
  // shared_out<sc_uint<7>> twiddle_addr_out;
  shared_out<sc_uint<15>> mem_rd_addr_out;
  shared_out<sc_uint<15>> mem_wr_addr_out;
  // Combinationally depends on 'shuffle_en'
  // shared_out<bool> mem_rd_en_out;
  // Combinationally depends on 'buf0_valid'
  // shared_out<bool> mem_wr_en_out;
  // Combinationally depends on both states
  // shared_out<bool> buf_wr_rst_count;
  // Combinationally depends on both states
  // shared_out<bool> buf_rd_rst_count;
  shared_out<sc_uint<15>> pw_mem_rd_addr_a_out;
  shared_out<sc_uint<15>> pw_mem_rd_addr_b_out;
  shared_out<sc_uint<15>> pw_mem_rd_addr_c_out;
  shared_out<bool> pw_wren_out;
  shared_out<bool> done_out;


private:
  PwmInttReadStatesType read_state;
  PwmInttWriteStatesType write_state;

  sc_uint<3> rounds_count;
  sc_uint<7> rd_valid_count;
  sc_uint<7> wr_valid_count;
  sc_uint<2> buf_count;
  sc_uint<2> index_count;
  sc_uint<4> chunk_count;
  sc_uint<4> chunk_rand_offset;

  sc_uint<2> index_rand_offset;
  sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg;
  sc_uint<2> buf_wrptr;
  sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg;
  sc_uint<7> twiddle_addr_reg;
  sc_uint<7> twiddle_addr_reg_d2;
  sc_uint<7> twiddle_addr_reg_d3;
  sc_uint<7> twiddle_addr_reg_d3_dummy;
  sc_uint<15> mem_rd_addr;
  sc_uint<15> mem_wr_addr;
  sc_uint<15> pw_mem_rd_addr_a_reg;
  sc_uint<15> pw_mem_rd_addr_b_reg;
  sc_uint<15> pw_mem_rd_addr_c_reg;

  bool bf_enable_reg;
  bool bf_enable_reg_d2;
  bool bf_enable_reg_d2_dummy;
  bool buf_wren_intt_reg;
  bool buf_wren_intt_reg_dummy;
  bool incr_twiddle_addr_reg;
  bool mem_rd_en_reg;
  bool mem_rd_en_reg_dummy;
  bool pw_rden_reg;
  bool pw_rden_reg_dummy;
  bool pw_wren_reg;
  bool pw_wren_reg_dummy;

  [[noreturn]] void read() {
    read_state = PwmInttReadStatesType::PwmInttReadIdle;

    while (true) {
      PwmInttReadStatesType next_state = PwmInttReadStatesType::PwmInttReadIdle;
      bool rst_rd_addr = false;
      bool incr_mem_rd_addr = false;
      sc_uint<15> rd_addr_step = 0;

      if (read_state == PwmInttReadStatesType::PwmInttReadIdle) {
        insert_state("read_idle");
        next_state = PwmInttReadStatesType::PwmInttReadIdle;
        rst_rd_addr = true;
        incr_mem_rd_addr = false;
        rd_addr_step = 0;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = PwmInttReadStatesType::PwmInttReadStage;
        }
      } else if (read_state == PwmInttReadStatesType::PwmInttReadStage) {
        insert_state("read_stage");
        next_state = PwmInttReadStatesType::PwmInttReadStage;
        rst_rd_addr = true;
        incr_mem_rd_addr = false;
        rd_addr_step = 0;

        if (rounds_count == 4) {
          next_state = PwmInttReadStatesType::PwmInttReadIdle;
        } else if (write_state == PwmInttWriteStatesType::PwmInttWriteStage) {
          next_state = PwmInttReadStatesType::PwmInttReadExec;
        }
      } else {
        // if (read_state == PwmInttReadStatesType::PwmInttReadExec) {
        insert_state("read_exec");
        next_state = PwmInttReadStatesType::PwmInttReadExec;
        rst_rd_addr = false;
        incr_mem_rd_addr = rounds_count != 0;
        rd_addr_step = 1;

        bool sampler_valid = false;
        sampler_valid_in->get(sampler_valid);

        if (rd_valid_count >= 0x3F) {
          next_state = PwmInttReadStatesType::PwmInttReadStage;
        }
      }

      bool sampler_valid = false;
      sampler_valid_in->get(sampler_valid);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      bool accumulate = false;
      accumulate_in->get(accumulate);

      sc_uint<6> random;
      random_in->get(random);

      NttMemBaseAddrs mem_base_addrs;
      ntt_mem_base_addr_in->get(mem_base_addrs);

      NttPwBaseAddrs pw_base_addrs;
      pwo_mem_base_addr_in->get(pw_base_addrs);

      std::array<sc_uint<7>, 8> twiddle_rand_offset_array = getTwiddleRandOffsets(chunk_count_reg, buf_wrptr_reg);

      std::array<sc_uint<7>, 8> twiddle_end_addr_array = {
        63, 15, 3, 0, 0, 0, 0, 0
      };

      std::array<sc_uint<7>, 8> twiddle_offset_array = {
        0, 64, 80, 84, 0, 0, 0, 0
      };

      twiddle_addr_reg_d3_dummy = twiddle_addr_reg_d3_dummy + twiddle_addr_reg_d3;
      twiddle_addr_reg_d3 = twiddle_addr_reg_d2;
      twiddle_addr_reg_d2 = shuffle_en
          ? (twiddle_rand_offset_array[rounds_count] + twiddle_offset_array[rounds_count])
          : (twiddle_addr_reg + twiddle_offset_array[rounds_count]);

      twiddle_addr_reg = getTwiddleAddrReg(incr_twiddle_addr_reg,
        read_state == PwmInttReadStatesType::PwmInttReadIdle
        || (read_state == PwmInttReadStatesType::PwmInttReadStage && !butterfly_ready),
        getTwiddleIncrAddr(shuffle_en,
          rounds_count,
          twiddle_rand_offset_array,
          twiddle_end_addr_array,
          twiddle_addr_reg),
        twiddle_addr_reg);

      incr_twiddle_addr_reg = read_state == PwmInttReadStatesType::PwmInttReadExec;

      chunk_count_reg = getChunkCountReg(read_state, butterfly_ready, rounds_count, chunk_count, chunk_count_reg);

      sc_uint<15> pw_base_addr_a = (rounds_count == 0 ? pw_base_addrs.pw_base_addr_a : sc_uint<15>(0));
      sc_uint<15> pw_base_addr_b = (rounds_count == 0 ? pw_base_addrs.pw_base_addr_b : sc_uint<15>(0));
      sc_uint<15> pw_base_addr_c = 0;

      sc_uint<2> mem_rd_index_ofst = getMemRdIndexOfst(index_count, index_rand_offset);

      sc_uint<15> pw_mem_rd_addr_a_nxt = getPwMemRdAddrNxt(pw_base_addr_a,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);
      sc_uint<15> pw_mem_rd_addr_b_nxt = getPwMemRdAddrNxt(pw_base_addr_b,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);
      sc_uint<15> pw_mem_rd_addr_c_nxt = getPwMemRdAddrNxt(pw_base_addr_c,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      bool rst_pw_addr = write_state == PwmInttWriteStatesType::PwmInttWriteIdle;

      bool incr_pw_rd_addr = read_state == PwmInttReadStatesType::PwmInttReadExec && rounds_count == 0 && sampler_valid;

      pw_mem_rd_addr_a_reg = getPwMemRdAddrAb(rst_pw_addr,
        incr_pw_rd_addr,
        getPwMemRdRstAddr(shuffle_en, chunk_rand_offset, pw_base_addr_a),
        getPwMemRdIncrAddrAb(shuffle_en, pw_mem_rd_addr_a_nxt, pw_mem_rd_addr_a_reg, PWO_READ_ADDR_STEP),
        pw_mem_rd_addr_a_reg);
      pw_mem_rd_addr_a_out->set(pw_mem_rd_addr_a_reg);

      pw_mem_rd_addr_b_reg = getPwMemRdAddrAb(rst_pw_addr,
        incr_pw_rd_addr,
        getPwMemRdRstAddr(shuffle_en, chunk_rand_offset, pw_base_addr_b),
        getPwMemRdIncrAddrAb(shuffle_en, pw_mem_rd_addr_b_nxt, pw_mem_rd_addr_b_reg, PWO_READ_ADDR_STEP),
        pw_mem_rd_addr_b_reg);
      pw_mem_rd_addr_b_out->set(pw_mem_rd_addr_b_reg);

      pw_mem_rd_addr_c_reg = getPwMemRdAddrC(rst_pw_addr,
        incr_pw_rd_addr,
        shuffle_en,
        getPwMemRdRstAddr(shuffle_en, chunk_rand_offset, pw_base_addr_c),
        getPwMemRdShuffledIncrAddrC(accumulate, pw_mem_rd_addr_c_nxt),
        getPwMemRdUnshuffledIncrAddrC(accumulate, pw_mem_rd_addr_c_reg, PWO_READ_ADDR_STEP),
        pw_mem_rd_addr_c_reg);
      pw_mem_rd_addr_c_out->set(pw_mem_rd_addr_c_reg);

      sc_uint<15> mem_rd_base_addr = getMemRdBaseAddr(rounds_count, mem_base_addrs);

      mem_rd_en_reg_dummy = mem_rd_en_reg_dummy && mem_rd_en_reg;
      mem_rd_en_reg = read_state == PwmInttReadStatesType::PwmInttReadExec
          && rounds_count > 0 && mem_rd_addr <= (mem_rd_base_addr + MEM_LAST_ADDR);

      sc_uint<16> mem_rd_addr_nxt = getMemRdAddrNxt(shuffle_en,
        rounds_count,
        getShuffledMemRdAddrNxt(chunk_count, rd_addr_step, mem_rd_index_ofst, mem_rd_base_addr),
        getUnshuffledMemRdAddrNxt(mem_rd_addr, rd_addr_step));

      mem_rd_addr = rst_rd_addr
          ? ((shuffle_en && rounds_count > 0)
            ? sc_uint<15>(mem_rd_base_addr + 4 * chunk_rand_offset)
            : mem_rd_base_addr)
          : (incr_mem_rd_addr
            ? wraparoundMemAddr(mem_rd_addr_nxt, mem_rd_base_addr)
            : mem_rd_addr);
      mem_rd_addr_out->set(mem_rd_addr);

      buf_wrptr_reg = getBufWrptrReg(read_state, butterfly_ready, rounds_count, mem_rd_index_ofst, buf_wrptr_reg);

      bf_enable_reg_d2_dummy = bf_enable_reg_d2_dummy && bf_enable_reg_d2;
      bf_enable_reg_d2 = bf_enable_reg;
      bf_enable_reg = read_state == PwmInttReadStatesType::PwmInttReadExec;

      rd_valid_count = getRdValidCount(read_state, rounds_count, sampler_valid, rd_valid_count);

      bool latch_index_rand_offset = (read_state == PwmInttReadStatesType::PwmInttReadStage
        && write_state == PwmInttWriteStatesType::PwmInttWriteStage && rounds_count != 4) || index_count == 3;

      index_rand_offset = latch_index_rand_offset ? random.range(1, 0) : index_rand_offset;

      index_count = getIndexCount(read_state, rounds_count, sampler_valid, index_count);

      pw_rden_reg_dummy = pw_rden_reg_dummy && pw_rden_reg;
      pw_rden_reg = read_state == PwmInttReadStatesType::PwmInttReadExec && rounds_count == 0 && sampler_valid;

      read_state = next_state;
    }
  }

  [[noreturn]] void write() {
    write_state = PwmInttWriteStatesType::PwmInttWriteIdle;

    while (true) {
      PwmInttWriteStatesType next_state = PwmInttWriteStatesType::PwmInttWriteIdle;
      bool rst_wr_addr = false;
      bool incr_mem_wr_addr = false;
      bool buf_wren_intt = false;
      bool latch_chunk_rand_offset = false;
      bool rst_wr_valid_count = false;
      bool incr_rounds_count = false;
      sc_uint<16> wr_addr_step = 0;

      if (write_state == PwmInttWriteStatesType::PwmInttWriteIdle) {
        insert_state("write_idle");
        next_state = PwmInttWriteStatesType::PwmInttWriteIdle;
        rst_wr_addr = true;
        incr_mem_wr_addr = false;
        buf_wren_intt = false;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = true;
        incr_rounds_count = false;
        wr_addr_step = 0;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = PwmInttWriteStatesType::PwmInttWriteStage;
          latch_chunk_rand_offset = true;
        }
      } else if (write_state == PwmInttWriteStatesType::PwmInttWriteStage) {
        insert_state("write_stage");
        rst_wr_addr = true;
        incr_mem_wr_addr = false;
        buf_wren_intt = false;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = true;
        incr_rounds_count = false;
        wr_addr_step = 0;

        if (rounds_count == 4) {
          next_state = PwmInttWriteStatesType::PwmInttWriteIdle;
        } else {
          next_state = PwmInttWriteStatesType::PwmInttWriteBuf;
        }
      } else if (write_state == PwmInttWriteStatesType::PwmInttWriteBuf) {
        insert_state("write_buf");
        next_state = PwmInttWriteStatesType::PwmInttWriteBuf;
        rst_wr_addr = false;
        incr_mem_wr_addr = false;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = false;
        incr_rounds_count = false;
        wr_addr_step = 16;

        butterfly_ready_in->get(buf_wren_intt);

        bool buf0_valid = false;
        buf0_valid_in->get(buf0_valid);

        if (buf0_valid) {
          next_state = PwmInttWriteStatesType::PwmInttWriteMem;
          incr_mem_wr_addr = true;
        }
      } else if (write_state == PwmInttWriteStatesType::PwmInttWriteMem) {
        insert_state("write_mem");
        next_state = PwmInttWriteStatesType::PwmInttWriteMem;
        rst_wr_addr = false;
        incr_mem_wr_addr = true;
        buf_wren_intt = true;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = false;
        incr_rounds_count = false;
        wr_addr_step = 16;

        bool buf0_valid = false;
        buf0_valid_in->get(buf0_valid);

        if (!buf0_valid && wr_valid_count < 0x40 && buf_count == 0) {
          next_state = PwmInttWriteStatesType::PwmInttWriteBuf;
        } else if (buf0_valid && wr_valid_count == 0x3C) {
          next_state = PwmInttWriteStatesType::PwmInttWriteWait;
        }
      } else {
        // if (write_state == PwmInttWriteStatesType::PwmInttWriteWait) {
        insert_state("write_wait");
        next_state = PwmInttWriteStatesType::PwmInttWriteWait;
        rst_wr_addr = false;
        incr_mem_wr_addr = true;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = false;
        incr_rounds_count = false;
        wr_addr_step = 16;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        buf_wren_intt = !shuffle_en;

        if (buf_count == 3) {
          next_state = PwmInttWriteStatesType::PwmInttWriteStage;
          latch_chunk_rand_offset = true;
          incr_rounds_count = rounds_count < 4;
        }
      }

      bool rst_rounds = false;
      rst_rounds_in->get(rst_rounds);

      bool buf0_valid = false;
      buf0_valid_in->get(buf0_valid);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool ntt_enable = false;
      ntt_enable_in->get(ntt_enable);

      sc_uint<6> random;
      random_in->get(random);

      NttMemBaseAddrs mem_base_addrs;
      ntt_mem_base_addr_in->get(mem_base_addrs);
      sc_uint<15> mem_wr_base_addr = ((rounds_count & 1) == 1
        ? mem_base_addrs.dest_base_addr
        : mem_base_addrs.interim_base_addr);

      sc_uint<16> mem_wr_addr_nxt = mem_wr_addr + wr_addr_step;

      mem_wr_addr = getMemWrAddr(rst_wr_addr,
        incr_mem_wr_addr,
        shuffle_en,
        mem_base_addrs,
        rounds_count,
        chunk_rand_offset,
        mem_wr_addr,
        wr_addr_step);

      buf_wrptr = getBufWrptr(shuffle_en, buf_wren_intt, buf_wrptr, buf_wrptr_reg);
      buf_wrptr_out->set(buf_wrptr);

      rounds_count = getRoundsCount(rst_rounds, incr_rounds_count, rounds_count);
      done_out->set(rounds_count == 4);

      wr_valid_count = (rst_wr_valid_count
        ? sc_uint<7>(0)
        : (buf0_valid ? (wr_valid_count > 0x40 ? sc_uint<7>(0) : sc_uint<7>(wr_valid_count + 4)) : wr_valid_count));

      buf_wren_intt_reg_dummy = buf_wren_intt_reg_dummy && buf_wren_intt_reg;
      buf_wren_intt_reg = buf_wren_intt;

      chunk_count = (latch_chunk_rand_offset
        ? random.range(5, 2)
        : (index_count == 3 ? sc_uint<4>(chunk_count + 1) : chunk_count));

      chunk_rand_offset = (latch_chunk_rand_offset ? random.range(5, 2) : chunk_rand_offset);

      pw_wren_reg_dummy = pw_wren_reg_dummy && pw_wren_reg;
      pw_wren_reg = false;

      write_state = next_state;
    }
  }

  [[noreturn]] void common() {
    while (true) {
      insert_state();

      bool buf0_valid = false;
      buf0_valid_in->get(buf0_valid);

      buf_count = ((buf0_valid || (buf_count > 0 && buf_count < 3)) ? sc_uint<2>(buf_count + 1) : sc_uint<2>(0));
      buf_rdptr_out->set(buf_count);

      opcode_out->set(rounds_count == 0 ? 5 : 1);
      masking_en_ctrl_out->set(rounds_count == 0);

      pw_wren_out->set(false);
    }
  }
};

#endif
