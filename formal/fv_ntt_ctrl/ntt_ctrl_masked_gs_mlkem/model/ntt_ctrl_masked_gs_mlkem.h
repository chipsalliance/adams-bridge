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

#ifndef NTT_CTRL_MASKED_GS_H
#define NTT_CTRL_MASKED_GS_H

#include <array>
#include "Interfaces.h"

 #define INTT_WRBUF_LATENCY 13
//#define INTT_WRBUF_LATENCY 3
// MASKED_INTT_WRBUF_LATENCY = MASKED_BF_STAGE1_LATENCY (266)(10) + (UNMASKED_BF_LATENCY (10)(8) / 2) + 3
 #define MASKED_INTT_WRBUF_LATENCY 274
//#define MASKED_INTT_WRBUF_LATENCY 17
// #define MASKED_PWM_LATENCY 211
#define MASKED_PWM_LATENCY 5
// BUF_WRPTR_REG_SIZE = 2 * MASKED_INTT_WRBUF_LATENCY//(274)(17)
//#define BUF_WRPTR_REG_SIZE 34
#define BUF_WRPTR_REG_SIZE 548
#define UNMASKED_BF_LATENCY 10
//#define UNMASKED_BF_LATENCY 8
// CHUNK_COUNT_REG_SIZE = 4 * (MASKED_INTT_WRBUF_LATENCY (274)(17) - 2)
#define CHUNK_COUNT_REG_SIZE 1088
//#define CHUNK_COUNT_REG_SIZE 60
#define MEM_LAST_ADDR 63
#define PWO_READ_ADDR_STEP 1

//MLKEM parameters
#define MLKEM_INTT_WRBUF_LATENCY 9
#define MLKEM_MASKED_INTT_WRBUF_LATENCY 20


enum class MaskedGsReadStatesType {
  MaskedGsReadIdle,
  MaskedGsReadStage,
  MaskedGsReadExec
};


enum class MaskedGsWriteStatesType {
  MaskedGsWriteIdle,
  MaskedGsWriteStage,
  MaskedGsWriteBuf,
  MaskedGsWriteMem,
  MaskedGsWriteWait
};


struct NttMemBaseAddrs {
  sc_uint<15> src_base_addr;
  sc_uint<15> interim_base_addr;
  sc_uint<15> dest_base_addr;
};


sc_uint<15> getMemRdBaseAddr(sc_uint<3> rounds_count, NttMemBaseAddrs ntt_mem_base_addrs) { //line 337, no change
  if (rounds_count == 0) {
    return ntt_mem_base_addrs.src_base_addr;
  }

  if ((rounds_count & 1) != 0) {
    return ntt_mem_base_addrs.interim_base_addr;
  }

  return ntt_mem_base_addrs.dest_base_addr;
}

sc_uint<16> getShuffledMemRdAddrNxt(sc_uint<4> chunk_count, sc_uint<15> rd_addr_step, sc_uint<2> mem_rd_index_ofst, //line 341 no change
  sc_uint<15> mem_rd_base_addr) {
  return 4 * chunk_count + rd_addr_step * mem_rd_index_ofst + mem_rd_base_addr;
}

sc_uint<16> getUnshuffledMemRdAddrNxt(sc_uint<15> mem_rd_addr, sc_uint<15> rd_addr_step) { //line 345 no change
  return mem_rd_addr + rd_addr_step;
}

sc_uint<16> getMemRdAddrNxt(bool shuffle_en, sc_uint<3> rounds_count, sc_uint<16> shuffled_nxt,
  sc_uint<16> unshuffled_nxt) {
  if (shuffle_en) {
    return shuffled_nxt;
  }

  return unshuffled_nxt;
}

std::array<sc_uint<7>, 8> getTwiddleRandOffsets(bool masking_en_ctrl, sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg, //line 516 no change for gs but added design for pairwm_mode, should be added here or in pairwm_mode model?
  sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg) {
  int chunk_count_reg_idx_0 = 4 * (MASKED_INTT_WRBUF_LATENCY - 3);
  int buf_wrptr_reg_idx_0 = 2 * (MASKED_INTT_WRBUF_LATENCY - 1);
  int chunk_count_reg_idx_1 = 4 * UNMASKED_BF_LATENCY;
  int buf_wrptr_reg_idx_1 = 2 * (INTT_WRBUF_LATENCY - 1);
  int buf_wrptr_reg_idx_2 = 2 * (INTT_WRBUF_LATENCY - 1);

  return std::array<sc_uint<7>, 8>{
    (masking_en_ctrl
      ? (4 * chunk_count_reg.range(chunk_count_reg_idx_0 + 3, chunk_count_reg_idx_0)  + buf_wrptr_reg.range(buf_wrptr_reg_idx_0 + 1, buf_wrptr_reg_idx_0))
      : (4 * chunk_count_reg.range(chunk_count_reg_idx_1 + 3, chunk_count_reg_idx_1)  + buf_wrptr_reg.range(buf_wrptr_reg_idx_1 + 1, buf_wrptr_reg_idx_1))),
    ((chunk_count_reg.range(chunk_count_reg_idx_1 + 3, chunk_count_reg_idx_1) & 0x3) * 4  + buf_wrptr_reg.range(buf_wrptr_reg_idx_1 + 1, buf_wrptr_reg_idx_1)),
    sc_uint<7>(buf_wrptr_reg.range(buf_wrptr_reg_idx_2 + 1, buf_wrptr_reg_idx_2)),
    0,
    0,
    0,
    0,
    0
  };
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

sc_uint<7> getTwiddleAddrReg(bool incr, bool rst, sc_uint<7> incr_addr, sc_uint<7> default_addr) { //no change, line 570-573
  if (incr) {
    return incr_addr;
  }

  if (rst) {
    return sc_uint<7>(0);
  }

  return default_addr;
}

sc_uint<7> getRdValidCount(MaskedGsReadStatesType read_state, sc_uint<3> rounds_count, bool sampler_valid, //line 603-612, no change
  sc_uint<7> rd_valid_count) {
  bool rst_rd_valid_count = read_state == MaskedGsReadStatesType::MaskedGsReadIdle
      || read_state == MaskedGsReadStatesType::MaskedGsReadStage;
  bool rd_data_valid = read_state == MaskedGsReadStatesType::MaskedGsReadExec;

  return (rst_rd_valid_count
    ? sc_uint<7>(0)
    : (rd_data_valid ? sc_uint<7>(rd_valid_count + 1) : rd_valid_count));
}

sc_uint<2> getIndexCount(bool incr_mem_rd_addr, sc_uint<2> index_count) { //line 738-747 no change
  if (incr_mem_rd_addr) {
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

sc_biguint<CHUNK_COUNT_REG_SIZE> getChunkCountReg(bool masking_en_ctrl, bool butterfly_ready, bool incr_mem_rd_addr, //line 750-766 no change for gs, pairwm_case already added in pairwm esl model
  sc_uint<4> chunk_count, sc_biguint<CHUNK_COUNT_REG_SIZE> chunk_count_reg) {
  if (masking_en_ctrl) {
    return concatChunkCountReg2(sc_biguint<CHUNK_COUNT_REG_SIZE>(chunk_count),
      CHUNK_COUNT_REG_SIZE - 4,
      chunk_count_reg.range(CHUNK_COUNT_REG_SIZE - 1, 4));
  }

  if (butterfly_ready || incr_mem_rd_addr) {
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

sc_biguint<BUF_WRPTR_REG_SIZE> getBufWrptrReg(bool incr_mem_rd_addr, bool butterfly_ready, bool masking_en_ctrl, //line 688, no change
  sc_uint<2> mem_rd_index_ofst, sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg) {
  // something <= { x, something[i:j] };
  // --> something = (x << (m * (i - j + 1))) | something.range(m * i + m - 1, m * j);
  if ((incr_mem_rd_addr || butterfly_ready) && !masking_en_ctrl) {
    return concatBufWrptrReg2(sc_biguint<BUF_WRPTR_REG_SIZE>(mem_rd_index_ofst),
      2 * (INTT_WRBUF_LATENCY - 1),
      buf_wrptr_reg.range(2 * (INTT_WRBUF_LATENCY - 1) + 1, 2));
  }

  if (incr_mem_rd_addr || masking_en_ctrl) {
    return concatBufWrptrReg2(sc_biguint<BUF_WRPTR_REG_SIZE>(mem_rd_index_ofst),
      2 * (MASKED_INTT_WRBUF_LATENCY - 1),
      buf_wrptr_reg.range(2 * (MASKED_INTT_WRBUF_LATENCY - 1) + 1, 2));
  }

  return sc_biguint<BUF_WRPTR_REG_SIZE>(0);
}

sc_uint<2> getMemRdIndexOfst(sc_uint<2> index_count, sc_uint<2> index_rand_offset) { //line 794, no change
  return index_count + index_rand_offset;
}

sc_uint<15> wraparoundMemAddr(sc_uint<16> new_addr, sc_uint<15> base_addr) { //line 369, no change
  if (new_addr > (sc_uint<16>(base_addr) + MEM_LAST_ADDR)) {
    return new_addr - MEM_LAST_ADDR;
  }

  return new_addr;
}

sc_uint<2> getBufWrptr(bool buf_wren_intt, bool shuffle_en, bool masking_en_ctrl, bool mlkem, sc_uint<2> buf_wrptr_reg_d1, //line 782, added mlkem case
  sc_biguint<BUF_WRPTR_REG_SIZE> buf_wrptr_reg, sc_uint<2> buf_wrptr) {
  if (buf_wren_intt && !shuffle_en) {
    return buf_wrptr + 1;
  }

  if (buf_wren_intt && shuffle_en) {
    if (masking_en_ctrl) {
      return buf_wrptr_reg_d1;
    }
    if (mlkem) {
      return sc_uint<2>(buf_wrptr_reg.range(
        2 * (INTT_WRBUF_LATENCY-MLKEM_INTT_WRBUF_LATENCY) + 1, 
        2 * (INTT_WRBUF_LATENCY-MLKEM_INTT_WRBUF_LATENCY)));
    }

    return sc_uint<2>(buf_wrptr_reg.range(1, 0));
  }

  return buf_wrptr;
}

sc_uint<15> getMemWrAddr(bool rst_wr_addr, bool incr_mem_wr_addr, bool shuffle_en, NttMemBaseAddrs ntt_mem_base_addrs, //line 342 no change for gs mode but for ct mode there is mlkem case for mem_wr_addr_nxt calculation
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

  if (incr_rounds && rounds_count < sc_uint<3>(4)) {
    return rounds_count + 1;
  }

  if (rounds_count == sc_uint<3>(4)) {
    return sc_uint<3>(0);
  }

  return rounds_count;
}

bool getMaskingEnCtrl(sc_uint<3> rounds_count, MaskedGsReadStatesType read_state, MaskedGsWriteStatesType write_state, //line 250 no change
  bool masking_en_ctrl) {
  if (rounds_count == sc_uint<3>(0)
    && read_state == MaskedGsReadStatesType::MaskedGsReadStage
    && write_state == MaskedGsWriteStatesType::MaskedGsWriteStage) {
    return true;
  }

  if (rounds_count > sc_uint<3>(0)) {
    return false;
  }

  return masking_en_ctrl;
}

SC_MODULE(ntt_ctrl_masked_gs_mlkem) {
public:
  SC_CTOR(ntt_ctrl_masked_gs_mlkem) {
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
  shared_in<bool> shuffle_en_in;
  shared_in<bool> mlkem_in;
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
  shared_out<bool> pw_rden_out;
  shared_out<bool> pw_wren_out;
  shared_out<bool> pw_share_mem_rden_out;
  shared_out<bool> done_out;
  shared_out<bool> intt_passthrough_out;


private:
  MaskedGsReadStatesType read_state;
  MaskedGsWriteStatesType write_state;

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
  sc_uint<2> buf_wrptr_reg_d1;
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
  sc_uint<3> bf_enable_reg;
  sc_uint<3> bf_enable_reg_dummy;

  bool buf_wren_intt_reg;
  bool buf_wren_intt_reg_dummy;
  bool incr_twiddle_addr_reg;
  bool masking_en_ctrl_reg;
  bool mem_rd_en_reg;
  bool mem_rd_en_reg_dummy;

  [[noreturn]] void read() {
    read_state = MaskedGsReadStatesType::MaskedGsReadIdle;

    while (true) {
      MaskedGsReadStatesType next_state = MaskedGsReadStatesType::MaskedGsReadIdle;
      bool rst_rd_addr = false;
      bool incr_mem_rd_addr = false;
      bool latch_index_rand_offset = false;
      sc_uint<15> rd_addr_step = 0;

      if (read_state == MaskedGsReadStatesType::MaskedGsReadIdle) {
        insert_state("read_idle");
        next_state = MaskedGsReadStatesType::MaskedGsReadIdle;
        rst_rd_addr = true;
        incr_mem_rd_addr = false;
        latch_index_rand_offset = false;
        rd_addr_step = 0;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = MaskedGsReadStatesType::MaskedGsReadStage;
        }
      } else if (read_state == MaskedGsReadStatesType::MaskedGsReadStage) {
        insert_state("read_stage");
        next_state = MaskedGsReadStatesType::MaskedGsReadStage;
        rst_rd_addr = true;
        incr_mem_rd_addr = false;
        latch_index_rand_offset = false;
        rd_addr_step = 0;

        if (rounds_count == 4) {
          next_state = MaskedGsReadStatesType::MaskedGsReadIdle;
        } else if (write_state == MaskedGsWriteStatesType::MaskedGsWriteStage) {
          next_state = MaskedGsReadStatesType::MaskedGsReadExec;
          latch_index_rand_offset = true;
        }
      } else {
        // if (read_state == MaskedGsReadStatesType::MaskedGsReadExec) {
        insert_state("read_exec");
        next_state = MaskedGsReadStatesType::MaskedGsReadExec;
        rst_rd_addr = false;
        incr_mem_rd_addr = true;
        latch_index_rand_offset = false;
        rd_addr_step = 1;

        bool sampler_valid = false;
        sampler_valid_in->get(sampler_valid);

        if (rd_valid_count >= 0x3F) {
          next_state = MaskedGsReadStatesType::MaskedGsReadStage;
        }
      }

      latch_index_rand_offset = latch_index_rand_offset || index_count == 3;

      bool sampler_valid = false;
      sampler_valid_in->get(sampler_valid);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      bool mlkem = false;
      mlkem_in->get(mlkem);

      bool accumulate = false;
      accumulate_in->get(accumulate);

      sc_uint<6> random;
      random_in->get(random);

      NttMemBaseAddrs mem_base_addrs;
      ntt_mem_base_addr_in->get(mem_base_addrs);

      std::array<sc_uint<7>, 8> twiddle_rand_offset_array = getTwiddleRandOffsets(masking_en_ctrl_reg,
        chunk_count_reg,
        buf_wrptr_reg);

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
        read_state == MaskedGsReadStatesType::MaskedGsReadIdle
        || (read_state == MaskedGsReadStatesType::MaskedGsReadStage && !butterfly_ready),
        getTwiddleIncrAddr(shuffle_en,
          rounds_count,
          twiddle_rand_offset_array,
          twiddle_end_addr_array,
          twiddle_addr_reg),
        twiddle_addr_reg);

      incr_twiddle_addr_reg = read_state == MaskedGsReadStatesType::MaskedGsReadExec;

      chunk_count_reg = getChunkCountReg(masking_en_ctrl_reg,
        butterfly_ready,
        incr_mem_rd_addr,
        chunk_count,
        chunk_count_reg);

      sc_uint<2> mem_rd_index_ofst = getMemRdIndexOfst(index_count, index_rand_offset);

      sc_uint<15> mem_rd_base_addr = getMemRdBaseAddr(rounds_count, mem_base_addrs);

      mem_rd_en_reg_dummy = mem_rd_en_reg_dummy && mem_rd_en_reg;
      mem_rd_en_reg = read_state == MaskedGsReadStatesType::MaskedGsReadExec
          && mem_rd_addr <= (mem_rd_base_addr + MEM_LAST_ADDR);

      sc_uint<16> mem_rd_addr_nxt = getMemRdAddrNxt(shuffle_en,
        rounds_count,
        getShuffledMemRdAddrNxt(chunk_count, rd_addr_step, mem_rd_index_ofst, mem_rd_base_addr),
        getUnshuffledMemRdAddrNxt(mem_rd_addr, rd_addr_step));

      mem_rd_addr = rst_rd_addr
          ? ((shuffle_en)
            ? sc_uint<15>(mem_rd_base_addr + 4 * chunk_rand_offset)
            : mem_rd_base_addr)
          : (incr_mem_rd_addr
            ? wraparoundMemAddr(mem_rd_addr_nxt, mem_rd_base_addr)
            : mem_rd_addr);
      mem_rd_addr_out->set(mem_rd_addr);

      buf_wrptr_reg_d1 = mlkem ? 
                              buf_wrptr_reg.range(
                              2 * (MASKED_INTT_WRBUF_LATENCY-MLKEM_MASKED_INTT_WRBUF_LATENCY) + 1, 
                              2 * (MASKED_INTT_WRBUF_LATENCY-MLKEM_MASKED_INTT_WRBUF_LATENCY))
                              : buf_wrptr_reg.range(1, 0);
      buf_wrptr_reg = getBufWrptrReg(incr_mem_rd_addr,
        butterfly_ready,
        masking_en_ctrl_reg,
        mem_rd_index_ofst,
        buf_wrptr_reg);

      bf_enable_reg_dummy = bf_enable_reg_dummy + bf_enable_reg;
      bf_enable_reg <<= 1;
      bf_enable_reg += read_state == MaskedGsReadStatesType::MaskedGsReadExec ? sc_uint<3>(1) : sc_uint<3>(0);

      rd_valid_count = getRdValidCount(read_state, rounds_count, sampler_valid, rd_valid_count);

      index_rand_offset = latch_index_rand_offset ? random.range(1, 0) : index_rand_offset;

      index_count = getIndexCount(incr_mem_rd_addr, index_count);

      read_state = next_state;
    }
  }

  [[noreturn]] void write() {
    write_state = MaskedGsWriteStatesType::MaskedGsWriteIdle;

    while (true) {
      MaskedGsWriteStatesType next_state = MaskedGsWriteStatesType::MaskedGsWriteIdle;
      bool rst_wr_addr = false;
      bool incr_mem_wr_addr = false;
      bool buf_wren_intt = false;
      bool latch_chunk_rand_offset = false;
      bool rst_wr_valid_count = false;
      bool incr_rounds_count = false;
      sc_uint<16> wr_addr_step = 0;

      if (write_state == MaskedGsWriteStatesType::MaskedGsWriteIdle) {
        insert_state("write_idle");
        next_state = MaskedGsWriteStatesType::MaskedGsWriteIdle;
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
          next_state = MaskedGsWriteStatesType::MaskedGsWriteStage;
          latch_chunk_rand_offset = true;
        }
      } else if (write_state == MaskedGsWriteStatesType::MaskedGsWriteStage) {
        insert_state("write_stage");
        rst_wr_addr = true;
        incr_mem_wr_addr = false;
        buf_wren_intt = false;
        latch_chunk_rand_offset = false;
        rst_wr_valid_count = true;
        incr_rounds_count = false;
        wr_addr_step = 0;

        if (rounds_count == 4) {
          next_state = MaskedGsWriteStatesType::MaskedGsWriteIdle;
        } else {
          next_state = MaskedGsWriteStatesType::MaskedGsWriteBuf;
        }
      } else if (write_state == MaskedGsWriteStatesType::MaskedGsWriteBuf) {
        insert_state("write_buf");
        next_state = MaskedGsWriteStatesType::MaskedGsWriteBuf;
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
          next_state = MaskedGsWriteStatesType::MaskedGsWriteMem;
          incr_mem_wr_addr = true;
        }
      } else if (write_state == MaskedGsWriteStatesType::MaskedGsWriteMem) {
        insert_state("write_mem");
        next_state = MaskedGsWriteStatesType::MaskedGsWriteMem;
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
          next_state = MaskedGsWriteStatesType::MaskedGsWriteBuf;
        } else if (buf0_valid && wr_valid_count == 0x3C) {
          next_state = MaskedGsWriteStatesType::MaskedGsWriteWait;
        }
      } else {
        // if (write_state == MaskedGsWriteStatesType::MaskedGsWriteWait) {
        insert_state("write_wait");
        next_state = MaskedGsWriteStatesType::MaskedGsWriteWait;
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
          next_state = MaskedGsWriteStatesType::MaskedGsWriteStage;
          latch_chunk_rand_offset = true;
          incr_rounds_count = true;
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

      bool mlkem = false;
      mlkem_in->get(mlkem);

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

      buf_wrptr = getBufWrptr(buf_wren_intt,
        shuffle_en,
        masking_en_ctrl_reg,
        mlkem,
        buf_wrptr_reg_d1,
        buf_wrptr_reg,
        buf_wrptr);
      buf_wrptr_out->set(buf_wrptr);

      rounds_count = getRoundsCount(rst_rounds, incr_rounds_count, rounds_count);
      intt_passthrough_out->set(rounds_count == 0 && mlkem); //line 308 new output
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

      opcode_out->set(1);
      masking_en_ctrl_reg = getMaskingEnCtrl(rounds_count, read_state, write_state, masking_en_ctrl_reg);
      masking_en_ctrl_out->set(masking_en_ctrl_reg);

      pw_rden_out->set(false);
      pw_wren_out->set(false);
      pw_share_mem_rden_out->set(false);
    }
  }
};

#endif
