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

#ifndef NTTCTRL_H
#define NTTCTRL_H

#include "Interfaces.h"

#define UNMASKED_BF_LATENCY 10
#define INTT_WRBUF_LATENCY 13
#define MAXIMUM_ADDR 63
#define RD_ADDR_STEP 1
#define WR_ADDR_STEP 16

#define MLKEM_INTT_WRBUF_LATENCY 9


enum class GsReadStatesType {
  GsReadIdle,
  GsReadStage,
  GsReadExec
};


enum class GsWriteStatesType {
  GsWriteIdle,
  GsWriteStage,
  GsWriteBuf,
  GsWriteMem,
  GsWriteWait
};


struct NttBaseAddrs {
  sc_uint<14> src_base_addr;
  sc_uint<14> interim_base_addr;
  sc_uint<14> dest_base_addr;
};


const std::array<sc_uint<7>, 8> twiddle_offsets = {
  0, 64, 80, 84, 0, 0, 0, 0
};

const std::array<sc_uint<7>, 8> twiddle_end_addrs = {
  63, 15, 3, 0, 0, 0, 0, 0
};


/**
 * Increments an address by the given step size and wraps it around in case it became too large
 */
sc_uint<15> incr_addr(sc_uint<15> addr, sc_uint<15> step, sc_uint<15> base) {
  sc_uint<16> new_addr = addr + step;

  if (new_addr > base + MAXIMUM_ADDR) {
    new_addr -= MAXIMUM_ADDR;
  }

  return static_cast<sc_uint<15>>(new_addr);
}

/**
 * Increments the mem_rd_addr in case shuffling is enabled
 */
sc_uint<15> get_rd_addr_shuffle(sc_uint<15> addr, sc_uint<15> step, sc_uint<15> base, sc_uint<4> chunk_count,
  sc_uint<2> mem_rd_index_ofst) {
  sc_uint<16> new_addr = 4 * chunk_count + step * mem_rd_index_ofst + base;

  if (new_addr > base + MAXIMUM_ADDR) {
    new_addr -= MAXIMUM_ADDR;
  }

  return static_cast<sc_uint<15>>(new_addr);
}

sc_uint<7> getTwiddleAddrIncr(bool shuffle_en, sc_uint<7> twiddle_rand_offset, sc_uint<7> current_addr,
  std::array<sc_uint<7>, 8> twiddle_end_addrs, sc_uint<3> rounds_count) {
  if (shuffle_en) {
    return twiddle_rand_offset;
  }

  if (current_addr == twiddle_end_addrs[rounds_count]) {
    return sc_uint<7>(0);
  }

  return current_addr + 1;
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

sc_uint<15> getMemRdAddrBase(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
  if (rounds_count == 0) {
    return base_addrs.src_base_addr;
  }

  if ((rounds_count & 1) != 0) {
    return base_addrs.interim_base_addr;
  }

  return base_addrs.dest_base_addr;
}

sc_uint<2> getBufWrptr(bool shuffle_en, bool mlkem, bool buf_wren_intt, sc_uint<2> buf_wrptr, sc_uint<26> buf_wrptr_reg) {
  if (buf_wren_intt) {
    if (shuffle_en) {
        if (mlkem) {
            return buf_wrptr_reg.range(
            2 * (INTT_WRBUF_LATENCY-MLKEM_INTT_WRBUF_LATENCY) + 1, 
            2 * (INTT_WRBUF_LATENCY-MLKEM_INTT_WRBUF_LATENCY));
        }
        return buf_wrptr_reg.range(1, 0);
    }

    return buf_wrptr + 1;
  }

  return buf_wrptr;
}

sc_uint<7> getWrValidCount(bool buf0_valid, GsWriteStatesType write_state, sc_uint<7> wr_valid_count) {
  if ((buf0_valid && wr_valid_count > 0x40U)
    || write_state == GsWriteStatesType::GsWriteIdle || write_state == GsWriteStatesType::GsWriteStage) {
    return sc_uint<7>(0);
  }

  if (buf0_valid) {
    return wr_valid_count + 4;
  }

  return wr_valid_count;
}

sc_uint<15> getMemWrAddrBase(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
  if ((rounds_count & 1) != 0) {
    return base_addrs.dest_base_addr;
  }

  return base_addrs.interim_base_addr;
}

SC_MODULE(ntt_ctrl_gs_mlkem) {
public:
  SC_CTOR(ntt_ctrl_gs_mlkem) {
    SC_THREAD(read)
    SC_THREAD(write)
  }

  shared_in<bool> ntt_enable_in;
  shared_in<bool> buf0_valid_in;
  shared_in<bool> shuffle_en_in;
  shared_in<bool> mlkem_in;
  shared_in<bool> intt_done_in;
  shared_in<bool> rst_rounds_in;
  shared_in<bool> butterfly_ready_in;
  shared_in<NttBaseAddrs> ntt_base_addrs_in;
  shared_in<sc_uint<6>> random_in;

  shared_out<bool> bf_enable_out;
  shared_out<sc_uint<3>> opcode_out;
  shared_out<bool> masking_en_ctrl_out;
  shared_out<sc_uint<2>> buf_wrptr_out;
  shared_out<sc_uint<2>> buf_rdptr_out;
  shared_out<sc_uint<15>> mem_rd_addr_out;
  shared_out<sc_uint<15>> mem_wr_addr_out;
  shared_out<bool> pw_rden_out;
  shared_out<bool> pw_wren_out;
  shared_out<bool> done_out;
  shared_out<bool> intt_passthrough_out;


private:
  GsReadStatesType read_state;
  GsWriteStatesType write_state;

  sc_uint<3> rounds_count;
  sc_uint<2> buf_count;
  sc_uint<4> chunk_rand_offset;
  sc_uint<2> index_rand_offset;
  sc_uint<4> chunk_count;
  sc_uint<2> index_count;
  sc_uint<26> buf_wrptr_reg;
  sc_uint<44> chunk_count_reg;

  bool unused_mem_rd_en_reg;
  sc_uint<7> unused_twiddle_addr_reg_d3;

  [[noreturn]] void read() {
    read_state = GsReadStatesType::GsReadIdle;
    sc_uint<7> rd_valid_count = 0;
    bool bf_enable_reg = false;
    bool incr_twiddle_addr_reg = false;
    sc_uint<7> twiddle_addr_reg = 0;
    sc_uint<7> twiddle_addr_reg_d2 = 0;
    sc_uint<7> twiddle_addr_reg_d3 = 0;
    sc_uint<15> mem_rd_addr_base = 0;
    sc_uint<15> mem_rd_addr = 0;
    bool mem_rd_en_reg = false;

    opcode_out->set(0);
    masking_en_ctrl_out->set(false);
    pw_rden_out->set(false);

    NttBaseAddrs initial_base_addrs;
    ntt_base_addrs_in->get(initial_base_addrs);
    mem_rd_addr_base = initial_base_addrs.src_base_addr;

    while (true) {
      GsReadStatesType next_state = GsReadStatesType::GsReadIdle;

      bool incr_twiddle_addr = false;
      bool latch_index_rand_offset = false;
      bool rst_twiddle_addr_reg = false;
      sc_uint<2> new_index_count = 0;

      if (read_state == GsReadStatesType::GsReadIdle) {
        insert_state("read_idle");

        // Required to not optimize away 'mem_rd_en_reg'
        unused_mem_rd_en_reg = unused_mem_rd_en_reg || mem_rd_en_reg;
        // Required to not optimize away 'twiddle_addr_reg_d3'
        unused_twiddle_addr_reg_d3 = unused_twiddle_addr_reg_d3 + twiddle_addr_reg_d3;

        latch_index_rand_offset = false;
        new_index_count = index_count;

        mem_rd_en_reg = false;

        rd_valid_count = 0;
        incr_twiddle_addr = incr_twiddle_addr_reg;
        incr_twiddle_addr_reg = false;
        rst_twiddle_addr_reg = true;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        mem_rd_addr_base = getMemRdAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_rd_addr = shuffle_en
            ? static_cast<sc_uint<15>>(mem_rd_addr_base + (chunk_rand_offset << 2))
            : mem_rd_addr_base;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = GsReadStatesType::GsReadStage;
        } else {
          next_state = GsReadStatesType::GsReadIdle;
        }
      } else if (read_state == GsReadStatesType::GsReadStage) {
        insert_state("read_stage");
        latch_index_rand_offset = false;
        new_index_count = index_count;

        mem_rd_en_reg = false;

        rd_valid_count = 0;
        incr_twiddle_addr = incr_twiddle_addr_reg;
        incr_twiddle_addr_reg = false;

        bool butterfly_ready = false;
        butterfly_ready_in->get(butterfly_ready);
        rst_twiddle_addr_reg = !butterfly_ready;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        mem_rd_addr_base = getMemRdAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_rd_addr = shuffle_en
            ? static_cast<sc_uint<15>>(mem_rd_addr_base + (chunk_rand_offset << 2))
            : mem_rd_addr_base;

        bool intt_done = false;
        intt_done_in->get(intt_done);

        if (rounds_count == static_cast<sc_uint<3>>(4U)) {
          next_state = GsReadStatesType::GsReadIdle;
        } else if (write_state == GsWriteStatesType::GsWriteStage && !intt_done) {
          latch_index_rand_offset = true;

          next_state = GsReadStatesType::GsReadExec;
        } else {
          next_state = read_state;
        }
      } else {
        // if (read_state == GsReadStatesTypes::GsReadExec) {
        insert_state("read_exec");
        latch_index_rand_offset = false;
        new_index_count = index_count;

        mem_rd_en_reg = mem_rd_addr <= mem_rd_addr_base + MAXIMUM_ADDR;

        incr_twiddle_addr = incr_twiddle_addr_reg;
        incr_twiddle_addr_reg = true;
        rst_twiddle_addr_reg = false;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        mem_rd_addr = shuffle_en
            ? get_rd_addr_shuffle(mem_rd_addr,
              RD_ADDR_STEP,
              mem_rd_addr_base,
              chunk_count,
              index_count + index_rand_offset)
            : incr_addr(mem_rd_addr, RD_ADDR_STEP, mem_rd_addr_base);
        new_index_count += 1;

        if (rd_valid_count == static_cast<sc_uint<7>>(0x3FU)) {
          next_state = GsReadStatesType::GsReadStage;
        } else {
          next_state = GsReadStatesType::GsReadExec;
        }

        rd_valid_count += 1;
      }

      mem_rd_addr_out->set(mem_rd_addr);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      sc_uint<4> chunk_count_reg_bf_latency = static_cast<sc_uint<4>>(chunk_count_reg >> (UNMASKED_BF_LATENCY * 4));
      sc_uint<2> buf_wrptr_reg_wrbuf_latency = static_cast<sc_uint<2>>(buf_wrptr_reg >> ((INTT_WRBUF_LATENCY - 1) * 2));
      std::array<sc_uint<7>, 8> twiddle_rand_offsets = {
        4 * chunk_count_reg_bf_latency + buf_wrptr_reg_wrbuf_latency,
        (chunk_count_reg_bf_latency & 0x3) * 4 + buf_wrptr_reg_wrbuf_latency,
        buf_wrptr_reg_wrbuf_latency,
        0,
        0,
        0,
        0,
        0
      };
      sc_uint<7> twiddle_rand_offset = twiddle_rand_offsets.at(rounds_count);
      sc_uint<7> twiddle_offset = twiddle_offsets.at(rounds_count);

      bool butterfly_ready = false;
      butterfly_ready_in->get(butterfly_ready);

      sc_uint<7> twiddle_addr_int = shuffle_en
          ? twiddle_rand_offset + twiddle_offset
          : twiddle_addr_reg + twiddle_offset;

      twiddle_addr_reg_d3 = twiddle_addr_reg_d2;
      twiddle_addr_reg_d2 = twiddle_addr_int;
      twiddle_addr_reg = getTwiddleAddrReg(incr_twiddle_addr,
        rst_twiddle_addr_reg,
        getTwiddleAddrIncr(shuffle_en, twiddle_rand_offset, twiddle_addr_reg, twiddle_end_addrs, rounds_count),
        twiddle_addr_reg);

      buf_wrptr_reg = (read_state == GsReadStatesType::GsReadExec || butterfly_ready)
          ? static_cast<sc_uint<26>>(((buf_wrptr_reg >> 2)
            | ((static_cast<sc_uint<26>>(index_count) + static_cast<sc_uint<26>>(index_rand_offset)) << 24)))
          : sc_uint<26>(0);

      sc_uint<6> random;
      random_in->get(random);

      index_rand_offset = (latch_index_rand_offset || index_count == 3)
          ? random.range(1, 0)
          : index_rand_offset;

      chunk_count_reg = (butterfly_ready || read_state == GsReadStatesType::GsReadExec)
          ? static_cast<sc_uint<44>>(static_cast<sc_uint<44>>(chunk_count_reg >> 4) | (static_cast<sc_uint<44>>(
            chunk_count) << 40))
          : chunk_count_reg;

      bf_enable_out->set(shuffle_en ? bf_enable_reg : (read_state == GsReadStatesType::GsReadExec));
      bf_enable_reg = (read_state == GsReadStatesType::GsReadExec);

      index_count = new_index_count;
      read_state = next_state;

      opcode_out->set(1);
    }
  }

  [[noreturn]] void write() {
    write_state = GsWriteStatesType::GsWriteIdle;
    buf_count = 0;
    sc_uint<7> wr_valid_count = 0;
    sc_uint<2> buf_wrptr = 0;
    sc_uint<15> mem_wr_addr = 0;

    pw_wren_out->set(false);

    NttBaseAddrs initial_base_addrs;
    ntt_base_addrs_in->get(initial_base_addrs);

    while (true) {
      GsWriteStatesType next_state = GsWriteStatesType::GsWriteIdle;

      bool latch_chunk_rand_offset = false;
      bool buf_wren_intt = false;

      if (write_state == GsWriteStatesType::GsWriteIdle) {
        insert_state("write_idle");
        latch_chunk_rand_offset = false;
        buf_wren_intt = false;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<15> mem_wr_addr_base = getMemWrAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = shuffle_en ? sc_uint<15>(mem_wr_addr_base + chunk_rand_offset) : mem_wr_addr_base;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          latch_chunk_rand_offset = true;

          next_state = GsWriteStatesType::GsWriteStage;
        } else {
          next_state = GsWriteStatesType::GsWriteIdle;
        }
      } else if (write_state == GsWriteStatesType::GsWriteStage) {
        insert_state("write_stage");
        latch_chunk_rand_offset = false;
        buf_wren_intt = false;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<15> mem_wr_addr_base = getMemWrAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = shuffle_en ? sc_uint<15>(mem_wr_addr_base + chunk_rand_offset) : mem_wr_addr_base;

        if (rounds_count == 4) {
          next_state = GsWriteStatesType::GsWriteIdle;
        } else {
          next_state = GsWriteStatesType::GsWriteBuf;
        }
      } else if (write_state == GsWriteStatesType::GsWriteBuf) {
        insert_state("write_buf");
        latch_chunk_rand_offset = false;

        butterfly_ready_in->get(buf_wren_intt);

        bool buf0_valid = false;
        buf0_valid_in->get(buf0_valid);

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<15> mem_wr_addr_base = getMemWrAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = buf0_valid
            ? ((shuffle_en && mem_wr_addr == (mem_wr_addr_base + MAXIMUM_ADDR))
              ? mem_wr_addr_base
              : incr_addr(mem_wr_addr, WR_ADDR_STEP, mem_wr_addr_base))
            : mem_wr_addr;

        if (buf0_valid) {
          next_state = GsWriteStatesType::GsWriteMem;
        } else {
          next_state = GsWriteStatesType::GsWriteBuf;
        }
      } else if (write_state == GsWriteStatesType::GsWriteMem) {
        insert_state("write_mem");
        latch_chunk_rand_offset = false;
        buf_wren_intt = true;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<15> mem_wr_addr_base = getMemWrAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = (shuffle_en && mem_wr_addr == (mem_wr_addr_base + MAXIMUM_ADDR))
            ? mem_wr_addr_base
            : incr_addr(mem_wr_addr, WR_ADDR_STEP, mem_wr_addr_base);

        bool buf0_valid = false;
        buf0_valid_in->get(buf0_valid);

        if (!buf0_valid && buf_count == 0U && wr_valid_count < 0x40U) {
          next_state = GsWriteStatesType::GsWriteBuf;
        } else if (buf0_valid && wr_valid_count == 0x3CU) {
          next_state = GsWriteStatesType::GsWriteWait;
        } else {
          next_state = GsWriteStatesType::GsWriteMem;
        }
      } else {
        // if (write_state == GsWriteStatesType::GsWriteWait) {
        insert_state("write_wait");
        latch_chunk_rand_offset = false;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<15> mem_wr_addr_base = getMemWrAddrBase(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = (shuffle_en && mem_wr_addr == (mem_wr_addr_base + MAXIMUM_ADDR))
            ? mem_wr_addr_base
            : incr_addr(mem_wr_addr, WR_ADDR_STEP, mem_wr_addr_base);

        buf_wren_intt = !shuffle_en && buf_count <= 3;

        if (buf_count == 3U) {
          latch_chunk_rand_offset = true;

          next_state = GsWriteStatesType::GsWriteStage;
        } else {
          next_state = GsWriteStatesType::GsWriteWait;
        }
      }

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool mlkem = false;
      mlkem_in->get(mlkem);

      bool buf0_valid = false;
      buf0_valid_in->get(buf0_valid);

      bool rst_rounds = false;
      rst_rounds_in->get(rst_rounds);

      sc_uint<6> random;
      random_in->get(random);

      chunk_rand_offset = latch_chunk_rand_offset ? random.range(5, 2) : chunk_rand_offset;
      chunk_count = latch_chunk_rand_offset
          ? random.range(5, 2)
          : (index_count == 3 ? static_cast<sc_uint<4>>(chunk_count + 1) : chunk_count);

      buf_wrptr = getBufWrptr(shuffle_en, mlkem, buf_wren_intt, buf_wrptr, buf_wrptr_reg);
      buf_wrptr_out->set(buf_wrptr);

      mem_wr_addr_out->set(mem_wr_addr);

      wr_valid_count = getWrValidCount(buf0_valid, write_state, wr_valid_count);

      rounds_count = (rst_rounds || rounds_count == 4U)
          ? static_cast<sc_uint<3>>(0)
          : ((write_state == GsWriteStatesType::GsWriteWait && next_state == GsWriteStatesType::GsWriteStage)
            ? static_cast<sc_uint<3>>(rounds_count + 1)
            : rounds_count);

      done_out->set(rounds_count == 4U);
      intt_passthrough_out->set(rounds_count == 0 && mlkem); //line 308 new output

      buf_count = (buf0_valid || (buf_count > 0 && buf_count < 3))
          ? static_cast<sc_uint<2>>(buf_count + 1)
          : static_cast<sc_uint<2>>(0);
      buf_rdptr_out->set(buf_count);

      write_state = next_state;
    }
  }
};

#endif
