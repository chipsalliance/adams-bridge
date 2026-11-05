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

constexpr unsigned BF_LATENCY         = 6;  // ntt_defines_pkg.sv
constexpr unsigned INTT_WRBUF_LATENCY = 9;  // ntt_defines_pkg.sv
constexpr unsigned MEM_LAST_ADDR      = 63;
constexpr unsigned INTT_READ_ADDR_STEP  = 1;   // ntt_ctrl.sv localparam
constexpr unsigned INTT_WRITE_ADDR_STEP = 16;  // ntt_ctrl.sv localparam

// Mirror ABR_MEM_ADDR_WIDTH = $clog2(ABR_MEM_MAX_DEPTH) + 3 from abr_params_pkg.sv
constexpr unsigned ABR_MEM_MAX_DEPTH_LOG2 = 11; // $clog2(ABR_MEM_MAX_DEPTH=1536)
constexpr unsigned MEM_ADDR_WIDTH         = ABR_MEM_MAX_DEPTH_LOG2 + 3; // = 14

constexpr unsigned COEFF_PER_CLK  = 4;                        // abr_params_pkg.sv
constexpr unsigned MLDSA_N        = 256;                      // abr_params_pkg.sv
constexpr unsigned VALID_COUNT    = MLDSA_N / COEFF_PER_CLK;  // = 64
constexpr unsigned NTT_NUM_ROUNDS = 4;                        // ntt_ctrl.sv localparam

constexpr unsigned OPCODE_CT = 0;  // ntt_defines_pkg.sv localparam ct
constexpr unsigned OPCODE_GS = 1;  // ntt_defines_pkg.sv localparam gs


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
  // sc_uint<MEM_ADDR_WIDTH> src_base_addr;
  // sc_uint<MEM_ADDR_WIDTH> interim_base_addr;
  // sc_uint<MEM_ADDR_WIDTH> dest_base_addr;
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
// sc_uint<MEM_ADDR_WIDTH> incr_addr(sc_uint<MEM_ADDR_WIDTH> addr, sc_uint<MEM_ADDR_WIDTH> step, sc_uint<MEM_ADDR_WIDTH> base) {
sc_uint<14> incr_addr(sc_uint<14> addr, sc_uint<14> step, sc_uint<14> base) {
  // sc_uint<MEM_ADDR_WIDTH+1> new_addr = addr + step;
  sc_uint<15> new_addr = addr + step;

  if (new_addr > base + MEM_LAST_ADDR) {
    new_addr -= MEM_LAST_ADDR;
  }

  // return static_cast<sc_uint<MEM_ADDR_WIDTH>>(new_addr);
  return static_cast<sc_uint<14>>(new_addr);
}

/**
 * Increments the mem_rd_addr in case shuffling is enabled
 */
// sc_uint<MEM_ADDR_WIDTH> get_rd_addr_shuffle(sc_uint<MEM_ADDR_WIDTH> addr, sc_uint<MEM_ADDR_WIDTH> step, sc_uint<MEM_ADDR_WIDTH> base, sc_uint<4> chunk_count,
sc_uint<14> get_rd_addr_shuffle(sc_uint<14> addr, sc_uint<14> step, sc_uint<14> base, sc_uint<4> chunk_count,
  sc_uint<2> mem_rd_index_ofst) {
  // sc_uint<MEM_ADDR_WIDTH+1> new_addr = COEFF_PER_CLK*chunk_count + step*mem_rd_index_ofst + base;
  sc_uint<15> new_addr = COEFF_PER_CLK*chunk_count + step*mem_rd_index_ofst + base;

  if (new_addr > base + MEM_LAST_ADDR) {
    new_addr -= MEM_LAST_ADDR;
  }

  // return static_cast<sc_uint<MEM_ADDR_WIDTH>>(new_addr);
  return static_cast<sc_uint<14>>(new_addr);
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

// sc_uint<MEM_ADDR_WIDTH> getMemRdBaseAddr(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
sc_uint<14> getMemRdBaseAddr(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
  if (rounds_count == 0) {
    return base_addrs.src_base_addr;
  }

  if ((rounds_count & 1) != 0) {
    return base_addrs.interim_base_addr;
  }

  return base_addrs.dest_base_addr;
}

// sc_uint<2> getBufWrptr(bool shuffle_en, bool buf_wren_intt, sc_uint<2> buf_wrptr, sc_uint<2*INTT_WRBUF_LATENCY> buf_wrptr_reg) {
sc_uint<2> getBufWrptr(bool shuffle_en, bool buf_wren_intt, sc_uint<2> buf_wrptr, sc_uint<18> buf_wrptr_reg) {
  if (buf_wren_intt) {
    if (shuffle_en) {
      return buf_wrptr_reg.range(1, 0);
    }

    return buf_wrptr + 1;
  }

  return buf_wrptr;
}

sc_uint<7> getWrValidCount(bool buf0_valid, GsWriteStatesType write_state, sc_uint<7> wr_valid_count) {
  if ((buf0_valid && wr_valid_count > VALID_COUNT)
    || write_state == GsWriteStatesType::GsWriteIdle || write_state == GsWriteStatesType::GsWriteStage) {
    return sc_uint<7>(0);
  }

  if (buf0_valid) {
    return wr_valid_count + 4;
  }

  return wr_valid_count;
}

// sc_uint<MEM_ADDR_WIDTH> getMemWrBaseAddr(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
sc_uint<14> getMemWrBaseAddr(sc_uint<3> rounds_count, NttBaseAddrs base_addrs) {
  if ((rounds_count & 1) != 0) {
    return base_addrs.dest_base_addr;
  }

  return base_addrs.interim_base_addr;
}

SC_MODULE(ntt_ctrl_gs_mldsa) {
public:
  SC_CTOR(ntt_ctrl_gs_mldsa) {
    SC_THREAD(read)
    SC_THREAD(write)
  }

  struct Request_and_Address {
    bool request;
    sc_uint<MEM_ADDR_WIDTH> address;
  };

  shared_in<bool> ntt_enable_in;
  shared_in<bool> buf0_valid_in;
  shared_in<bool> shuffle_en_in;
  shared_in<bool> intt_done_in;
  shared_in<bool> rst_rounds_in;
  shared_in<bool> butterfly_ready_in;
  shared_in<NttBaseAddrs> ntt_base_addrs_in;
  shared_in<sc_uint<6>> random_in;

  shared_out<bool> bf_enable_out;
  shared_out<sc_uint<3>> opcode_out;
  shared_out<sc_uint<2>> buf_wrptr_out;
  shared_out<sc_uint<2>> buf_rdptr_out;
  shared_out<Request_and_Address> mem_read_req_port;
  Request_and_Address read_req;
  shared_out<Request_and_Address> mem_write_req_port;
  Request_and_Address write_req;
  shared_out<bool> pw_rden_out;
  shared_out<bool> pw_rden_dest_mem_out;
  shared_out<bool> pw_wren_out;
  shared_out<bool> done_out;
  shared_out<sc_uint<7>> twiddle_addr_reg_2_out;
  shared_out<bool> ntt_passthrough_out;
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
  sc_uint<2*INTT_WRBUF_LATENCY> buf_wrptr_reg;
  sc_uint<4*(BF_LATENCY+1)> chunk_count_reg;

  [[noreturn]] void read() {
    read_state = GsReadStatesType::GsReadIdle;
    sc_uint<7> rd_valid_count = 0;
    bool bf_enable_reg_0 = false;
    bool incr_twiddle_addr_reg = false;
    sc_uint<7> twiddle_addr_int = 0;
    sc_uint<7> twiddle_addr_reg_1 = 0;
    sc_uint<7> twiddle_addr_reg_2 = 0;
    // sc_uint<MEM_ADDR_WIDTH> mem_rd_base_addr = 0;
    sc_uint<MEM_ADDR_WIDTH> mem_rd_addr = 0;
    bool mem_rd_en_reg = false;

    opcode_out->set(OPCODE_CT);
    pw_rden_out->set(false);

    // NttBaseAddrs initial_base_addrs;
    // ntt_base_addrs_in->get(initial_base_addrs);
    // mem_rd_base_addr = initial_base_addrs.src_base_addr;

    while (true) {
      GsReadStatesType next_state = GsReadStatesType::GsReadIdle;

      bool incr_twiddle_addr = false;
      bool latch_index_rand_offset = false;
      bool rst_twiddle_addr_reg = false;
      sc_uint<2> new_index_count = 0;

      if (read_state == GsReadStatesType::GsReadIdle) {
        insert_state("read_idle");

        latch_index_rand_offset = false;
        new_index_count = index_count;

        mem_rd_en_reg = false;

        rd_valid_count = 0;
        incr_twiddle_addr = incr_twiddle_addr_reg;
        incr_twiddle_addr_reg = false;
        rst_twiddle_addr_reg = true;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_rd_base_addr = getMemRdBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_rd_addr = shuffle_en
            ? static_cast<sc_uint<MEM_ADDR_WIDTH>>(mem_rd_base_addr + COEFF_PER_CLK*chunk_rand_offset)
            : mem_rd_base_addr;

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
        sc_uint<MEM_ADDR_WIDTH> mem_rd_base_addr = getMemRdBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_rd_addr = shuffle_en
            ? static_cast<sc_uint<MEM_ADDR_WIDTH>>(mem_rd_base_addr + COEFF_PER_CLK*chunk_rand_offset)
            : mem_rd_base_addr;

        bool intt_done = false;
        intt_done_in->get(intt_done);

        if (rounds_count == static_cast<sc_uint<3>>(NTT_NUM_ROUNDS)) {
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

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_rd_base_addr = getMemRdBaseAddr(rounds_count, ntt_base_addrs);

        mem_rd_en_reg = mem_rd_addr <= mem_rd_base_addr + MEM_LAST_ADDR;

        incr_twiddle_addr = incr_twiddle_addr_reg;
        incr_twiddle_addr_reg = true;
        rst_twiddle_addr_reg = false;

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);

        mem_rd_addr = shuffle_en
            ? get_rd_addr_shuffle(mem_rd_addr,
              INTT_READ_ADDR_STEP,
              mem_rd_base_addr,
              chunk_count,
              index_count + index_rand_offset)
            : incr_addr(mem_rd_addr, INTT_READ_ADDR_STEP, mem_rd_base_addr);
        new_index_count += 1;

        if (rd_valid_count == static_cast<sc_uint<7>>(VALID_COUNT - 1)) {
          next_state = GsReadStatesType::GsReadStage;
        } else {
          next_state = GsReadStatesType::GsReadExec;
        }

        rd_valid_count += 1;
      }

      read_req.request = mem_rd_en_reg;
      read_req.address = mem_rd_addr;
      mem_read_req_port->set(read_req);

      ntt_passthrough_out->set(false);
      intt_passthrough_out->set(false);
      pw_rden_dest_mem_out->set(false);

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      sc_uint<4> chunk_count_reg_bf_latency = static_cast<sc_uint<4>>(chunk_count_reg >> (BF_LATENCY*4));
      sc_uint<2> buf_wrptr_reg_wrbuf_latency = static_cast<sc_uint<2>>(buf_wrptr_reg >> ((INTT_WRBUF_LATENCY - 1)*2));
      std::array<sc_uint<7>, 8> twiddle_rand_offsets = {
        COEFF_PER_CLK*chunk_count_reg_bf_latency + buf_wrptr_reg_wrbuf_latency,
        (chunk_count_reg_bf_latency & 0x3)*COEFF_PER_CLK + buf_wrptr_reg_wrbuf_latency,
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

      sc_uint<7> twiddle_addr_reg_0 = shuffle_en
          ? twiddle_rand_offset + twiddle_offset
          : twiddle_addr_int + twiddle_offset;

      twiddle_addr_reg_2 = twiddle_addr_reg_1;
      twiddle_addr_reg_1 = twiddle_addr_reg_0;
      twiddle_addr_int = getTwiddleAddrReg(incr_twiddle_addr,
        rst_twiddle_addr_reg,
        getTwiddleAddrIncr(shuffle_en, twiddle_rand_offset, twiddle_addr_int, twiddle_end_addrs, rounds_count),
        twiddle_addr_int);
      twiddle_addr_reg_2_out->set(twiddle_addr_reg_2);

      buf_wrptr_reg = (read_state == GsReadStatesType::GsReadExec || butterfly_ready)
          ? static_cast<sc_uint<2*INTT_WRBUF_LATENCY>>(((buf_wrptr_reg >> 2)
            | ((static_cast<sc_uint<2*INTT_WRBUF_LATENCY>>(index_count) + static_cast<sc_uint<2*INTT_WRBUF_LATENCY>>(index_rand_offset)) << (2*(INTT_WRBUF_LATENCY - 1)))))
          : sc_uint<2*INTT_WRBUF_LATENCY>(0);

      sc_uint<6> random;
      random_in->get(random);

      index_rand_offset = (latch_index_rand_offset || index_count == COEFF_PER_CLK - 1)
          ? random.range(1, 0)
          : index_rand_offset;

      chunk_count_reg = (butterfly_ready || read_state == GsReadStatesType::GsReadExec)
          ? static_cast<sc_uint<4*(BF_LATENCY+1)>>(static_cast<sc_uint<4*(BF_LATENCY+1)>>(chunk_count_reg >> 4) | (static_cast<sc_uint<4*(BF_LATENCY+1)>>(
            chunk_count) << (4*BF_LATENCY)))
          : chunk_count_reg;

      bf_enable_out->set(shuffle_en ? bf_enable_reg_0 : (read_state == GsReadStatesType::GsReadExec));
      bf_enable_reg_0 = (read_state == GsReadStatesType::GsReadExec);

      index_count = new_index_count;
      read_state = next_state;

      opcode_out->set(OPCODE_GS);
    }
  }

  [[noreturn]] void write() {
    write_state = GsWriteStatesType::GsWriteIdle;
    buf_count = 0;
    sc_uint<7> wr_valid_count = 0;
    sc_uint<2> buf_wrptr = 0;
    sc_uint<MEM_ADDR_WIDTH> mem_wr_addr = 0;

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
        write_req.request = false;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_wr_base_addr = getMemWrBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = shuffle_en ? sc_uint<MEM_ADDR_WIDTH>(mem_wr_base_addr + chunk_rand_offset) : mem_wr_base_addr;

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
        write_req.request = false;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_wr_base_addr = getMemWrBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = shuffle_en ? sc_uint<MEM_ADDR_WIDTH>(mem_wr_base_addr + chunk_rand_offset) : mem_wr_base_addr;

        if (rounds_count == NTT_NUM_ROUNDS) {
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
        write_req.request = buf0_valid;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_wr_base_addr = getMemWrBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = buf0_valid
            ? ((shuffle_en && mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR))
              ? mem_wr_base_addr
              : incr_addr(mem_wr_addr, INTT_WRITE_ADDR_STEP, mem_wr_base_addr))
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
        write_req.request = true;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_wr_base_addr = getMemWrBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = (shuffle_en && mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR))
            ? mem_wr_base_addr
            : incr_addr(mem_wr_addr, INTT_WRITE_ADDR_STEP, mem_wr_base_addr);

        bool buf0_valid = false;
        buf0_valid_in->get(buf0_valid);

        if (!buf0_valid && buf_count == 0U && wr_valid_count < VALID_COUNT) {
          next_state = GsWriteStatesType::GsWriteBuf;
        } else if (buf0_valid && wr_valid_count == VALID_COUNT - 4) {
          next_state = GsWriteStatesType::GsWriteWait;
        } else {
          next_state = GsWriteStatesType::GsWriteMem;
        }
      } else {
        // if (write_state == GsWriteStatesType::GsWriteWait) {
        insert_state("write_wait");
        latch_chunk_rand_offset = false;
        write_req.request = true;

        NttBaseAddrs ntt_base_addrs;
        ntt_base_addrs_in->get(ntt_base_addrs);
        sc_uint<MEM_ADDR_WIDTH> mem_wr_base_addr = getMemWrBaseAddr(rounds_count, ntt_base_addrs);

        bool shuffle_en = false;
        shuffle_en_in->get(shuffle_en);
        mem_wr_addr = (shuffle_en && mem_wr_addr == (mem_wr_base_addr + MEM_LAST_ADDR))
            ? mem_wr_base_addr
            : incr_addr(mem_wr_addr, INTT_WRITE_ADDR_STEP, mem_wr_base_addr);

        buf_wren_intt = !shuffle_en && buf_count <= COEFF_PER_CLK - 1;

        if (buf_count == COEFF_PER_CLK - 1) {
          latch_chunk_rand_offset = true;

          next_state = GsWriteStatesType::GsWriteStage;
        } else {
          next_state = GsWriteStatesType::GsWriteWait;
        }
      }

      bool shuffle_en = false;
      shuffle_en_in->get(shuffle_en);

      bool buf0_valid = false;
      buf0_valid_in->get(buf0_valid);

      bool rst_rounds = false;
      rst_rounds_in->get(rst_rounds);

      sc_uint<6> random;
      random_in->get(random);

      chunk_rand_offset = latch_chunk_rand_offset ? random.range(5, 2) : chunk_rand_offset;
      chunk_count = latch_chunk_rand_offset
          ? random.range(5, 2)
          : (index_count == COEFF_PER_CLK - 1 ? static_cast<sc_uint<4>>(chunk_count + 1) : chunk_count);

      buf_wrptr = getBufWrptr(shuffle_en, buf_wren_intt, buf_wrptr, buf_wrptr_reg);
      buf_wrptr_out->set(buf_wrptr);

      write_req.address = mem_wr_addr;
      mem_write_req_port->set(write_req);

      wr_valid_count = getWrValidCount(buf0_valid, write_state, wr_valid_count);

      rounds_count = (rst_rounds || rounds_count == NTT_NUM_ROUNDS)
          ? static_cast<sc_uint<3>>(0)
          : ((write_state == GsWriteStatesType::GsWriteWait && next_state == GsWriteStatesType::GsWriteStage)
            ? static_cast<sc_uint<3>>(rounds_count + 1)
            : rounds_count);

      done_out->set(rounds_count == NTT_NUM_ROUNDS);

      buf_count = (buf0_valid || (buf_count > 0 && buf_count < COEFF_PER_CLK - 1))
          ? static_cast<sc_uint<2>>(buf_count + 1)
          : static_cast<sc_uint<2>>(0);
      buf_rdptr_out->set(buf_count);

      write_state = next_state;
    }
  }
};

#endif
