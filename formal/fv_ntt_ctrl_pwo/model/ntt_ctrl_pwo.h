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

#ifndef NTT_CTRL_PWO_H
#define NTT_CTRL_PWO_H

#include <array>
#include "Interfaces.h"

#define PWA_MODE 3
#define PWS_MODE 4
#define PWO_READ_ADDR_STEP 1
#define PWO_WRITE_ADDR_STEP 1
#define UNMASKED_BF_LATENCY 10
#define BUF_RDPTR_REG_SIZE (2 * (UNMASKED_BF_LATENCY + 1))
#define CHUNK_COUNT_REG_SIZE (4 * (UNMASKED_BF_LATENCY + 1))
#define UNMASKED_PWM_LATENCY 5


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


sc_uint<2> getMemRdIndexOfst(sc_uint<2> index_count, sc_uint<2> index_rand_offset) {
  return index_count + index_rand_offset;
}

sc_uint<15> getPwAddrRst(bool shuffle_en, sc_uint<4> chunk_rand_offset, sc_uint<15> base_addr) {
  if (shuffle_en) {
    return 4 * chunk_rand_offset + base_addr;
  }

  return base_addr;
}

sc_uint<15> getPwAddrIncrAbcWr(bool shuffle_en, sc_uint<15> addr_nxt, sc_uint<15> current_addr, sc_uint<15> addr_step) {
  if (shuffle_en) {
    return addr_nxt;
  }

  return current_addr + addr_step;
}

sc_uint<15> getPwAddrAbcWr(bool rst_addr, bool incr_addr, sc_uint<15> addr_rst, sc_uint<15> addr_incr,
  sc_uint<15> addr_default) {
  if (rst_addr) {
    return addr_rst;
  }

  if (incr_addr) {
    return addr_incr;
  }

  return addr_default;
}

sc_uint<15> getPwAddrCrd(bool shuffle_en, bool accumulate, bool rst_pw_addr, bool incr_pw_rd_addr, sc_uint<15> addr_rst,
  sc_uint<15> addr_nxt, sc_uint<15> addr_default, sc_uint<15> addr_step) {
  if (rst_pw_addr) {
    return addr_rst;
  }

  if (incr_pw_rd_addr) {
    if (shuffle_en) {
      if (accumulate) {
        return addr_nxt;
      }

      return sc_uint<15>(0);
    }

    if (accumulate) {
      return addr_default + addr_step;
    }

    return sc_uint<15>(0);
  }

  return addr_default;
}

sc_uint<15> getPwAddrNxt(sc_uint<15> base_addr, sc_uint<4> chunk_count, sc_uint<15> step, sc_uint<15> offset) {
  return base_addr + 4 * chunk_count + step * offset;
}

SC_MODULE(ntt_ctrl) {
public:
  SC_CTOR(ntt_ctrl) {
    SC_THREAD(read)
    SC_THREAD(write)
    SC_THREAD(commons)
  }

  shared_in<sc_uint<3>> ntt_mode_in;
  shared_in<bool> ntt_enable_in;
  shared_in<bool> butterfly_ready_in;
  shared_in<bool> sampler_valid_in;
  shared_in<bool> accumulate_in;
  shared_in<bool> shuffle_en_in;
  shared_in<PwoMemAddrs> pwo_mem_base_addr_in;
  shared_in<sc_uint<6>> random_in;

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
  sc_uint<4> chunk_rand_offset;
  sc_uint<15> pw_mem_rd_addr_a_reg;
  sc_uint<15> pw_mem_rd_addr_b_reg;
  sc_uint<15> pw_mem_rd_addr_c_reg;
  sc_uint<15> pw_mem_wr_addr_c_reg;

  sc_uint<BUF_RDPTR_REG_SIZE> buf_rdptr_reg;
  sc_uint<CHUNK_COUNT_REG_SIZE> chunk_count_reg;

  bool bf_enable_reg;
  bool bf_enable_reg_d2;
  bool bf_enable_reg_d2_dummy;
  bool pw_rden_reg;
  bool pw_rden_reg_dummy;
  bool pw_wren_reg;
  bool pw_wren_reg_dummy;

  [[noreturn]] void read() {
    read_state = PwoReadStatesType::PwoReadIdle;

    PwoReadStatesType next_state = PwoReadStatesType::PwoReadIdle;
    bool incr_pw_rd_addr = false;

    while (true) {
      if (read_state == PwoReadStatesType::PwoReadIdle) {
        insert_state("read_idle");
        next_state = PwoReadStatesType::PwoReadIdle;
        incr_pw_rd_addr = false;

        bool ntt_enable = false;
        ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = PwoReadStatesType::PwoReadStage;
        }
      } else if (read_state == PwoReadStatesType::PwoReadStage) {
        insert_state("read_stage");
        next_state = PwoReadStatesType::PwoReadStage;
        incr_pw_rd_addr = false;

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

      PwoMemAddrs base_addrs;
      pwo_mem_base_addr_in->get(base_addrs);

      rd_valid_count = (read_state == PwoReadStatesType::PwoReadIdle || read_state == PwoReadStatesType::PwoReadStage)
          ? sc_uint<7>(0)
          : (sampler_valid ? sc_uint<7>(rd_valid_count + 1) : rd_valid_count);

      bf_enable_reg_d2_dummy = bf_enable_reg_d2_dummy && bf_enable_reg_d2;
      bf_enable_reg_d2 = bf_enable_reg;
      bf_enable_reg = (read_state == PwoReadStatesType::PwoReadExec || read_state == PwoReadStatesType::PwoReadExecWait)
          && sampler_valid;

      sc_uint<2> mem_rd_index_ofst = getMemRdIndexOfst(index_count, index_rand_offset);

      sc_uint<15> pw_mem_rd_addr_a_nxt = getPwAddrNxt(base_addrs.pw_base_addr_a,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> pw_mem_rd_addr_b_nxt = getPwAddrNxt(base_addrs.pw_base_addr_b,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> pw_mem_rd_addr_c_nxt = getPwAddrNxt(base_addrs.pw_base_addr_c,
        chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

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

      pw_mem_rd_addr_c_reg = getPwAddrCrd(shuffle_en,
        accumulate,
        rst_pw_addr,
        incr_pw_rd_addr,
        getPwAddrRst(shuffle_en, chunk_rand_offset, base_addrs.pw_base_addr_c),
        pw_mem_rd_addr_c_nxt,
        pw_mem_rd_addr_c_reg,
        PWO_READ_ADDR_STEP);
      pw_mem_rd_addr_c_out->set(pw_mem_rd_addr_c_reg);

      pw_rden_reg_dummy = pw_rden_reg_dummy && pw_rden_reg;
      pw_rden_reg = sampler_valid
      && (read_state == PwoReadStatesType::PwoReadExec || read_state == PwoReadStatesType::PwoReadExecWait);

      buf_rdptr_reg = (incr_pw_rd_addr || butterfly_ready)
          ? sc_uint<BUF_RDPTR_REG_SIZE>(
            (buf_rdptr_reg >> 2) | (sc_uint<BUF_RDPTR_REG_SIZE>(mem_rd_index_ofst) << (BUF_RDPTR_REG_SIZE - 2)))
          : sc_uint<BUF_RDPTR_REG_SIZE>(0);

      chunk_count_reg = (incr_pw_rd_addr || butterfly_ready)
          ? sc_uint<CHUNK_COUNT_REG_SIZE>(
            (chunk_count_reg >> 4) | (sc_uint<CHUNK_COUNT_REG_SIZE>(chunk_count) << (CHUNK_COUNT_REG_SIZE - 4)))
          : chunk_count_reg;

      read_state = next_state;
    }
  }

  [[noreturn]] void write() {
    write_state = PwoWriteStatesType::PwoWriteIdle;

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

      sc_uint<6> random;
      random_in->get(random);

      sc_uint<3> ntt_mode;
      ntt_mode_in->get(ntt_mode);

      PwoMemAddrs base_addrs;
      pwo_mem_base_addr_in->get(base_addrs);

      bool incr_pw_rd_addr = sampler_valid
          && (read_state == PwoReadStatesType::PwoReadExec || read_state == PwoReadStatesType::PwoReadExecWait);

      bool latch_index_rand_offset = incr_pw_rd_addr && index_count == 0x3;

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

      bool pwa_mode = ntt_mode == PWA_MODE;
      bool pws_mode = ntt_mode == PWS_MODE;

      sc_uint<4> chunk_count_reg_value = (accumulate
        ? chunk_count_reg.range((UNMASKED_PWM_LATENCY - 1) * 4 - 1, (UNMASKED_PWM_LATENCY - 2) * 4)
        : ((pwa_mode || pws_mode)
          ? chunk_count_reg.range(31, 28)
          : chunk_count_reg.range((UNMASKED_PWM_LATENCY) * 4 - 1, (UNMASKED_PWM_LATENCY - 1) * 4)));

      sc_uint<2> buf_rdptr_reg_value = (accumulate
        ? buf_rdptr_reg.range((UNMASKED_PWM_LATENCY - 1) * 2 - 1, (UNMASKED_PWM_LATENCY - 2) * 2)
        : ((pwa_mode || pws_mode)
          ? buf_rdptr_reg.range(15, 14)
          : buf_rdptr_reg.range((UNMASKED_PWM_LATENCY) * 2 - 1, (UNMASKED_PWM_LATENCY - 1) * 2)));

      sc_uint<15> pw_mem_wr_addr_c_nxt = getPwAddrNxt(base_addrs.pw_base_addr_c,
        chunk_count_reg_value,
        PWO_WRITE_ADDR_STEP,
        buf_rdptr_reg_value);

      bool incr_pw_wr_addr = (write_state == PwoWriteStatesType::PwoWriteMem && butterfly_ready)
          || (write_state == PwoWriteStatesType::PwoWriteWait && (shuffle_en || butterfly_ready));

      pw_mem_wr_addr_c_reg = getPwAddrAbcWr(rst_pw_addr,
        incr_pw_wr_addr,
        getPwAddrRst(shuffle_en, chunk_rand_offset, base_addrs.pw_base_addr_c),
        getPwAddrIncrAbcWr(shuffle_en, pw_mem_wr_addr_c_nxt, pw_mem_wr_addr_c_reg, PWO_WRITE_ADDR_STEP),
        pw_mem_wr_addr_c_reg);
      pw_mem_wr_addr_c_out->set(pw_mem_wr_addr_c_reg);

      chunk_rand_offset = latch_chunk_rand_offset ? random.range(5, 2) : chunk_rand_offset;

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

      sc_uint<3> ntt_mode;
      ntt_mode_in->get(ntt_mode);
      opcode_out->set(ntt_mode);
    }
  }
};

#endif
