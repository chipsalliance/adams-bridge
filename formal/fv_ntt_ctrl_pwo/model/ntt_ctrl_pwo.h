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

#include "Interfaces.h"

#define PWA_MODE 3
#define PWS_MODE 4
#define PWM_MODE 2
#define PAIRWM_MODE 5

#define PWO_READ_ADDR_STEP 1
#define PWO_WRITE_ADDR_STEP 1
#define UNMASKED_BF_LATENCY 10
// SRAM_DELAY = SRAM_LATENCY-1 (see ntt_ctrl.sv). Default 0 == SRAM_LATENCY=1;
// define SRAM_DELAY=1 (SRAM_LATENCY=2) before including this header to match a
// DUT elaborated with SRAM_LATENCY=2 -- MAX_RDPTR_REG_DEPTH/MAX_CHUNK_REG_DEPTH
// grow by SRAM_DELAY in the RTL, so these sizes must track it.
#ifndef SRAM_DELAY
#define SRAM_DELAY 0
#endif
#define BUF_RDPTR_REG_SIZE (2 * (UNMASKED_BF_LATENCY + 1 + SRAM_DELAY))
#define CHUNK_COUNT_REG_SIZE (4 * (UNMASKED_BF_LATENCY + 1 + SRAM_DELAY))
#define UNMASKED_PWM_LATENCY 5
#define BUF_RDPTR_REG_SIZE_NONPAIRWM (14 + 2 * SRAM_DELAY)
#define CHUNK_COUNT_REG_SIZE_NONPAIRWM (28 + 4 * SRAM_DELAY)



enum class pwoReadStatesType {
  fv_pwo_read_idle_type,
  fv_pwo_read_stage_type,
  fv_pwo_read_exec_type,
  fv_pwo_read_exec_wait_type
};


enum class pwoWriteStatesType {
  fv_pwo_write_idle_type,
  fv_pwo_write_stage_type,
  fv_pwo_write_wait_type,
  fv_pwo_write_mem_type
};


struct fv_pwo_mem_addrs_type {
  sc_uint<15> pw_base_addr_a;
  sc_uint<15> pw_base_addr_b;
  sc_uint<15> pw_base_addr_c;
};


sc_uint<2> get_mem_rd_index_ofst(sc_uint<2> fv_index_count, sc_uint<2> fv_index_rand_offset) {
  return fv_index_count + fv_index_rand_offset;
}

sc_uint<4> get_chunk_rand_offset_from_random(sc_uint<6> random) {
  return random.range(5, 2);
}

sc_uint<2> get_index_rand_offset_from_random(sc_uint<6> random) {
  return random.range(1, 0);
}

sc_uint<BUF_RDPTR_REG_SIZE> get_buf_rdptr_reg_next_pairwm(sc_uint<BUF_RDPTR_REG_SIZE> fv_buf_rdptr_reg, sc_uint<2> mem_rd_index_ofst) {
  return (fv_buf_rdptr_reg >> 2) | (sc_uint<BUF_RDPTR_REG_SIZE>(mem_rd_index_ofst) << (BUF_RDPTR_REG_SIZE - 2));
}

sc_uint<BUF_RDPTR_REG_SIZE_NONPAIRWM> get_buf_rdptr_reg_next_nonpairwm(sc_uint<BUF_RDPTR_REG_SIZE> fv_buf_rdptr_reg, sc_uint<2> mem_rd_index_ofst) {
  return sc_uint<BUF_RDPTR_REG_SIZE_NONPAIRWM>(
    (fv_buf_rdptr_reg.range(BUF_RDPTR_REG_SIZE_NONPAIRWM - 1, 0) >> 2)
    | (sc_uint<BUF_RDPTR_REG_SIZE_NONPAIRWM>(mem_rd_index_ofst) << (BUF_RDPTR_REG_SIZE_NONPAIRWM - 2)));
}

sc_uint<CHUNK_COUNT_REG_SIZE> get_chunk_count_reg_next_pairwm(sc_uint<CHUNK_COUNT_REG_SIZE> fv_chunk_count_reg, sc_uint<4> fv_chunk_count) {
  return (fv_chunk_count_reg >> 4) | (sc_uint<CHUNK_COUNT_REG_SIZE>(fv_chunk_count) << (CHUNK_COUNT_REG_SIZE - 4));
}

sc_uint<CHUNK_COUNT_REG_SIZE_NONPAIRWM> get_chunk_count_reg_next_nonpairwm(sc_uint<CHUNK_COUNT_REG_SIZE> fv_chunk_count_reg, sc_uint<4> fv_chunk_count) {
  return sc_uint<CHUNK_COUNT_REG_SIZE_NONPAIRWM>(
    (fv_chunk_count_reg.range(CHUNK_COUNT_REG_SIZE_NONPAIRWM - 1, 0) >> 4)
    | (sc_uint<CHUNK_COUNT_REG_SIZE_NONPAIRWM>(fv_chunk_count) << (CHUNK_COUNT_REG_SIZE_NONPAIRWM - 4)));
}

sc_uint<15> get_pw_addr_rst(bool shuffle_en, sc_uint<4> fv_chunk_rand_offset, sc_uint<15> base_addr) {
  if (shuffle_en) {
    return 4 * fv_chunk_rand_offset + base_addr;
  }

  return base_addr;
}

sc_uint<15> get_pw_addr_incr_abc_wr(bool shuffle_en, sc_uint<15> addr_nxt, sc_uint<15> current_addr, sc_uint<15> addr_step) {
  if (shuffle_en) {
    return addr_nxt;
  }

  return current_addr + addr_step;
}

sc_uint<15> get_pw_addr_abc_wr(bool rst_addr, bool incr_addr, sc_uint<15> addr_rst, sc_uint<15> addr_incr,
  sc_uint<15> addr_default) {
  if (rst_addr) {
    return addr_rst;
  }

  if (incr_addr) {
    return addr_incr;
  }

  return addr_default;
}

sc_uint<15> get_pw_addr_crd(bool shuffle_en, bool mode,bool accumulate, bool rst_pw_addr, bool incr_pw_rd_addr, sc_uint<15> addr_rst,
  sc_uint<15> addr_nxt, sc_uint<15> addr_default, sc_uint<15> addr_step) {
  if (rst_pw_addr) {
    if (shuffle_en) {
    return addr_rst;
    }
    return addr_default;
  }

  if (mode && accumulate) {
    if(incr_pw_rd_addr)
    {
    if (shuffle_en) {
        return addr_nxt;
    }
      return addr_default + addr_step;  
  }
  return addr_default;
  }

  return sc_uint<15>(0);
}

sc_uint<15> get_pw_addr_cwr(bool rst_pw_addr, bool incr_pw_wr_addr, bool shuffle_en, sc_uint<4> fv_chunk_rand_offset,
  sc_uint<15> pw_base_addr_c, sc_uint<15> shuffled_pw_mem_wr_addr_c_nxt, sc_uint<15> pw_mem_wr_addr_c) {
  if (rst_pw_addr) {
    if (shuffle_en) {
      return 4 * fv_chunk_rand_offset + pw_base_addr_c;
    }

    return pw_base_addr_c;
  }

  if (incr_pw_wr_addr) {
    if (shuffle_en) {
      return shuffled_pw_mem_wr_addr_c_nxt;
    }

    return pw_mem_wr_addr_c + PWO_WRITE_ADDR_STEP;
  }

  return pw_mem_wr_addr_c;
}

sc_uint<15> get_pw_addr_nxt(sc_uint<15> base_addr, sc_uint<4> fv_chunk_count, sc_uint<15> step, sc_uint<15> offset) {
  return base_addr + 4 * fv_chunk_count + step * offset;
}
sc_uint<15> get_pw_addr_wr_nxt(sc_uint<15> base_addr, sc_uint<CHUNK_COUNT_REG_SIZE> fv_chunk_count_reg, sc_uint<15> step,
  sc_uint<BUF_RDPTR_REG_SIZE> fv_buf_rdptr_reg, bool accumulate, sc_uint<3> mode) {
  if (mode == PWA_MODE || mode == PWS_MODE) {
    
    return base_addr + 4 * fv_chunk_count_reg.range(15,12)
      + step * fv_buf_rdptr_reg.range(7,6);
  }
  else if(mode==PWM_MODE) {
  if (accumulate) {
    return base_addr + 4 * fv_chunk_count_reg.range(7, 4)
      + step * fv_buf_rdptr_reg.range(3, 2);
  }

  
  return base_addr + 4 * fv_chunk_count_reg.range(11, 8)
    + step * fv_buf_rdptr_reg.range(5, 4);
}
if (accumulate) {
    return base_addr + 4 * fv_chunk_count_reg.range(15, 12)
      + step * fv_buf_rdptr_reg.range(7,6);
  }

  
  return base_addr + 4 * fv_chunk_count_reg.range(19, 16)
    + step * fv_buf_rdptr_reg.range(9,8);
}

// Non-pairwm (pwa/pws/pwm) taps fv_chunk_count_reg at RTL's BF_LATENCY (=6, bits [27:24]).
// buf_wrptr_reg (non-pairwm) and buf_rdptr_int/buf_count (pairwm) are both provably 0 in
// this unit and dropped -- see the model's notes on assume_ntt_mode (gs_mode always 0)
// and the buf_wren/pwo_mode tie-off (buf0_valid always 0).

std::array<sc_uint<7>, 8> get_twiddle_rand_offsets(sc_uint<CHUNK_COUNT_REG_SIZE> fv_chunk_count_reg,
  sc_uint<4> fv_chunk_count, sc_uint<2> buf_count, bool pairwm_mode) {
  return std::array<sc_uint<7>, 8>{
    (pairwm_mode ? sc_uint<7>(fv_chunk_count * 4 + buf_count) : sc_uint<7>(fv_chunk_count_reg.range(27, 24) * 4)),
    sc_uint<7>((fv_chunk_count_reg.range(27, 24) & 0x3) * 4),
    0,
    0,
    0,
    0,
    0,
    0
  };
}

sc_uint<7> get_twiddle_addr_reg(bool incr, bool rst, sc_uint<7> incr_addr, sc_uint<7> default_addr) { //no change, line 570-573
  if (incr) {
    return incr_addr;
  }

  if (rst) {
    return sc_uint<7>(0);
  }

  return default_addr;
}

sc_uint<7> get_twiddle_incr_addr(bool shuffle_en, sc_uint<3> fv_rounds_count, std::array<sc_uint<7>, 8> rand_offsets, //line 571, no change
  std::array<sc_uint<7>, 8> end_addrs, sc_uint<7> default_addr) {
  if (shuffle_en) {
    return rand_offsets[fv_rounds_count];
  }

  if (default_addr == end_addrs[fv_rounds_count]) {
    return sc_uint<7>(0);
  }

  return default_addr + 1;
}

SC_MODULE(ntt_ctrl) {
public:
  SC_CTOR(ntt_ctrl) {
    SC_THREAD(read)
    SC_THREAD(write)
    SC_THREAD(commons)
  }

  shared_in<sc_uint<3>> fv_ntt_mode_in;
  shared_in<bool> fv_ntt_enable_in;
  shared_in<bool> fv_butterfly_ready_in;
  shared_in<bool> fv_sampler_valid_in;
  shared_in<bool> fv_accumulate_in;
  shared_in<bool> fv_shuffle_en_in;
  shared_in<fv_pwo_mem_addrs_type> fv_pwo_mem_base_addr_in;
  shared_in<sc_uint<6>> fv_random_in;
  shared_in<sc_uint<1>> fv_mlkem_in;
  // Write custom property, as bf_enable combinationally depends on shuffle_en
  // shared_out<bool> bf_enable_out;
  shared_out<sc_uint<3>> fv_opcode_out;
  //shared_out<bool> masking_en_ctrl_out;
  shared_out<bool> fv_buf_wren_out;
  shared_out<bool> fv_buf_rden_out;
  shared_out<sc_uint<2>> fv_buf_wrptr_out;
  shared_out<sc_uint<2>> fv_buf_rdptr_out;
  shared_out<bool> fv_mem_rd_en_out;
  shared_out<bool> fv_mem_wr_en_out;
  shared_out<bool> fv_buf_wr_rst_count_out;
  shared_out<bool> fv_buf_rd_rst_count_out;
  shared_out<sc_uint<15>> fv_pw_mem_rd_addr_a_out;
  shared_out<sc_uint<15>> fv_pw_mem_rd_addr_b_out;
  shared_out<sc_uint<15>> fv_pw_mem_rd_addr_c_out;
  shared_out<sc_uint<15>> fv_pw_mem_wr_addr_c_out;
  // Write custom property, as pw_rden combinationally depends on shuffle_en
  // shared_out<bool> pw_rden_out;
  // Write custom property, as pw_wren combinationally depends on shuffle_en
  // shared_out<bool> pw_wren_out;
  // Write custom property, as busy combinationally depends on both processes
  // shared_out<bool> busy_out;
  shared_out<bool> fv_done_out;
  // Write custom property, as twiddle_addr combinationally depends on shuffle_en
  // shared_out<sc_uint<7>> twiddle_addr_out;

  // Write a custom property for this signal, as it combinationally depends on both processes
  shared_in<bool> fv_rst_rounds_in;


private:
  pwoReadStatesType fv_read_state;
  pwoWriteStatesType fv_write_state;

  sc_uint<3> fv_rounds_count;
  sc_uint<7> fv_rd_valid_count;
  sc_uint<7> fv_wr_valid_count;
  sc_uint<2> fv_index_count;
  sc_uint<2> fv_index_rand_offset;
  sc_uint<4> fv_chunk_count;
  sc_uint<4> fv_chunk_rand_offset;
  sc_uint<15> fv_pw_mem_rd_addr_a_reg;
  sc_uint<15> fv_pw_mem_rd_addr_b_reg;
  sc_uint<15> fv_pw_mem_rd_addr_c_reg;
  sc_uint<15> fv_pw_mem_wr_addr_c_reg;

  sc_uint<BUF_RDPTR_REG_SIZE> fv_buf_rdptr_reg;
  sc_uint<CHUNK_COUNT_REG_SIZE> fv_chunk_count_reg;

   sc_uint<7> fv_twiddle_addr_int;
  sc_uint<7> fv_twiddle_addr_reg;
  sc_uint<7> fv_twiddle_addr_reg_d2;
  sc_uint<7> fv_twiddle_addr_reg_d3;
  sc_uint<7> fv_twiddle_addr_reg_d3_dummy;
  bool fv_incr_twiddle_addr_reg;
  bool fv_rst_twiddle_addr;
  bool fv_bf_enable_reg;
  //bool fv_bf_enable_reg_d2;
  //bool fv_bf_enable_reg_d2_dummy;
  bool fv_pw_rden_reg;
  //bool fv_pw_rden_reg_dummy;
  bool fv_pw_wren_reg;
  //bool fv_pw_wren_reg_dummy;

  [[noreturn]] void read() {
    fv_read_state = pwoReadStatesType::fv_pwo_read_idle_type;

    pwoReadStatesType next_state = pwoReadStatesType::fv_pwo_read_idle_type;
    bool incr_pw_rd_addr = false;

    while (true) {
      if (fv_read_state == pwoReadStatesType::fv_pwo_read_idle_type) {
        insert_state("fv_read_idle");
        next_state = pwoReadStatesType::fv_pwo_read_idle_type;
        incr_pw_rd_addr = false;

        bool ntt_enable = false;
        fv_ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = pwoReadStatesType::fv_pwo_read_stage_type;
        }
      } else if (fv_read_state == pwoReadStatesType::fv_pwo_read_stage_type) {
        insert_state("fv_read_stage");
        next_state = pwoReadStatesType::fv_pwo_read_stage_type;
        incr_pw_rd_addr = false;

        bool ntt_enable = false;
        fv_ntt_enable_in->get(ntt_enable);

        if (fv_rounds_count == 1 && !ntt_enable) {
          next_state = pwoReadStatesType::fv_pwo_read_idle_type;
        } else if (fv_write_state == pwoWriteStatesType::fv_pwo_write_stage_type && fv_rounds_count != 1) {
          next_state = pwoReadStatesType::fv_pwo_read_exec_type;
        }
      } else if (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type) {
        insert_state("fv_read_exec");
        next_state = pwoReadStatesType::fv_pwo_read_exec_type;

        bool sampler_valid = false;
        fv_sampler_valid_in->get(sampler_valid);

        incr_pw_rd_addr = sampler_valid;

        if (!sampler_valid && fv_rd_valid_count < 0x40) {
          next_state = pwoReadStatesType::fv_pwo_read_exec_wait_type;
        } else if (fv_rd_valid_count >= 0x3F) {
          next_state = pwoReadStatesType::fv_pwo_read_stage_type;
        }
      } else {
        // if (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type) {
        insert_state("fv_read_exec_wait");
        next_state = pwoReadStatesType::fv_pwo_read_exec_wait_type;

        bool sampler_valid = false;
        fv_sampler_valid_in->get(sampler_valid);

        incr_pw_rd_addr = sampler_valid && (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type || fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type);

        if (sampler_valid) {
          next_state = pwoReadStatesType::fv_pwo_read_exec_type;
        }
        
        }
      
      

      bool shuffle_en = false;
      fv_shuffle_en_in->get(shuffle_en);

      bool sampler_valid = false;
      fv_sampler_valid_in->get(sampler_valid);

      bool accumulate = false;
      fv_accumulate_in->get(accumulate);

      bool butterfly_ready = false;
      fv_butterfly_ready_in->get(butterfly_ready);

      fv_pwo_mem_addrs_type base_addrs;
      fv_pwo_mem_base_addr_in->get(base_addrs);

       bool rst_rounds = false;
      fv_rst_rounds_in->get(rst_rounds);

    

      fv_rd_valid_count = (fv_read_state == pwoReadStatesType::fv_pwo_read_idle_type || fv_read_state == pwoReadStatesType::fv_pwo_read_stage_type)
          ? sc_uint<7>(0)
          : (sampler_valid ? sc_uint<7>(fv_rd_valid_count + 1) : fv_rd_valid_count);

      //fv_bf_enable_reg_d2_dummy = fv_bf_enable_reg_d2_dummy && fv_bf_enable_reg_d2;
      //fv_bf_enable_reg_d2 = fv_bf_enable_reg;
      fv_bf_enable_reg = (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type || fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type)
          && sampler_valid;

      sc_uint<2> mem_rd_index_ofst = get_mem_rd_index_ofst(fv_index_count, fv_index_rand_offset);

      sc_uint<15> pw_mem_rd_addr_a_nxt = get_pw_addr_nxt(base_addrs.pw_base_addr_a,
        fv_chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> pw_mem_rd_addr_b_nxt = get_pw_addr_nxt(base_addrs.pw_base_addr_b,
        fv_chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

      sc_uint<15> pw_mem_rd_addr_c_nxt = get_pw_addr_nxt(base_addrs.pw_base_addr_c,
        fv_chunk_count,
        PWO_READ_ADDR_STEP,
        mem_rd_index_ofst);

        sc_uint<3> ntt_mode;
      fv_ntt_mode_in->get(ntt_mode);

      sc_uint<1> mlkem;
      fv_mlkem_in->get(mlkem);

      bool rst_pw_addr =
          fv_write_state == pwoWriteStatesType::fv_pwo_write_idle_type || fv_write_state == pwoWriteStatesType::fv_pwo_write_stage_type;

      fv_pw_mem_rd_addr_a_reg = get_pw_addr_abc_wr(rst_pw_addr,
        incr_pw_rd_addr,
        get_pw_addr_rst(shuffle_en, fv_chunk_rand_offset, base_addrs.pw_base_addr_a),
        get_pw_addr_incr_abc_wr(shuffle_en, pw_mem_rd_addr_a_nxt, fv_pw_mem_rd_addr_a_reg, PWO_READ_ADDR_STEP),
        fv_pw_mem_rd_addr_a_reg);
      fv_pw_mem_rd_addr_a_out->set(fv_pw_mem_rd_addr_a_reg);

      fv_pw_mem_rd_addr_b_reg = get_pw_addr_abc_wr(rst_pw_addr,
        incr_pw_rd_addr,
        get_pw_addr_rst(shuffle_en, fv_chunk_rand_offset, base_addrs.pw_base_addr_b),
        get_pw_addr_incr_abc_wr(shuffle_en, pw_mem_rd_addr_b_nxt, fv_pw_mem_rd_addr_b_reg, PWO_READ_ADDR_STEP),
        fv_pw_mem_rd_addr_b_reg);
      fv_pw_mem_rd_addr_b_out->set(fv_pw_mem_rd_addr_b_reg);

      fv_pw_mem_rd_addr_c_reg = get_pw_addr_crd(shuffle_en,(ntt_mode== PWM_MODE|| (mlkem && ntt_mode== PAIRWM_MODE)),
        accumulate,
        rst_pw_addr,
        incr_pw_rd_addr,
        get_pw_addr_rst(shuffle_en, fv_chunk_rand_offset, base_addrs.pw_base_addr_c),
        pw_mem_rd_addr_c_nxt,
        fv_pw_mem_rd_addr_c_reg,
        PWO_READ_ADDR_STEP);
      fv_pw_mem_rd_addr_c_out->set(fv_pw_mem_rd_addr_c_reg);

      //fv_pw_rden_reg_dummy = fv_pw_rden_reg_dummy && fv_pw_rden_reg;
      fv_pw_rden_reg = sampler_valid
      && (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type || fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type);

      bool pairwm_mode = mlkem && (ntt_mode == PAIRWM_MODE);

      fv_buf_rdptr_reg = (incr_pw_rd_addr || butterfly_ready)
          ? (pairwm_mode
            ? get_buf_rdptr_reg_next_pairwm(fv_buf_rdptr_reg, mem_rd_index_ofst)
            : sc_uint<BUF_RDPTR_REG_SIZE>(get_buf_rdptr_reg_next_nonpairwm(fv_buf_rdptr_reg, mem_rd_index_ofst)))
          : sc_uint<BUF_RDPTR_REG_SIZE>(0);

      // Read fv_chunk_count_reg for twiddle_rand_offset_array before it's updated below --
      // design's twiddle_rand_offset is combinational off the pre-edge fv_chunk_count_reg.
      std::array<sc_uint<7>, 8> twiddle_rand_offset_array = get_twiddle_rand_offsets(fv_chunk_count_reg,
        fv_chunk_count,
        0,
        pairwm_mode);

      fv_chunk_count_reg = (incr_pw_rd_addr || butterfly_ready)
          ? (pairwm_mode
            ? get_chunk_count_reg_next_pairwm(fv_chunk_count_reg, fv_chunk_count)
            : sc_uint<CHUNK_COUNT_REG_SIZE>(get_chunk_count_reg_next_nonpairwm(fv_chunk_count_reg, fv_chunk_count)))
          : fv_chunk_count_reg;

      std::array<sc_uint<7>, 8> twiddle_end_addr_array = {
        63, 15, 3, 0, 0, 0, 0, 0
      };

      std::array<sc_uint<7>, 8> twiddle_offset_array = {
        (pairwm_mode ? sc_uint<7>(21) : sc_uint<7>(0)), 64, 80, 84, 0, 0, 0, 0
      };
      
      
      // fv_twiddle_addr_reg == design's fv_twiddle_addr_reg[0] (comb, zero delay off fv_twiddle_addr_int).
      // fv_twiddle_addr_reg[0] and the final twiddle_addr output are both combinational, so they're
      // checked via a custom property (assert_twiddle_addr_p) instead of through this model.
      fv_twiddle_addr_reg = !shuffle_en ? sc_uint<7>(fv_twiddle_addr_int + twiddle_offset_array[fv_rounds_count])
          : (shuffle_en && pairwm_mode) ?
            sc_uint<7>(twiddle_rand_offset_array[fv_rounds_count] + sc_uint<2>((fv_index_count + fv_index_rand_offset) % 4) + twiddle_offset_array[fv_rounds_count])
          : sc_uint<7>(twiddle_rand_offset_array[fv_rounds_count] + twiddle_offset_array[fv_rounds_count]);

     // fv_twiddle_addr_reg_d3_dummy = fv_twiddle_addr_reg_d3_dummy + fv_twiddle_addr_reg_d3;
      fv_twiddle_addr_reg_d3 = fv_twiddle_addr_reg_d2;
      fv_twiddle_addr_reg_d2 = fv_twiddle_addr_reg;

      fv_twiddle_addr_int = get_twiddle_addr_reg(fv_incr_twiddle_addr_reg,
        fv_read_state == pwoReadStatesType::fv_pwo_read_idle_type
        || (fv_read_state == pwoReadStatesType::fv_pwo_read_stage_type && !butterfly_ready),
        get_twiddle_incr_addr(shuffle_en,
          fv_rounds_count,
          twiddle_rand_offset_array,
          twiddle_end_addr_array,
          fv_twiddle_addr_int),
        fv_twiddle_addr_int);

      fv_incr_twiddle_addr_reg = (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type || fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type) && (pairwm_mode && sampler_valid);
      fv_read_state = next_state;
    }
  }

  [[noreturn]] void write() {
    fv_write_state = pwoWriteStatesType::fv_pwo_write_idle_type;

    pwoWriteStatesType next_state;
    bool incr_rounds = false;
    bool latch_fv_chunk_rand_offset = false;
    bool rst_pw_addr = false;

    while (true) {
      if (fv_write_state == pwoWriteStatesType::fv_pwo_write_idle_type) {
        insert_state("fv_write_idle");
        next_state = pwoWriteStatesType::fv_pwo_write_idle_type;
        incr_rounds = false;
        latch_fv_chunk_rand_offset = false;
        rst_pw_addr = true;

        bool ntt_enable = false;
        fv_ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = pwoWriteStatesType::fv_pwo_write_stage_type;
          latch_fv_chunk_rand_offset = true;
        }
      } else if (fv_write_state == pwoWriteStatesType::fv_pwo_write_stage_type) {
        insert_state("fv_write_stage");
        incr_rounds = false;
        latch_fv_chunk_rand_offset = false;
        rst_pw_addr = true;

        bool shuffle_en = false;
        fv_shuffle_en_in->get(shuffle_en);

        if (fv_rounds_count == 1) {
          next_state = pwoWriteStatesType::fv_pwo_write_idle_type;
        } else if (shuffle_en) {
          next_state = pwoWriteStatesType::fv_pwo_write_mem_type;
        } else {
          next_state = pwoWriteStatesType::fv_pwo_write_wait_type;
        }
      } else if (fv_write_state == pwoWriteStatesType::fv_pwo_write_wait_type) {
        insert_state("fv_write_wait");
        next_state = pwoWriteStatesType::fv_pwo_write_wait_type;
        incr_rounds = false;
        latch_fv_chunk_rand_offset = false;
        rst_pw_addr = false;

        bool shuffle_en = false;
        fv_shuffle_en_in->get(shuffle_en);

        bool butterfly_ready = false;
        fv_butterfly_ready_in->get(butterfly_ready);

        if (shuffle_en) {
          next_state = pwoWriteStatesType::fv_pwo_write_stage_type;
          incr_rounds = true;
          latch_fv_chunk_rand_offset = true;
        } else if (butterfly_ready) {
          next_state = pwoWriteStatesType::fv_pwo_write_mem_type;
        }
      } else {
        // if (fv_write_state == pwoWriteStatesType::fv_pwo_write_mem_type) {
        insert_state("fv_write_mem");
        next_state = pwoWriteStatesType::fv_pwo_write_mem_type;
        incr_rounds = false;
        latch_fv_chunk_rand_offset = false;
        rst_pw_addr = false;

        bool shuffle_en = false;
        fv_shuffle_en_in->get(shuffle_en);

        bool butterfly_ready = false;
        fv_butterfly_ready_in->get(butterfly_ready);

        if ((!shuffle_en && !butterfly_ready && fv_wr_valid_count < 0x40)
          || (shuffle_en && butterfly_ready && fv_wr_valid_count == 0x3F)) {
          next_state = pwoWriteStatesType::fv_pwo_write_wait_type;
        } else if (!shuffle_en && fv_wr_valid_count == 0x40) {
          next_state = pwoWriteStatesType::fv_pwo_write_stage_type;
          incr_rounds = true;
          latch_fv_chunk_rand_offset = true;
        }
      }

      bool rst_rounds = false;
      fv_rst_rounds_in->get(rst_rounds);

      bool butterfly_ready = false;
      fv_butterfly_ready_in->get(butterfly_ready);

      bool shuffle_en = false;
      fv_shuffle_en_in->get(shuffle_en);

      bool sampler_valid = false;
      fv_sampler_valid_in->get(sampler_valid);

      bool accumulate = false;
      fv_accumulate_in->get(accumulate);

      sc_uint<6> random;
      fv_random_in->get(random);

      sc_uint<3> ntt_mode;
      fv_ntt_mode_in->get(ntt_mode);

      fv_pwo_mem_addrs_type base_addrs;
      fv_pwo_mem_base_addr_in->get(base_addrs);

      bool incr_pw_rd_addr = sampler_valid
          && (fv_read_state == pwoReadStatesType::fv_pwo_read_exec_type || fv_read_state == pwoReadStatesType::fv_pwo_read_exec_wait_type);

      bool latch_fv_index_rand_offset = incr_pw_rd_addr && fv_index_count == 0x3;

      fv_rounds_count = rst_rounds
          ? sc_uint<3>(0)
          : ((incr_rounds && fv_rounds_count < 1)
            ? sc_uint<3>(fv_rounds_count + 1)
            : (fv_rounds_count == 1 ? sc_uint<3>(0) : fv_rounds_count));
      fv_done_out->set(fv_rounds_count == 1);

      fv_wr_valid_count = (fv_write_state == pwoWriteStatesType::fv_pwo_write_idle_type
            || fv_write_state == pwoWriteStatesType::fv_pwo_write_stage_type)
          ? sc_uint<7>(0)
          : (butterfly_ready ? sc_uint<7>(fv_wr_valid_count + 1) : fv_wr_valid_count);

      //fv_pw_wren_reg_dummy = fv_pw_wren_reg_dummy && fv_pw_wren_reg;
      fv_pw_wren_reg = (fv_write_state == pwoWriteStatesType::fv_pwo_write_mem_type && butterfly_ready)
          || (fv_write_state == pwoWriteStatesType::fv_pwo_write_wait_type && butterfly_ready && !shuffle_en);

      fv_chunk_count = latch_fv_chunk_rand_offset
          ? get_chunk_rand_offset_from_random(random)
          : ((incr_pw_rd_addr && fv_index_count == 0x3) ? sc_uint<4>(fv_chunk_count + 1) : fv_chunk_count);
        //need to modify?
      fv_index_rand_offset = latch_fv_index_rand_offset ? get_index_rand_offset_from_random(random) : fv_index_rand_offset;

      fv_index_count = incr_pw_rd_addr ? sc_uint<2>(fv_index_count + 1) : fv_index_count;

      bool pwa_mode = ntt_mode == PWA_MODE;
      bool pws_mode = ntt_mode == PWS_MODE;
sc_uint<2> mem_rd_index_ofst = get_mem_rd_index_ofst(fv_index_count, fv_index_rand_offset);
    

      sc_uint<15> pw_mem_wr_addr_c_nxt = get_pw_addr_wr_nxt(base_addrs.pw_base_addr_c,
        fv_chunk_count_reg,
        PWO_WRITE_ADDR_STEP,
        fv_buf_rdptr_reg,accumulate,ntt_mode);

      bool incr_pw_wr_addr = (fv_write_state == pwoWriteStatesType::fv_pwo_write_mem_type && butterfly_ready)
          || (fv_write_state == pwoWriteStatesType::fv_pwo_write_wait_type && (shuffle_en || butterfly_ready));

      fv_pw_mem_wr_addr_c_reg = get_pw_addr_cwr(rst_pw_addr,
        incr_pw_wr_addr,
        shuffle_en,
        fv_chunk_rand_offset,
        base_addrs.pw_base_addr_c,
        pw_mem_wr_addr_c_nxt,
        fv_pw_mem_wr_addr_c_reg);
      fv_pw_mem_wr_addr_c_out->set(fv_pw_mem_wr_addr_c_reg);

      fv_chunk_rand_offset = latch_fv_chunk_rand_offset ? get_chunk_rand_offset_from_random(random) : fv_chunk_rand_offset;

      fv_write_state = next_state;
    }
  }

  [[noreturn]] void commons() {
    fv_buf_wren_out->set(false);
    fv_buf_rden_out->set(false);
    fv_buf_wrptr_out->set(sc_uint<2>(0));
    fv_buf_rdptr_out->set(sc_uint<2>(0));
    fv_mem_rd_en_out->set(false);
    fv_mem_wr_en_out->set(false);
    fv_buf_wr_rst_count_out->set(true);
    fv_buf_rd_rst_count_out->set(true);

    while (true) {
      insert_state();

      sc_uint<3> ntt_mode;
      sc_uint<1> mlkem;
      fv_ntt_mode_in->get(ntt_mode);
      fv_opcode_out->set(ntt_mode);
      fv_mlkem_in->get(mlkem);
    }
  }
};

#endif
