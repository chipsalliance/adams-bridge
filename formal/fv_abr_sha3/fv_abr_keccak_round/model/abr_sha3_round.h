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

#ifndef ABR_SH3_H
#define ABR_SH3_H

#include <array>
#include "Interfaces.h"

#define PERMUTATION_WIDTH 1600
#define LANE_SIZE 64
#define ROUNDS_PER_CLOCK 2
#define CYCLES_PER_RUN (24 / ROUNDS_PER_CLOCK)

#define STRING_TYPE sc_biguint<PERMUTATION_WIDTH>
#define LANE_TYPE sc_biguint<LANE_SIZE>
#define STATE_TYPE std::array<std::array<LANE_TYPE, 5>, 5>

const std::array<std::array<int, 5>, 5> rho_offsets = {
  std::array<int, 5>{  0, 36,  3, 41, 18 },
  std::array<int, 5>{  1, 44, 10, 45,  2 },
  std::array<int, 5>{ 62,  6, 43, 15, 61 },
  std::array<int, 5>{ 28, 55, 25, 21, 56 },
  std::array<int, 5>{ 27, 20, 39,  8, 14 }
};

const std::array<LANE_TYPE, 24> rc_values = {
  0x0000000000000001u, 0x0000000000008082u, 0x800000000000808au, 0x8000000080008000u,
  0x000000000000808bu, 0x0000000080000001u, 0x8000000080008081u, 0x8000000000008009u,
  0x000000000000008au, 0x0000000000000088u, 0x0000000080008009u, 0x000000008000000au,
  0x000000008000808bu, 0x800000000000008bu, 0x8000000000008089u, 0x8000000000008003u,
  0x8000000000008002u, 0x8000000000000080u, 0x000000000000800au, 0x800000008000000au,
  0x8000000080008081u, 0x8000000000008080u, 0x0000000080000001u, 0x8000000080008008u
};

LANE_TYPE rotateLeft(LANE_TYPE lane, int positions) {
  return (lane << positions) | (lane >> (LANE_SIZE - positions));
}

STATE_TYPE stringToState(STRING_TYPE str) {
  STATE_TYPE new_state;

  for (int row_idx = 0; row_idx < 5; ++row_idx) {
    for (int col_idx = 0; col_idx < 5; ++col_idx) {
      new_state[col_idx][row_idx] = static_cast<LANE_TYPE>(str);
      str >>= LANE_SIZE;
    }
  }

  return new_state;
}

STRING_TYPE stateToString(STATE_TYPE state) {
  STRING_TYPE new_string;

  for (int row_idx = 4; row_idx >= 0; --row_idx) {
    for (int col_idx = 4; col_idx >= 0; --col_idx) {
      new_string <<= LANE_SIZE;
      new_string |= state[col_idx][row_idx];
    }
  }

  return new_string;
}

STATE_TYPE theta(STATE_TYPE original_state) {
  std::array<LANE_TYPE, 5> C;
  for (int col_idx = 0; col_idx < 5; ++col_idx) {
    C[col_idx] = original_state[col_idx][0] ^ original_state[col_idx][1] ^ original_state[col_idx][2]
        ^ original_state[col_idx][3] ^ original_state[col_idx][4];
  }

  std::array<LANE_TYPE, 5> D;
  for (int col_idx = 0; col_idx < 5; ++col_idx) {
    D[col_idx] = C[(col_idx + 4) % 5] ^ rotateLeft(C[(col_idx + 1) % 5], 1);
  }

  STATE_TYPE new_state;
  for (int row_idx = 0; row_idx < 5; ++row_idx) {
    for (int col_idx = 0; col_idx < 5; ++col_idx) {
      new_state[col_idx][row_idx] = original_state[col_idx][row_idx] ^ D[col_idx];
    }
  }

  return new_state;
}

STATE_TYPE rho(STATE_TYPE original_state) {
  STATE_TYPE new_state;
  for (int row_idx = 0; row_idx < 5; ++row_idx) {
    for (int col_idx = 0; col_idx < 5; ++col_idx) {
      new_state[col_idx][row_idx] = rotateLeft(original_state[col_idx][row_idx], rho_offsets[col_idx][row_idx]);
    }
  }

  return new_state;
}

STATE_TYPE pi(STATE_TYPE original_state) {
  STATE_TYPE new_state;
  for (int row_idx = 0; row_idx < 5; ++row_idx) {
    for (int col_idx = 0; col_idx < 5; ++col_idx) {
      new_state[col_idx][row_idx] = original_state[(col_idx + 3 * row_idx) % 5][col_idx];
    }
  }

  return new_state;
}

STATE_TYPE chi(STATE_TYPE original_state) {
  STATE_TYPE new_state;
  for (int row_idx = 0; row_idx < 5; ++row_idx) {
    for (int col_idx = 0; col_idx < 5; ++col_idx) {
      new_state[col_idx][row_idx] = original_state[col_idx][row_idx]
          ^ (~original_state[(col_idx + 1) % 5][row_idx] & original_state[(col_idx + 2) % 5][row_idx]);
    }
  }

  return new_state;
}

STATE_TYPE iota(STATE_TYPE original_state, int round_idx) {
  original_state[0][0] ^= rc_values[round_idx];

  return original_state;
}

SC_MODULE(abr_sha3_round) {
public:
  SC_CTOR(abr_sha3_round) {
    SC_THREAD(fsm)
  }

  blocking_in<STRING_TYPE> data_in;
  shared_in<bool> clear_in;
  shared_in<bool> squeezing_in;
  shared_out<STRING_TYPE> state_out;
  shared_out<bool> complete_out;

  shared_out<bool> rand_consumed_out;
  shared_out<bool> sparse_fsm_error_out;
  shared_out<bool> round_count_error_out;
  shared_out<bool> rst_storage_error_out;


private:
  STRING_TYPE storage;

  void fsm() {
    state_out->set(0);
    complete_out->set(false);

    rand_consumed_out->set(false);
    sparse_fsm_error_out->set(false);
    round_count_error_out->set(false);
    rst_storage_error_out->set(false);

    while (true) {
      STRING_TYPE input_string = 0;
      bool input_valid = false;
      bool clear = false;
      do {
        data_in->try_read(input_string, input_valid, "waiting_for_input");

        clear_in->get(clear);
        if (clear) {
          storage = 0;
          state_out->set(0);
        }

        complete_out->set(false);
      } while (clear || !input_valid);

      bool squeezing = false;
      squeezing_in->get(squeezing);

      if (!squeezing) {
        storage ^= input_string;
        state_out->set(storage);
      }

      int round_idx = 0;
      for (; round_idx < 24; round_idx += ROUNDS_PER_CLOCK) {
        insert_state("round_state");
        
        STATE_TYPE current_state = stringToState(storage);

        for (int clock_idx = 0; clock_idx < ROUNDS_PER_CLOCK; ++clock_idx) {
          current_state = iota(chi(pi(rho(theta(current_state)))), round_idx + clock_idx);
        }

        storage = stateToString(current_state);
        state_out->set(storage);
      }
      round_idx = 0;

      state_out->set(storage);
      complete_out->set(true);
    }
  }
};

#endif //ABR_SH3_H
