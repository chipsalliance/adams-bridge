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


#ifndef _EXP_MASK_CTRL
#define _EXP_MASK_CTRL

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417
#define MLDSA_GAMMA2 261888
#define MLDSA_MEM_ADDR_WIDTH 14
#define Q_MINUS_2GAMMA2 7856641
#define MLDSA_K 8
#define MLDSA_N 256
#define BUFFER_CYC 4
#define REG_SIZE 24

const sc_uint<24> GAMMA1 = static_cast<unsigned>(1) << static_cast<unsigned>(19);



SC_MODULE (exp_mask_ctrl){
    public:
       SC_CTOR(exp_mask_ctrl){
            SC_THREAD(run);
        }

        //blocking_in<std::array<sc_uint<20>, 4>>input_data_port;
        //master_out<std::array<sc_uint<23>, 4>>output_data_port;
        shared_in<std::array<sc_uint<20>, 4>>input_data_port;
        shared_out<std::array<sc_uint<23>, 4>>output_data_port;
        shared_in<bool> input_data_valid_port;
        shared_out<bool> output_data_valid_port;

        std::array<sc_uint<20>, 4> r0;
        bool dv;
        

        sc_uint<23> expand_mask (sc_uint<20> data) const {
          sc_uint<23> result;

          result = GAMMA1 - data;

          if (GAMMA1 < data) {
            result = result + MLDSA_Q;
          }

          return result;
        }
        
        std::array<sc_uint<23>, 4> expand_mask_coeff (std::array<sc_uint<20>, 4> data) const {
          std::array<sc_uint<23>, 4> result;

          for(int i = 0; i < 4; ++i) {
            result[i] = expand_mask(data[i]);
          }
          
          return result;
        }


        void run(){

          while(true) {

            input_data_port->get(r0);
            input_data_valid_port->get(dv);

            output_data_port -> set(expand_mask_coeff(r0));
            output_data_valid_port->set(dv);
            insert_state("COMPUTE");
            
          }
        }
};
#endif
