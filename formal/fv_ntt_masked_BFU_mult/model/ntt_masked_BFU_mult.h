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

#ifndef _ntt_masked_BFU_mult_
#define _ntt_masked_BFU_mult_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

// Declare data types here
// I.e., structs (or classes)



std::array<sc_uint<46>, 2> mult_mod_q(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v) {
    std::array<sc_uint<46>, 2> temp;

    temp[0] = (sc_uint<46> (u[0] * v[0]) + sc_uint<46> (u[0] * v[1])) % MLDSA_Q;
    temp[1] = (sc_uint<46> (u[1] * v[0]) + sc_uint<46> (u[1] * v[1])) % MLDSA_Q;
    
    return temp;
}

std::array<sc_uint<2>, 46> transpose(std::array<sc_uint<46>, 2> temp) {
    std::array<sc_uint<2>, 46> result;

    for (int i = 0;i < 46;++i) {
        result[i][0] = temp[0][i];
        result[i][1] = temp[1][i];
    }

    return result;
}

SC_MODULE(ntt_masked_BFU_mult) {
    public:
        SC_CTOR(ntt_masked_BFU_mult) {
            SC_THREAD(run);
        }

        //shared_in<sc_uint<23>> u;
        shared_in<std::array<sc_uint<46>, 2>> u;
        shared_in<std::array<sc_uint<46>, 2>> v;
        
        shared_out<std::array<sc_uint<2>, 46>> res;

        std::array<sc_uint<46>, 2> u_in;
        std::array<sc_uint<46>, 2> v_in;



        void run(){

          while(true) {

            u->get(u_in);
            v->get(v_in);

            res->set(transpose(mult_mod_q(u_in, v_in)));

            insert_state("COMPUTE");

               
          }
        }
};
#endif