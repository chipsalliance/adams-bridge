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

#ifndef _ntt_masked_BFU_add_sub_
#define _ntt_masked_BFU_add_sub_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

// Declare data types here
// I.e., structs (or classes)



std::array<sc_uint<46>, 2> add_sub(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v, sc_uint<1> sub) {
    std::array<sc_uint<46>, 2> temp;

    for (int i = 0;i < 2; ++i) {
        if (!sub){
            temp[i] = u[i] + v[i];
        }
        else {
            temp[0] = u[0] + MLDSA_Q - v[0];
            temp[1] = u[1] + ~v[1] + 1;
        }
    }
    return temp;
}


std::array<sc_uint<2>, 46> transpose(std::array<sc_uint<46>, 2> temp) {
    std::array<sc_uint<2>, 46> result;

    for (int i = 0;i < 46;++i) {
        result[0][i] = temp[i][0];
        result[1][i] = temp[i][1];
    }

    return result;
}

SC_MODULE(ntt_masked_BFU_add_sub) {
    public:
        SC_CTOR(ntt_masked_BFU_add_sub) {
            SC_THREAD(run);
        }

        //shared_in<sc_uint<23>> u;
        shared_in<std::array<sc_uint<46>, 2>> u;
        shared_in<std::array<sc_uint<46>, 2>> v;
        shared_in<sc_uint<1>> sub;
        
        shared_out<std::array<sc_uint<2>, 46>> res;
        //shared_out<sc_uint<48>> add_res_reduced_sum;

        std::array<sc_uint<46>, 2> u_in;
        std::array<sc_uint<46>, 2> v_in;
        sc_uint<1> s;



        void run(){

          while(true) {

            u->get(u_in);
            v->get(v_in);
            sub->get(s);

            res->set(transpose(add_sub(u_in, v_in, s)));
            //add_res_reduced_sum->set(add_sub_1(u_in, v_in, s));

            insert_state("COMPUTE");

               
          }
        }
};
#endif