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

#ifndef _ntt_masked_butterfly1x2_
#define _ntt_masked_butterfly1x2_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

// Declare data types here
// I.e., structs (or classes)



sc_uint<23> compute_u(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v) {
    sc_uint<23> temp;

    temp = sc_uint<23> (((u[0] + u[1] + v[0] + v[1]) % 0x400000000000) % MLDSA_Q);

    return temp;
}

sc_uint<23> compute_v(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v, std::array<sc_uint<46>, 2> w) {
    sc_uint<23> temp;

    if (sc_uint<46> (u[0] + u[1]) >= sc_uint<46> (v[0] + v[1])) {
        temp = sc_uint<23> (u[0] + u[1] - v[0] - v[1]);
        //return sc_uint<46> (u[0] + u[1] - v[0] - v[1]);
    }
    else {
        temp = sc_uint<23> (u[0] + u[1] - v[0] - v[1] + MLDSA_Q);
    }
    
    return ((temp * ((w[0] + w[1]) % 0x400000000000)) % MLDSA_Q);
    
}

sc_uint<23> div2(sc_uint<23> data) {
    sc_uint<23> result = 0;
    if (data[0]) {
        result = (data >> 1) + sc_uint<23> ((MLDSA_Q + 1) / 2);
    }
    else {
        result = data >> 1;
    }
    return result;
}


SC_MODULE(ntt_masked_butterfly1x2) {
    public:
        SC_CTOR(ntt_masked_butterfly1x2) {
            SC_THREAD(run);
        }

        //shared_in<sc_uint<23>> u;
        shared_in<std::array<sc_uint<46>, 2>> u00;
        shared_in<std::array<sc_uint<46>, 2>> v00;
        shared_in<std::array<sc_uint<46>, 2>> w00;

        shared_in<std::array<sc_uint<46>, 2>> u01;
        shared_in<std::array<sc_uint<46>, 2>> v01;
        shared_in<std::array<sc_uint<46>, 2>> w01;
        
        shared_out<sc_uint<23>> uv_0_u20;
        shared_out<sc_uint<23>> uv_0_u21;
        shared_out<sc_uint<23>> uv_0_v20;
        shared_out<sc_uint<23>> uv_0_v21;

        std::array<sc_uint<46>, 2> u00_in;
        std::array<sc_uint<46>, 2> v00_in;
        std::array<sc_uint<46>, 2> w00_in;

        std::array<sc_uint<46>, 2> u01_in;
        std::array<sc_uint<46>, 2> v01_in;
        std::array<sc_uint<46>, 2> w01_in;


        void run(){

          while(true) {

            u00->get(u00_in);
            v00->get(v00_in);
            w00->get(w00_in);

            u01->get(u01_in);
            v01->get(v01_in);
            w01->get(w01_in);

            uv_0_u20->set(div2(compute_u(u00_in,v00_in)));
            uv_0_u21->set(div2(compute_v(u00_in,v00_in,w00_in)));

            uv_0_v20->set(div2(compute_u(u01_in,v01_in)));
            uv_0_v21->set(div2(compute_v(u01_in,v01_in,w01_in)));

            insert_state("COMPUTE");
               
          }
        }
};
#endif