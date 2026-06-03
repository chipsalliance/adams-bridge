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

#ifndef _ntt_masked_gs_butterfly_
#define _ntt_masked_gs_butterfly_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

// Declare data types here
// I.e., structs (or classes)


sc_uint<46> add(sc_uint<46> u, std::array<sc_uint<46>, 2> v) {
    sc_uint<46> temp;

    temp = sc_uint<46> (((u + v[0] + v[1]) % 0x400000000000) % MLDSA_Q);

    return temp;
}

sc_uint<46> mult(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v) {
    
    return (((u[0] + u[1]) * (v[0] + v[1])) % 0x400000000000) % MLDSA_Q; 
    
}

sc_uint<46> compute_u(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v, std::array<sc_uint<46>, 2> w, sc_uint<3> nm, sc_uint<1> acc) {
    sc_uint<46> temp;

    if (nm == 2) {
        if (acc) {
            temp = add(mult(u,v),w);
        }
        else {
            temp = mult(u,v);
        }
    }
    else {
        temp = sc_uint<46> (((u[0] + u[1] + v[0] + v[1]) % 0x400000000000) % MLDSA_Q);
    }

    return temp;
}


sc_uint<46> compute_v(std::array<sc_uint<46>, 2> u, std::array<sc_uint<46>, 2> v, std::array<sc_uint<46>, 2> w, sc_uint<3> nm) {
    sc_uint<46> temp;

    if (nm == 2) {
        temp = 0;
    }

    else {
        if (sc_uint<46> (u[0] + u[1]) >= sc_uint<46> (v[0] + v[1])) {
            temp = sc_uint<46> (u[0] + u[1] - v[0] - v[1]);
        }
        else {
            temp = sc_uint<46> (u[0] + u[1] - v[0] - v[1] + MLDSA_Q);
        }
    }
    
    return ((temp * ((w[0] + w[1]) % 0x400000000000)) % MLDSA_Q);
    
}


SC_MODULE(ntt_masked_gs_butterfly) {
    public:
        SC_CTOR(ntt_masked_gs_butterfly) {
            SC_THREAD(run);
        }

        //shared_in<sc_uint<23>> u;
        shared_in<std::array<sc_uint<46>, 2>> u;
        shared_in<std::array<sc_uint<46>, 2>> v;
        shared_in<std::array<sc_uint<46>, 2>> w;
        shared_in<sc_uint<3>> mode;
        shared_in<sc_uint<1>> accumulate;
        
        shared_out<sc_uint<46>> u_0;
        shared_out<sc_uint<46>> v_0;

        std::array<sc_uint<46>, 2> u_in;
        std::array<sc_uint<46>, 2> v_in;
        std::array<sc_uint<46>, 2> w_in;

        sc_uint<3> nm;
        sc_uint<1> acc;


        void run(){

          while(true) {

            insert_state("INIT");

            u->get(u_in);
            v->get(v_in);
            w->get(w_in);
            mode->get(nm);
            accumulate->get(acc);


            u_0->set(compute_u(u_in,v_in,w_in,nm,acc));
            v_0->set(compute_v(u_in,v_in,w_in,nm));

            if (nm == 2) {
                if (acc) {
                    insert_state("PWMA");
                }
                else {
                    insert_state("PWM");
                }    
            }
            else {
                insert_state("NON_PWM");
            }

               
          }
        }
};
#endif