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

#ifndef _ntt_butterfly_
#define _ntt_butterfly_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

// Declare data types here
// I.e., structs (or classes)

//enum ntt_mode {ct, gs, pwm, pwa, pws, pwm_intt};

sc_uint<23> compute_a_min_b (sc_uint<23> a, sc_uint<23> b) {
    sc_uint<23> result = 0;

    if (a >= b) {
        result = a - b;
    }
    else {
        result = a - b + MLDSA_Q;
    }

    return result;
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

sc_uint<23> compute_u(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm, sc_uint<1> acc) {
    sc_uint<23> result = 0;
    sc_uint<23> result1 = sc_uint<23> ((u + v) % MLDSA_Q);

    if (nm == 0) {  //verified
        result = (u + sc_uint<23> ((v * w) % MLDSA_Q)) % MLDSA_Q;
    }
    else if (nm == 1) { //verified
        if (result1[0]) {
            result = (result1 >> 1) + sc_uint<23> ((MLDSA_Q + 1) / 2);
        }
        else {
            result = result1 >> 1;
        } 
    }
    else if (nm == 2) { //verified
        if (acc) {
            result = (w + sc_uint<23> ((u * v) % MLDSA_Q)) % MLDSA_Q;
        }
        else {
            result = sc_uint<23> ((u * v) % MLDSA_Q);
        }
    }
    else if (nm == 3) { //verified
        result = result1;
    }
    else if (nm == 4) { //verified
        result = compute_a_min_b(u, v);
    }
    else {
        result = 0;
    }
    return result;
}

sc_uint<23> compute_v(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm) {
    sc_uint<23> result = 0;
    sc_uint<23> result1 = sc_uint<23> ((v * w) % MLDSA_Q);
    sc_uint<23> result2 = compute_a_min_b(u,v);
    sc_uint<23> result3 = (result2 >> 1) + 0x3ff001;
    if (nm == 0) {
        if (u >= result1) { //verified
            result =  u - result1;
        }
        else {
            result =  u - result1 + MLDSA_Q;
        }  
    }
    else if (nm == 1) { //hold bounded
        result = sc_uint<23> ((div2(result2) * w) % MLDSA_Q);
    }
    else {
        result = 0;
    }

    return result;
}

sc_uint<23> compute_pwm(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm, sc_uint<1> acc) {
    sc_uint<23> result = 0;
    if (nm == 2) {
        if (acc) {
            result = (w + sc_uint<23> ((u * v) % MLDSA_Q)) % MLDSA_Q;
        }
        else {
            result = sc_uint<23> ((u * v) % MLDSA_Q);
        }
    }
    else if (nm == 3) {
        result = sc_uint<23> ((u + v) % MLDSA_Q);
    }
    else if (nm == 4) {
        result = compute_a_min_b(u, v);
    }
    else {
        result = 0;
    }

    return result;  
}




SC_MODULE(ntt_butterfly) {
    public:
        SC_CTOR(ntt_butterfly) {
            SC_THREAD(run);
        }

        shared_in<sc_uint<23>> opu_i;
        shared_in<sc_uint<23>> opv_i;
        shared_in<sc_uint<23>> opw_i;
        shared_in<sc_uint<3>> mode;
        shared_in<sc_uint<1>> accumulate;

        shared_out<sc_uint<23>> u_o;
        shared_out<sc_uint<23>> v_o;
        shared_out<sc_uint<23>> pwm_res_o;

        shared_out<sc_uint<23>> u_reg;
        shared_out<sc_uint<23>> u_reg_d2;
        shared_out<sc_uint<23>> u_reg_d3;
        shared_out<sc_uint<23>> u_reg_d4;

        shared_out<sc_uint<23>> w_reg;
        shared_out<sc_uint<23>> w_reg_d2;
        shared_out<sc_uint<23>> w_reg_d3;
        shared_out<sc_uint<23>> w_reg_d4;

        shared_in<sc_uint<23>> add_res;
        shared_out<sc_uint<23>> add_res_d1;
        shared_out<sc_uint<23>> add_res_d2;

        shared_out<sc_uint<23>> mul_opa;
        shared_out<sc_uint<23>> mul_opb;

        sc_uint<23> u_in, v_in, w_in, a_in;
        sc_uint<3> nm;
        sc_uint<1> acc;

        void run(){

          while(true) {

            insert_state("INIT");

            mode->get(nm);
            accumulate->get(acc);
            opu_i->get(u_in);
            opv_i->get(v_in);
            opw_i->get(w_in);
            add_res->get(a_in);

            u_o->set(compute_u(u_in,v_in,w_in,nm,acc));
            v_o->set(compute_v(u_in,v_in,w_in,nm));
            pwm_res_o->set(compute_pwm(u_in,v_in,w_in,nm,acc));

            u_reg->set(u_in);
            u_reg_d2->set(u_in);
            u_reg_d3->set(u_in);
            u_reg_d4->set(u_in);

            w_reg->set(w_in);
            w_reg_d2->set(w_in);
            w_reg_d3->set(w_in);
            w_reg_d4->set(w_in);

            add_res_d1->set(a_in);
            add_res_d2->set(a_in);

            if (nm != 2) {
                if (nm > 2) {
                    mul_opa->set(0);
                    mul_opb->set(0);
                    insert_state("PWA_PWS");
                }
                else if (nm == 0) {
                    mul_opa->set(v_in);
                    mul_opb->set(w_in);
                    insert_state("CT");
                }
                else {
                    mul_opa->set(div2(compute_a_min_b(u_in,v_in)));
                    mul_opb->set(w_in);
                    insert_state("GS");
                }
            }
            else {
                mul_opa->set(u_in);
                mul_opb->set(v_in);
                if (acc) {
                    insert_state("PWM_ACC");
                }

                else {
                    insert_state("PWM_NOT_ACC");
                }

            }   
          }
        }
};
#endif