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

#ifndef NTT_BUTTERFLY2X2_H
#define NTT_BUTTERFLY2X2_H

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q 8380417

sc_uint<23> compute_a_min_b(sc_uint<23> a, sc_uint<23> b) {
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
        result = (data >> 1) + sc_uint<23>((MLDSA_Q + 1) / 2);
    }
    else {
        result = data >> 1;
    }
    return result;
}

// CT (nm=0): u_out = (u + v*w) mod Q
// GS (nm=1): u_out = (u + v) / 2 mod Q  [div2 of sum]
// PWM (nm=2): u_out = u*v mod Q, or w + u*v mod Q if acc
// PWA (nm=3): u_out = (u + v) mod Q
// PWS (nm=4): u_out = (u - v) mod Q
sc_uint<23> compute_u(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm, sc_uint<1> acc) {
    sc_uint<23> result = 0;
    sc_uint<23> result1 = sc_uint<23>((u + v) % MLDSA_Q);

    if (nm == 0) {
        result = (u + sc_uint<23>((v * w) % MLDSA_Q)) % MLDSA_Q;
    }
    else if (nm == 1) {
        if (result1[0]) {
            result = (result1 >> 1) + sc_uint<23>((MLDSA_Q + 1) / 2);
        }
        else {
            result = result1 >> 1;
        }
    }
    else if (nm == 2) {
        if (acc) {
            result = (w + sc_uint<23>((u * v) % MLDSA_Q)) % MLDSA_Q;
        }
        else {
            result = sc_uint<23>((u * v) % MLDSA_Q);
        }
    }
    else if (nm == 3) {
        result = result1;
    }
    else if (nm == 4) {
        result = compute_a_min_b(u, v);
    }
    else {
        result = 0;
    }
    return result;
}

// CT (nm=0): v_out = (u - v*w) mod Q
// GS (nm=1): v_out = ((u - v) / 2) * w mod Q
sc_uint<23> compute_v(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm) {
    sc_uint<23> result = 0;
    sc_uint<23> result1 = sc_uint<23>((v * w) % MLDSA_Q);
    sc_uint<23> result2 = compute_a_min_b(u, v);

    if (nm == 0) {
        if (u >= result1) {
            result = u - result1;
        }
        else {
            result = u - result1 + MLDSA_Q;
        }
    }
    else if (nm == 1) {
        result = sc_uint<23>((div2(result2) * w) % MLDSA_Q);
    }
    else {
        result = 0;
    }
    return result;
}

// PWM output: u*v mod Q (with optional accumulate into w)
// PWA output: (u + v) mod Q
// PWS output: (u - v) mod Q
// All other modes: 0
sc_uint<23> compute_pwm(sc_uint<23> u, sc_uint<23> v, sc_uint<23> w, sc_uint<3> nm, sc_uint<1> acc) {
    sc_uint<23> result = 0;
    if (nm == 2) {
        if (acc) {
            result = (w + sc_uint<23>((u * v) % MLDSA_Q)) % MLDSA_Q;
        }
        else {
            result = sc_uint<23>((u * v) % MLDSA_Q);
        }
    }
    else if (nm == 3) {
        result = sc_uint<23>((u + v) % MLDSA_Q);
    }
    else if (nm == 4) {
        result = compute_a_min_b(u, v);
    }
    else {
        result = 0;
    }
    return result;
}

SC_MODULE(ntt_butterfly2x2)
{
public:
    SC_CTOR(ntt_butterfly2x2) {
        SC_THREAD(run);
    }

    // Control signals
    shared_in<sc_uint<3>>  mode;
    shared_in<sc_uint<1>>  accumulate;
    shared_in<sc_uint<1>>  mlkem;

    // NTT/INTT butterfly inputs (bf_uvwi_t flattened)
    shared_in<sc_uint<23>> u00_i;
    shared_in<sc_uint<23>> u01_i;
    shared_in<sc_uint<23>> v00_i;
    shared_in<sc_uint<23>> v01_i;
    shared_in<sc_uint<23>> w00_i;
    shared_in<sc_uint<23>> w01_i;
    shared_in<sc_uint<23>> w10_i;
    shared_in<sc_uint<23>> w11_i;

    // PWO inputs (pwo_uvwi_t flattened)
    shared_in<sc_uint<23>> pw_u0_i;
    shared_in<sc_uint<23>> pw_u1_i;
    shared_in<sc_uint<23>> pw_u2_i;
    shared_in<sc_uint<23>> pw_u3_i;
    shared_in<sc_uint<23>> pw_v0_i;
    shared_in<sc_uint<23>> pw_v1_i;
    shared_in<sc_uint<23>> pw_v2_i;
    shared_in<sc_uint<23>> pw_v3_i;
    shared_in<sc_uint<23>> pw_w0_i;
    shared_in<sc_uint<23>> pw_w1_i;
    shared_in<sc_uint<23>> pw_w2_i;
    shared_in<sc_uint<23>> pw_w3_i;

    // Stage 1 intermediate results
    // bf_inst00 -> (u10_int, u11_int), bf_inst01 -> (v10_int, v11_int)
    shared_out<sc_uint<23>> u10_int;
    shared_out<sc_uint<23>> u11_int;
    shared_out<sc_uint<23>> v10_int;
    shared_out<sc_uint<23>> v11_int;

    // Stage 2 final outputs (bf_uvo_t flattened)
    shared_out<sc_uint<23>> u20_o;
    shared_out<sc_uint<23>> u21_o;
    shared_out<sc_uint<23>> v20_o;
    shared_out<sc_uint<23>> v21_o;

    // PWO result outputs (pwo_t flattened)
    shared_out<sc_uint<23>> pwo_uv0;
    shared_out<sc_uint<23>> pwo_uv1;
    shared_out<sc_uint<23>> pwo_uv2;
    shared_out<sc_uint<23>> pwo_uv3;

    sc_uint<3> nm;
    sc_uint<1> acc, mlk;
    sc_uint<23> u00, u01, v00, v01, w00, w01, w10, w11;
    sc_uint<23> pu0, pu1, pu2, pu3;
    sc_uint<23> pv0, pv1, pv2, pv3;
    sc_uint<23> pw0, pw1, pw2, pw3;

    void run()
    {
        while (true) {

            insert_state("INIT");

            mode->get(nm);
            accumulate->get(acc);
            mlkem->get(mlk);

            u00_i->get(u00); u01_i->get(u01);
            v00_i->get(v00); v01_i->get(v01);
            w00_i->get(w00); w01_i->get(w01);
            w10_i->get(w10); w11_i->get(w11);

            pw_u0_i->get(pu0); pw_u1_i->get(pu1);
            pw_u2_i->get(pu2); pw_u3_i->get(pu3);
            pw_v0_i->get(pv0); pw_v1_i->get(pv1);
            pw_v2_i->get(pv2); pw_v3_i->get(pv3);
            pw_w0_i->get(pw0); pw_w1_i->get(pw1);
            pw_w2_i->get(pw2); pw_w3_i->get(pw3);

            // pwo_mode:    PWM/PWA/PWS — all four BF units take pw_uvw_i directly
            // pairwm_mode: pairwm (nm=5) — mode==5 maps to PWA_PWS in RTL binding
            //              regardless of mlkem, so treated as PWO path here
            bool pwo_mode    = (nm == 2 || nm == 3 || nm == 4);
            bool pairwm_mode = (nm == 5);

            if (pwo_mode || pairwm_mode) {
                // All four butterfly units receive pw_uvw_i inputs directly
                u10_int->set(compute_u(pu0, pv0, pw0, nm, acc));
                u11_int->set(compute_v(pu0, pv0, pw0, nm));
                v10_int->set(compute_u(pu1, pv1, pw1, nm, acc));
                v11_int->set(compute_v(pu1, pv1, pw1, nm));

                u20_o->set(compute_u(pu2, pv2, pw2, nm, acc));
                v20_o->set(compute_v(pu2, pv2, pw2, nm));
                u21_o->set(compute_u(pu3, pv3, pw3, nm, acc));
                v21_o->set(compute_v(pu3, pv3, pw3, nm));

                pwo_uv0->set(compute_pwm(pu0, pv0, pw0, nm, acc));
                pwo_uv1->set(compute_pwm(pu1, pv1, pw1, nm, acc));
                pwo_uv2->set(compute_pwm(pu2, pv2, pw2, nm, acc));
                pwo_uv3->set(compute_pwm(pu3, pv3, pw3, nm, acc));

                if (nm == 2) {
                    if (acc) {
                        insert_state("PWM_ACC");
                    }
                    else {
                        insert_state("PWM_NOT_ACC");
                    }
                }
                else {
                    insert_state("PWA_PWS");
                }
            }
            else {
                // NTT/INTT mode: ct (nm=0) or gs (nm=1)
                // Stage 1: bf_inst00 -> (u10_int, u11_int), bf_inst01 -> (v10_int, v11_int)
                sc_uint<23> s1_u10 = compute_u(u00, v00, w00, nm, acc);
                sc_uint<23> s1_u11 = compute_v(u00, v00, w00, nm);
                sc_uint<23> s1_v10 = compute_u(u01, v01, w01, nm, acc);
                sc_uint<23> s1_v11 = compute_v(u01, v01, w01, nm);

                u10_int->set(s1_u10);
                u11_int->set(s1_u11);
                v10_int->set(s1_v10);
                v11_int->set(s1_v11);

                // Stage 2: bf_inst10 -> (u20_o, v20_o), bf_inst11 -> (u21_o, v21_o)
                // w10/w11 are the twiddle factors delayed through stage 1 pipeline
                u20_o->set(compute_u(s1_u10, s1_v10, w10, nm, acc));
                v20_o->set(compute_v(s1_u10, s1_v10, w10, nm));
                u21_o->set(compute_u(s1_u11, s1_v11, w11, nm, acc));
                v21_o->set(compute_v(s1_u11, s1_v11, w11, nm));

                // compute_pwm returns 0 for nm=0 (ct) and nm=1 (gs)
                pwo_uv0->set(compute_pwm(u00, v00, w00, nm, acc));
                pwo_uv1->set(compute_pwm(u01, v01, w01, nm, acc));
                pwo_uv2->set(compute_pwm(s1_u10, s1_v10, w10, nm, acc));
                pwo_uv3->set(compute_pwm(s1_u11, s1_v11, w11, nm, acc));

                if (nm == 0) {
                    insert_state("CT");
                }
                else {
                    insert_state("GS");
                }
            }
        }
    }
};

#endif
