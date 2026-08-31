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

#ifndef _sample_in_ball_ctrl_state_
#define _sample_in_ball_ctrl_state_

#include "systemc.h"
#include "Interfaces.h"

// Declare data types here
// I.e., structs (or classes)

/*sc_uint<1> c_read_valid(sc_uint<1> shuffler_valid) {
    if (shuffler_valid & !c_read_valid(shuffler_valid)) {
        return 1;
    }
    else {
        return 0;
    }
}*/

/*sc_uint<4> c_mask_d (sc_uint<1> data_valid, sc_uint<4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej) {
    sc_uint<4> temp = mask;
    for(int i = 3; i >= 0; --i) {
        if (data_valid & !c_index_found(data_valid, mask, data, rej)) {
            temp[i] = 0;
        }
    }
    return temp;
    
}*/

/*sc_uint<1> c_mask_en (bool data_valid, std::array<sc_uint<1>, 4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej, sc_uint<1> read_valid) {
    sc_uint<1> a = c_index_found(data_valid, mask, data, rej);
    sc_uint<1> b = (c_valid_index(data_valid, mask, data, rej) != 3);
    //sc_uint<1> c = c_read_valid(c_index_found(data_valid, mask, data, rej));
    
    return (a & b & read_valid);
}*/

/*sc_uint<4> c_mask (sc_uint<1> data_valid, sc_uint<4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej) {
    sc_uint<4> temp = 0xF;
    
    if (c_mask_en(data_valid, mask, data, rej)) {
        temp = c_mask_d(data_valid, mask, data, rej);
    }

    return temp;
    
}*/


SC_MODULE(sample_in_ball_ctrl_state) {
    public:
        SC_CTOR(sample_in_ball_ctrl_state) {
            SC_THREAD(run);
        }
        
        blocking_in<sc_uint<32>> data_i_port;
        sc_uint<32> data_in;
        shared_in<bool> data_valid_i;
        bool dv_in;

        shared_out<sc_uint<60>> sign_buffer;
        shared_in<sc_uint<60>> sign_buffer_in;
        sc_uint<60> sb_in;

        shared_in<sc_uint<8>> rej_value_in;
        shared_in<bool> rej_value_en;        
        shared_out<sc_uint<8>> rej_value;
        sc_uint<8> rej;
        bool r;

        shared_out<bool> read_valid;
        shared_in<bool> read_valid_in; 
        shared_in<bool> index_found; 
        bool rv_in, i_f;

        /*shared_out<std::array<sc_uint<1>, 4>> sampler_mask;
        shared_in<std::array<sc_uint<1>, 4>> sampler_mask_in;
        shared_in<bool> sampler_mask_en;
        std::array<sc_uint<1>, 4> sm;
        bool me;
        
        std::array<sc_uint<1>, 4> comp_mask_d(std::array<sc_uint<1>, 4> mask, bool valid, bool i_f) const {
            std::array<sc_uint<1>, 4> temp = mask;

            //if (me) {
                for(int i = 0; i < 4; ++i) {
                    if (valid&& !i_f) {
                        temp[i] = 0;
                        break;
                    }
                }
            //}
            return temp;   
        }*/

        void run() {

            while (true) {

                rej_value->set(0xc4);
                sign_buffer->set(0);
                read_valid->set(false);
                //sampler_mask->set({1,1,1,1});

                data_i_port->read(data_in, "IDLE");

                rej_value->set(0xc4);
                sign_buffer->set(sc_uint<60> (data_in)); //on IDLE -> SB transition, sign_buffer == $past(data_i)
                read_valid->set(false);
                //sampler_mask->set({1,1,1,1});

                data_i_port->read(data_in, "SIGN_BUFFER");

                sign_buffer_in->get(sb_in);

                rej_value->set(0xc4);
                sign_buffer->set(sb_in | sc_uint<60> (sc_uint<64> (data_in) << 32)); 
                //on SB -> ACT transition, sign_buffer == $past(sign_buffer | (data_i << 32)) 

                read_valid->set(false);
                //sampler_mask->set({1,1,1,1});

                do {
                    insert_state("ACTIVE");
                    data_valid_i->get(dv_in);
                    rej_value_in->get(rej);
                    sign_buffer_in->get(sb_in);
                    read_valid_in->get(rv_in);
                    index_found->get(i_f);  //index found is already proven in sib_ctrl.h
                    rej_value_en->get(r);   //rej_value_en is already proven in sib_ctrl.h
                    //sampler_mask_en->get(me);
                    //sampler_mask_in->get(sm);
                    
                    read_valid->set(i_f && !rv_in);
                    
                    /*if (me) {
                        sampler_mask->set(comp_mask_d(sm, dv_in, i_f)); 
                        //sampler_mask_d[i] keeps getting assigned to 0 even when index_found is 1.
                    }*/
                    
                    if (r) {
                        rej_value->set(rej+1);
                        sign_buffer->set(sb_in >> 1);
                    }

                } while (rej < 255);

                insert_state("DONE"); //no transition back to IDLE as per design.
                
	        }
        }
    };

#endif
