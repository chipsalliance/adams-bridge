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

#ifndef _sample_in_ball_ctrl_
#define _sample_in_ball_ctrl_

#include "systemc.h"
#include "Interfaces.h"

// Declare data types here
// I.e., structs (or classes)


SC_MODULE(sample_in_ball_ctrl) {
    public:
        SC_CTOR(sample_in_ball_ctrl) {
            SC_THREAD(run);
        }

        blocking_in<std::array<sc_uint<8>, 4>> sib_data_in_port;
        shared_in<std::array<sc_uint<8>, 4>> shared_sib_data_in_port;
        shared_out<bool> data_hold_o;
        shared_out<bool> sib_done_o;
        shared_out<sc_uint<2>> cs_o;
        shared_out<sc_uint<2>> we_o;
        shared_out<std::array<sc_uint<6>, 2>> addr_o;
        shared_in<sc_uint<8>> rej_value_port;
        shared_in<sc_uint<8>> sampler_valid_port;
        shared_in<bool> read_valid_port;
        shared_in<bool> sign_buffer0_port;
        shared_out<std::array<sc_uint<23>, 4>> wrdata0_o;
        shared_out<std::array<sc_uint<23>, 4>> wrdata1_o;
        shared_in<std::array<sc_uint<23>, 4>> rddata0_port;
        shared_in<std::array<sc_uint<23>, 4>> rddata1_port;
        shared_in<bool> data_valid_port;
        shared_in<std::array<bool, 4>> sampler_data_valid_port;
        shared_in<std::array<sc_uint<1>, 4>> sampler_mask; 
        shared_out<sc_uint<1>> index_found; 
        shared_out<sc_uint<1>> rej_value_en_out; 
        shared_out<sc_uint<8>> valid_sample; 
        shared_out<bool> sampler_mask_en; 
        shared_out<std::array<sc_uint<1>, 4>> sampler_mask_d;
        
        enum states {
        SIB_IDLE, SIB_SIGN_BUFFER, SIB_ACTIVE, SIB_DONE
        };

        states cur_st, nxt_st;
        std::array<sc_uint<8>, 4> data_i;
        bool v, sign, rv;
        sc_uint<8> index_i, index_j;
        std::array<sc_uint<23>, 4> rd_data0, rd_data1;
        std::array<bool, 4> sv;
        std::array<sc_uint<1>, 4> m;

        sc_uint<6> compute_addr(std::array<sc_uint<8>, 4> data, sc_uint<8> rej, std::array<bool, 4> sampler_valid, bool valid) const {
          sc_uint<8> result = data[0]; //when all data > rej | data_valid == 0, the output is data[0].. is this expected?
          
          if (valid) {
            for(int i = 3; i >= 0; --i) {
              if (sampler_valid[i] && data[i] <= rej) {
                result = data[i];
              }
            }
          }
          return result.range(7,2);
          
        }

        sc_uint<6> upper_range(sc_uint<8> index) const {
          sc_uint<8> result = index;
          
          return result.range(7,2);
        }

        sc_uint<2> lower_range(sc_uint<8> index) const {
          sc_uint<8> result = index;
          
          return result.range(1,0);
        }

        std::array<sc_uint<23>, 4> compute_data_0(std::array<sc_uint<23>, 4> data, sc_uint<8> index, bool sign) const {
          std::array<sc_uint<23>, 4> result = {0,0,0,0};
          sc_uint<2> j = lower_range(index);

          if (j == 0) {
            result[3] = data[3];
            result[2] = data[2];
            result[1] = data[1];
            result[0] = sign? sc_uint<23>(8380416) : sc_uint<23>(1);
          }
          else if (j == 1) {
            result[3] = data[3];
            result[2] = data[2];
            result[1] = sign? sc_uint<23>(8380416) : sc_uint<23>(1);
            result[0] = data[0];
          }
          else if (j == 2) {
            result[3] = data[3];
            result[2] = sign? sc_uint<23>(8380416) : sc_uint<23>(1);
            result[1] = data[1];
            result[0] = data[0];
          }
          else if (j == 3) {
            result[3] = sign? sc_uint<23>(8380416) : sc_uint<23>(1);
            result[2] = data[2];
            result[1] = data[1];
            result[0] = data[0];
          }
          return result;
        }

        std::array<sc_uint<23>, 4> compute_data_pre(std::array<sc_uint<23>, 4> data0, std::array<sc_uint<23>, 4> data1,
         sc_uint<8> index_i, sc_uint<8> index_j) const {
          std::array<sc_uint<23>, 4> result = {0,0,0,0};
          sc_uint<2> i = lower_range(index_i);
          sc_uint<2> j = lower_range(index_j);
          
          if (i == 0) {
            result[3] = data1[3];
            result[2] = data1[2];
            result[1] = data1[1];
            result[0] = data0[j];
          }
          else if (i == 1) {
            result[3] = data1[3];
            result[2] = data1[2];
            result[1] = data0[j];
            result[0] = data1[0];
          }
          else if (i == 2) {
            result[3] = data1[3];
            result[2] = data0[j];
            result[1] = data1[1];
            result[0] = data1[0];
          }
          else if (i == 3) {
            result[3] = data0[j];
            result[2] = data1[2];
            result[1] = data1[1];
            result[0] = data1[0];
          }
          return result;
        }
        
        std::array<sc_uint<23>, 4> compute_data_1(std::array<sc_uint<23>, 4> data0, std::array<sc_uint<23>, 4> data1,
         sc_uint<8> index_i, sc_uint<8> index_j, bool sign) const {
          std::array<sc_uint<23>, 4> result = {0,0,0,0};
          sc_uint<6> addr_i = upper_range(index_i);
          sc_uint<6> addr_j = upper_range(index_j);
          sc_uint<2> i = lower_range(index_i);
          sc_uint<2> j = lower_range(index_j);

          if (addr_i != addr_j) {
            result = compute_data_pre(data0, data1, index_i, index_j);
          }
          else
          {
            result = compute_data_0(compute_data_pre(data0, data1, index_i, index_j),index_j, sign);
          }
          return result;
        }

        bool is_sampler_hold(std::array<sc_uint<8>, 4> data, sc_uint<8> rej, std::array<bool, 4> sampler_valid, bool valid) const {
          bool result = false;
          if (valid) {
            for(int i = 3; i >= 0; --i) {
              if (sampler_valid[i] && data[i] <= rej && i != 3) {
                result = true;
              }
            }
          }
          return result;
        }

        bool is_shuffler_hold(std::array<sc_uint<8>, 4> data, sc_uint<8> rej, bool read_valid, std::array<bool, 4> sampler_valid, bool valid) const {
          bool result = false;
          if (valid) {
            for(int i = 3; i >= 0; --i) {
              if (sampler_valid[i] && data[i] <= rej) {
                result = true;
              }
            }
          }
          return (result && !read_valid); 
        }

        bool is_data_hold(std::array<sc_uint<8>, 4> data, sc_uint<8> rej, bool read_valid, std::array<bool, 4> sampler_valid, bool valid) const {
          return (is_sampler_hold(data, rej, sampler_valid, valid) || is_shuffler_hold(data, rej, read_valid, sampler_valid, valid));
        }

        sc_uint<2> compute_cs(std::array<sc_uint<8>, 4> data, sc_uint<8> rej, std::array<bool, 4> sampler_valid, bool valid) const {
          sc_uint<2> result = 0;
          if (valid) {
            for(int i = 3; i >= 0; --i) {
              if (sampler_valid[i] && data[i] <= rej) {
                result = 3;
              }
            }
          }
          return result;
        }

        sc_uint<2> compute_we(bool read_valid, sc_uint<8> index_i, sc_uint<8> index_j) const {
          sc_uint<6> addr_i = upper_range(index_i);
          sc_uint<6> addr_j = upper_range(index_j);

          if (!read_valid) {
            return 0;
          }
          else {
            if (addr_i != addr_j) {
              return 3;
            }
            else {
              return 2;
            }
          }
        }

        sc_uint<1> c_index_found (bool data_valid, std::array<sc_uint<1>, 4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej) const {
          sc_uint<1> temp = 0;
          for(int i = 3; i > (-1); --i) {
              if (data_valid && (mask[i] == sc_uint<2> (1)) && (data[i] <= rej)) {
                  temp = 1;
                  break;
              }
              else {
                  temp = 0;
              }
          }
          return temp;  
      }

        sc_uint<1> c_rej_val_en(bool data_valid, std::array<sc_uint<1>, 4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej, bool read_valid) const {
  
          return (c_index_found(data_valid, mask, data, rej) && read_valid);
        }

        sc_uint<8> c_valid_sample (bool data_valid, std::array<sc_uint<1>, 4> mask, std::array<sc_uint<8>, 4> data, sc_uint<8> rej) const {
          sc_uint<2> temp = 0;
          for(int i = 3; i > (-1); --i) {
              if (data_valid && (mask[i] == sc_uint<2> (1)) && (data[i] <= rej)) {
                  temp = sc_uint<2> (i);
                  //break;
              }
          }
          return data[temp];  
        }

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
      }

      

        void run() {
            while (true) {

                shared_sib_data_in_port->get(data_i); 
                rej_value_port->get(index_i);
                sampler_data_valid_port->get(sv);
                data_valid_port->get(v);
                addr_o->set({compute_addr(data_i,index_i,sv,v),upper_range(index_i)});

                rddata0_port->get(rd_data0);
                sampler_valid_port->get(index_j);
                sign_buffer0_port->get(sign);
                wrdata0_o->set(compute_data_0(rd_data0,index_j,sign));

                rddata1_port->get(rd_data1);
                wrdata1_o->set(compute_data_1(rd_data0, rd_data1, index_i, index_j, sign));

                sampler_mask->get(m);//added

                index_found->set(c_index_found(v, m, data_i, index_i)); //added
                valid_sample->set(c_valid_sample(v, m, data_i, index_i)); //added
                sampler_mask_d->set(comp_mask_d(m, v, bool(c_index_found(v,m,data_i,index_i))));


                cur_st = nxt_st;
                if (cur_st == SIB_IDLE) {
                  insert_state("IDLE");

                  data_hold_o->set(false);
                  sib_done_o->set(false);
                  cs_o->set(0);
                  we_o->set(0);
                  rej_value_en_out->set(0);
                  sampler_mask_en->set(false);
                  
                  nxt_st = SIB_IDLE;
                }

                else if (cur_st == SIB_SIGN_BUFFER) {
                  insert_state("SIGN_BUFFER");

                  data_hold_o->set(false);
                  sib_done_o->set(false);
                  cs_o->set(0);
                  we_o->set(0);
                  rej_value_en_out->set(0);
                  sampler_mask_en->set(false);

                  nxt_st = SIB_SIGN_BUFFER;
                }

                else if(cur_st == SIB_ACTIVE) {
                  insert_state("ACTIVE");

                  shared_sib_data_in_port->get(data_i);
                  data_valid_port->get(v);
                  rej_value_port->get(index_i);
                  read_valid_port->get(rv);
                  sampler_data_valid_port->get(sv);
                  sampler_valid_port->get(index_j);
                  sampler_mask->get(m);//added

                  data_hold_o->set(is_data_hold(data_i, index_i, rv, sv, v)); 
                  sib_done_o->set(false);
                  cs_o->set(compute_cs(data_i, index_i, sv,v));
                  we_o->set(compute_we(rv,index_i,index_j));

                  rej_value_en_out->set(c_rej_val_en(v, m, data_i, index_i, rv)); //added
                  sampler_mask_en->set(c_index_found(v, m, data_i, index_i) && is_sampler_hold(data_i,index_i,sv,v) && !is_shuffler_hold(data_i,index_i,rv,sv,v));

                  nxt_st = SIB_ACTIVE;
                }

                else if (cur_st == SIB_DONE) {
                  insert_state("DONE");

                  sib_done_o->set(true);
                  data_hold_o->set(false);
                  cs_o->set(0);
                  we_o->set(0);
                  rej_value_en_out->set(0);
                  sampler_mask_en->set(false);

                  nxt_st = SIB_DONE;
                }
                else {
                  data_hold_o->set(true);
                }
                

	    }
        }
};

#endif
