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

#ifndef _DECOMPOSE
#define _DECOMPOSE

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
#define VERIFY_OP 0x1
#define SIGN_OP 0x0




enum mem_rw_mode { RW_IDLE, RW_READ, RW_WRITE };
enum rd_states {IDR, RD};
enum wr_states {IDW, WR};


struct mem_if_t {
  mem_rw_mode rd_wr_en;
  sc_uint<MLDSA_MEM_ADDR_WIDTH> addr;
};

sc_uint<4> r1_lut (sc_uint<23> a) {
  if (a <= sc_uint<23>(MLDSA_GAMMA2)) {
    return sc_uint<4>(0);
  }
  else if (a <= sc_uint<23> (3*MLDSA_GAMMA2)) {
    return sc_uint<4>(1);
  }
  else if (a <= sc_uint<23> (5*MLDSA_GAMMA2)) {
    return sc_uint<4>(2);
  }
  else if (a <= sc_uint<23> (7*MLDSA_GAMMA2)) {
    return sc_uint<4>(3);
  }
  else if (a <= sc_uint<23> (9*MLDSA_GAMMA2)) {
    return sc_uint<4>(4);
  }
  else if (a <= sc_uint<23> (11*MLDSA_GAMMA2)) {
    return sc_uint<4>(5);
  }
  else if (a <= sc_uint<23> (13*MLDSA_GAMMA2)) {
    return sc_uint<4>(6);
  }
  else if (a <= sc_uint<23> (15*MLDSA_GAMMA2)) {
    return sc_uint<4>(7);
  }
  else if (a <= sc_uint<23> (17*MLDSA_GAMMA2)) {
    return sc_uint<4>(8);
  }
  else if (a <= sc_uint<23> (19*MLDSA_GAMMA2)) {
    return sc_uint<4>(9);
  }
  else if (a <= sc_uint<23> (21*MLDSA_GAMMA2)) {
    return sc_uint<4>(10);
  }
  else if (a <= sc_uint<23> (23*MLDSA_GAMMA2)) {
    return sc_uint<4>(11);
  }
  else if (a <= sc_uint<23> (25*MLDSA_GAMMA2)) {
    return sc_uint<4>(12);
  }
  else if (a <= sc_uint<23> (27*MLDSA_GAMMA2)) {
    return sc_uint<4>(13);
  }
  else if (a <= sc_uint<23> (29*MLDSA_GAMMA2)) {
    return sc_uint<4>(14);
  }
  else if (a <= sc_uint<23> (31*MLDSA_GAMMA2)) {
    return sc_uint<4>(15);
  }
  else {
    return sc_uint<4>(0);
  }
}
        
std::array<sc_uint<4>, 4> compute_r1 (std::array<sc_uint<23>, 4> data) {
  std::array<sc_uint<4>, 4> result;

  for(int i = 0; i < 4; ++i) {
    result[i] = sc_uint<4> (r1_lut(data[i]));
  }
  return result;
}

std::array<sc_uint<1>, 4> compute_z (std::array<sc_uint<23>, 4> data) {
  std::array<sc_uint<1>, 4> result;

  for(int i = 0; i < 4; ++i) {
    if (r1_lut(data[i]) == 0) {
      result[i] = 0;
    }
    else {
      result[i] = 1;
    }
  }
  return result;
}

//test new function

sc_uint<19> compute_r0_mod_2GAMMA2 (sc_uint<23> data) {

  return (data % sc_uint<19> (2*MLDSA_GAMMA2));
}

sc_uint<23> compute_r0_mod_q (sc_uint<19> data) {
  if (data <= sc_uint<18>(MLDSA_GAMMA2)) {
    return sc_uint<23> (data);
  }
  else {
    return sc_uint<23> (data + Q_MINUS_2GAMMA2);
  }
}

std::array<sc_uint<23>, 4> compute_r0(std::array<sc_uint<23>, 4> data) {
  std::array<sc_uint<23>, 4> result;
  
  for(int i = 0; i < 4; ++i) {
    if (data[i] > sc_uint<23>(31 * MLDSA_GAMMA2)) { //edited
      result[i] = data[i];
    }
    else {
      result[i] = sc_uint<23>(compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[i])));
    }
  }
  return result;
}

std::array<sc_uint<23>, 4> compute_r0_1(std::array<sc_uint<23>, 4> data, bool valid) {
  std::array<sc_uint<23>, 4> result;
  
  for(int i = 0; i < 4; ++i) {
    if (data[i] > sc_uint<23>(31 * MLDSA_GAMMA2)) { //edited
      result[i] = data[i];
    }
    else {
      if (!valid) {
        result[i] = 0;
      }
      else {
        result[i] = sc_uint<23>(compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[i])));
      }
    }
  }
  return result;
}

std::array<sc_uint<23>, 4> compute_r0_2(std::array<sc_uint<23>, 4> data, sc_uint<4> valid, std::array<sc_uint<23>, 4> data2) {
  std::array<sc_uint<23>, 4> result;
  
  for(int i = 0; i < 4; ++i) {
    if (data[i] > sc_uint<23>(31 * MLDSA_GAMMA2)) { 
      result[i] = data[i];
    }
    else {
      if (valid == 0) {
        result[i] = data2[i];
      }
      else {
        result[i] = sc_uint<23>(compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[i])));
      }
    }
  }
  return result;
}

std::array<sc_uint<23>, 4> compute_r0_3(std::array<sc_uint<23>, 4> data, bool valid, std::array<sc_uint<23>, 4> data2) {
  std::array<sc_uint<23>, 4> result;
  
  for(int i = 0; i < 4; ++i) {
    if (data[i] > sc_uint<23>(31 * MLDSA_GAMMA2)) { 
      result[i] = data[i];
    }
    else {
      if (!valid) {
        result[i] = data2[i];
      }
      else {
        result[i] = sc_uint<23>(compute_r0_mod_q(compute_r0_mod_2GAMMA2(data[i])));
      }
    }
  }
  return result;
}


//end test function

bool is_buffer(sc_uint<14> data) {
  if (data % 4 == 3) {
    return true;
  }
  else {
    return false;
  }
}



SC_MODULE (decompose_sign_mode){
    public:
       SC_CTOR(decompose_sign_mode){
            SC_THREAD(run);
        }

        struct BaseAddress {
            sc_uint<14> source;
            sc_uint<14> destination; 
            sc_uint<14> hint_source;
        };

        blocking_in<BaseAddress> start_port; 
        BaseAddress base_address;

        shared_out<sc_uint<14>> cnt_new;
        master_out<mem_if_t> mem_rd_req;
        master_out<mem_if_t> mem_wr_req;
        master_out<mem_if_t> mem_hint_rd_req;
        master_out<mem_if_t> z_mem_wr_req;

        mem_if_t rd_req, wr_req, hrd_req, zwr_req;

        shared_in<sc_uint<14>> current_cnt;
        sc_uint<14> cnt;

        shared_in<sc_uint<4>> mod_ready_port; //added
        sc_uint<4> mr; //added

        shared_in<bool> mod_enable_port; //added
        bool me; //added

        shared_in<std::array<sc_uint<23>, 4>> r0_mod_q_port;
        std::array<sc_uint<23>, 4> rmq;

        shared_in<std::array<sc_uint<23>, 4>> rd_data_port;
        shared_out<std::array<sc_uint<23>, 4>> r0;
        shared_out<std::array<sc_uint<23>, 4>> r0_reg;
        shared_out<std::array<sc_uint<24>, 4>> mem_wr_data;

        shared_in<std::array<sc_uint<23>, 4>> r0_in;
        shared_in<std::array<sc_uint<23>, 4>> r0_reg_in;
        shared_in<std::array<sc_uint<1>, 4>> z_d1_in;
        shared_in<std::array<sc_uint<1>, 4>> z_d2_in;
        shared_in<std::array<sc_uint<16>, 4>> w1_encode_r1_i_in;
        

        shared_out<std::array<sc_uint<1>, 4>> z_neq_z_d1;
        shared_out<std::array<sc_uint<1>, 4>> z_neq_z_d2;
        shared_out<std::array<sc_uint<1>, 4>> z_neq_z;

        shared_out<std::array<sc_uint<4>, 4>> w1_encode_r1_i;
        shared_out<std::array<sc_uint<16>, 4>> w1_o;
        shared_out<bool> buffer_en;
        shared_out<bool> decompose_done;


        std::array<sc_uint<23>, 4> r,r0_var,w0_i, r0_reg_var,wr_data;
        std::array<sc_uint<1>, 4> z,z2,z_data;
        std::array<sc_uint<16>, 4> w1_o_var;
        std::array<sc_uint<4>, 4> r1, w1_i, usehint_w1_o;
        std::array<bool, 4> r_corner;
        std::array<sc_uint<19>, 4> r0_mod_2GAMMA2;
        sc_uint<2> buffer_count;
        sc_uint<3> rounds_count;

        void run(){

          rd_req.rd_wr_en = RW_IDLE;
          rd_req.addr = 0;
          mem_rd_req->master_write(rd_req);

          zwr_req.rd_wr_en = RW_IDLE;
          zwr_req.addr = 0;
          z_mem_wr_req->master_write(zwr_req);

          
          wr_req.rd_wr_en = RW_IDLE;
          wr_req.addr = 0;
          mem_wr_req->master_write(wr_req);
          
          hrd_req.rd_wr_en = RW_IDLE;
          hrd_req.addr = 0;
          mem_hint_rd_req->master_write(hrd_req);

          cnt_new->set(0x2c80);

          decompose_done->set(true);

          while(true) {

            start_port->read(base_address, "IDLE");
            
            rd_req.rd_wr_en = RW_READ;
            rd_req.addr = base_address.source;
            mem_rd_req->master_write(rd_req);
            
            
            wr_req.rd_wr_en = RW_IDLE;
            wr_req.addr = base_address.destination;
            mem_wr_req->master_write(wr_req); 

            zwr_req.rd_wr_en = RW_IDLE;
            zwr_req.addr = 0;
            z_mem_wr_req->master_write(zwr_req); 

            hrd_req.rd_wr_en = RW_IDLE;
            hrd_req.addr = 0;
            mem_hint_rd_req->master_write(hrd_req);

            rd_data_port->get(r);
            mod_ready_port->get(mr);
            r0_mod_q_port->get(rmq);
            
            r0_var = compute_r0_2(r, mr, rmq); //added
            r0->set(r0_var); //added

            r0_in->get(r0_reg_var); //added
            r0_reg->set(r0_reg_var); //added

            r0_reg_in->get(wr_data); //added
            mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])}); //added

            z_neq_z_d1->set(compute_z(r));

            z_d1_in->get(z2); //added
            z_neq_z_d2->set(z2); //added

            z_d2_in->get(z_data); //added
            z_neq_z->set(z_data); //added

            w1_encode_r1_i->set(compute_r1(r));

            buffer_en->set(false);
            decompose_done->set(false);

            cnt_new->set(0);

            insert_state("REQ_1ST_DATA");

            rd_req.rd_wr_en = RW_READ;
            rd_req.addr = base_address.source + 1;
            mem_rd_req->master_write(rd_req);

            wr_req.rd_wr_en = RW_IDLE;
            wr_req.addr = base_address.destination;
            mem_wr_req->master_write(wr_req);

            hrd_req.rd_wr_en = RW_IDLE;
            hrd_req.addr = 0;
            mem_hint_rd_req->master_write(hrd_req);

            zwr_req.rd_wr_en = RW_IDLE;
            zwr_req.addr = 0;
            z_mem_wr_req->master_write(zwr_req);

            rd_data_port->get(r);
            mod_ready_port->get(mr);
            r0_mod_q_port->get(rmq);
            
            r0_var = compute_r0_2(r, mr, rmq); //added
            r0->set(r0_var); //added

            r0_in->get(r0_reg_var); //added
            r0_reg->set(r0_reg_var); //added

            r0_reg_in->get(wr_data); //added
            mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])}); //added

            z_neq_z_d1->set(compute_z(r));

            z_d1_in->get(z2);
            z_neq_z_d2->set(z2);

            z_d2_in->get(z_data); //added
            z_neq_z->set(z_data); //added

            w1_encode_r1_i->set(compute_r1(r));

            buffer_en->set(false);
            decompose_done->set(false);

            insert_state("REQ_2ND_DATA");

            rd_req.rd_wr_en = RW_READ;
            rd_req.addr = base_address.source + 2;
            mem_rd_req->master_write(rd_req);

            wr_req.rd_wr_en = RW_IDLE;
            wr_req.addr = base_address.destination;
            mem_wr_req->master_write(wr_req);

            hrd_req.rd_wr_en = RW_IDLE;
            hrd_req.addr = 0;
            mem_hint_rd_req->master_write(hrd_req);

            zwr_req.rd_wr_en = RW_IDLE;
            zwr_req.addr = 0;
            z_mem_wr_req->master_write(zwr_req);

            rd_data_port->get(r);
            r0_var = compute_r0(r);  
            r0->set(r0_var); //added

            r0_in->get(r0_reg_var);
            r0_reg->set(r0_reg_var);

            r0_reg_in->get(wr_data); //added
            mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])}); //added

            z_neq_z_d1->set(compute_z(r));
            
            z_d1_in->get(z2);
            z_neq_z_d2->set(z2);

            //z_data_port->set({0,0,0,0});

            z_d2_in->get(z_data); //added
            z_neq_z->set(z_data); //added

            w1_encode_r1_i->set(compute_r1(r));

            buffer_en->set(false);
            decompose_done->set(false);

            insert_state("REQ_3RD_DATA");

            rd_req.rd_wr_en = RW_READ;
            rd_req.addr = base_address.source + 3;
            mem_rd_req->master_write(rd_req);

            buffer_en->set(false);
            decompose_done->set(false);

            rd_data_port->get(r);
            r0_var = compute_r0(r);  
            r0->set(r0_var);

            r0_in->get(r0_reg_var);
            r0_reg->set(r0_reg_var);

            r0_reg_in->get(wr_data);
            mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])});

            w1_encode_r1_i->set(compute_r1(r));
            w1_encode_r1_i_in->get(w1_o_var);
            w1_o->set(w1_o_var);

            z_neq_z_d1->set(compute_z(r));
            z_d1_in->get(z2);
            z_neq_z_d2->set(z2);
            z_d2_in->get(z_data);
            z_neq_z->set(z_data);

            wr_req.rd_wr_en = RW_IDLE;
            wr_req.addr = base_address.destination;
            mem_wr_req->master_write(wr_req);

            hrd_req.rd_wr_en = RW_IDLE;
            hrd_req.addr = 0;
            mem_hint_rd_req->master_write(hrd_req);

            zwr_req.rd_wr_en = RW_IDLE;
            zwr_req.addr = 0;
            z_mem_wr_req->master_write(zwr_req);
            

            do {
                insert_state("RD_MEM_WR_MEM"); //READ & WRITE LOOP
                current_cnt -> get(cnt);

                buffer_en->set(is_buffer(cnt+1));
                decompose_done->set(false);


                wr_req.rd_wr_en = RW_WRITE;
                wr_req.addr = base_address.destination + cnt;    
                mem_wr_req->master_write(wr_req);

                zwr_req.rd_wr_en = RW_WRITE;
                zwr_req.addr = cnt;
                z_mem_wr_req->master_write(zwr_req);

                hrd_req.rd_wr_en = RW_IDLE;
                hrd_req.addr = 0;
                mem_hint_rd_req->master_write(hrd_req);

                if(cnt + 3 < 511) {

                  rd_req.rd_wr_en = RW_READ;
                  rd_req.addr = base_address.source + cnt + 4;
                  mem_rd_req->master_write(rd_req);

                }
                else {
                  rd_req.rd_wr_en = RW_IDLE;
                  rd_req.addr = base_address.source;
                  mem_rd_req->master_write(rd_req);
                }

                rd_data_port->get(r); 
                r0_var = compute_r0(r);

                r0->set(r0_var);

                r0_in->get(r0_reg_var);
                r0_reg->set(r0_reg_var);

                r0_reg_in->get(wr_data);
                mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])});

                w1_encode_r1_i->set(compute_r1(r));
                w1_encode_r1_i_in->get(w1_o_var);
                w1_o->set(w1_o_var);

                z_neq_z_d1->set(compute_z(r));
                z_d1_in->get(z2);
                z_neq_z_d2->set(z2);
                z_d2_in->get(z_data);
                z_neq_z->set(z_data);

                cnt_new->set(cnt+1);

            } while (cnt < 510);

            rd_data_port->get(r);
            mod_enable_port->get(me);
            r0_mod_q_port->get(rmq);
            
            r0_var = compute_r0_3(r, me, rmq); //added
            r0->set(r0_var); //added

            insert_state("RESP_LAST_DATA");

            wr_req.rd_wr_en = RW_WRITE;
            wr_req.addr = base_address.destination + 511;    
            mem_wr_req->master_write(wr_req);

            zwr_req.rd_wr_en = RW_WRITE;
            zwr_req.addr = 511;
            z_mem_wr_req->master_write(zwr_req);

            rd_req.rd_wr_en = RW_IDLE;
            rd_req.addr = base_address.source;
            mem_rd_req->master_write(rd_req);

            hrd_req.rd_wr_en = RW_IDLE;
            hrd_req.addr = 0;
            mem_hint_rd_req->master_write(hrd_req);

            rd_data_port->get(r);
            mod_ready_port->get(mr);
            r0_mod_q_port->get(rmq);
            
            r0_var = compute_r0_2(r, mr, rmq); //added
            r0->set(r0_var); //added

            r0_in->get(r0_reg_var);
            r0_reg->set(r0_reg_var);

            r0_reg_in->get(wr_data);
            mem_wr_data->set({sc_uint<24>(wr_data[0]), sc_uint<24>(wr_data[1]), sc_uint<24>(wr_data[2]), sc_uint<24>(wr_data[3])});

            z_neq_z_d1->set(compute_z(r));

            z_d1_in->get(z2);
            z_neq_z_d2->set(z2);
            
            z_d2_in->get(z_data);
            z_neq_z->set(z_data);

            w1_encode_r1_i->set(compute_r1(r));

            buffer_en->set(false);
            decompose_done->set(true);

            cnt_new->set(0x2c80);


          }
            
        }
};
#endif