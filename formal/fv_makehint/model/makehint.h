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

#ifndef _MAKEHINT
#define _MAKEHINT

#include "systemc.h"
#include "Interfaces.h"



#define REG_SIZE              24
#define MLDSA_Q               8380417
#define MLDSA_N               256
#define MLDSA_K               8
#define OMEGA                 75
#define BUFFER_DATA_W         8
#define MLDSA_MEM_ADDR_WIDTH  14
#define MLDSA_GAMMA2          261888 //(MLDSA_Q - 1)/32
#define Q_MINUS_GAMMA2        8118529//MLDSA_Q - MLDSA_GAMMA2

enum mh_read_state_e { MH_IDLE, MH_RD_MEM, MH_WAIT1, MH_WAIT2, MH_FLUSH_SBUF, MH_RD_IBUF_LOW, MH_RD_IBUF_HIGH, MH_RD_IBUF_MID};
enum mem_rw_mode_e   { RW_IDLE, RW_READ, RW_WRITE };

struct mem_if_t {
  mem_rw_mode_e                   rd_wr_en;
  sc_uint<MLDSA_MEM_ADDR_WIDTH>   addr;
};

struct BaseAddress {
  sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_base_addr;
  sc_uint<MLDSA_MEM_ADDR_WIDTH> dest_base_addr; 
};


SC_MODULE(makehint){

    public:
        SC_CTOR(makehint){
            SC_THREAD(run);
        }

        blocking_in<bool>                              makehint_enable_port;
        bool                                           makehint_enable;

        shared_in<sc_uint<4*REG_SIZE>>                 r_port;
        sc_uint<4*REG_SIZE>                            r;

        shared_in<std::array<sc_uint<1>, 4>>           z_port;
        std::array<sc_uint<1>, 4>                      z;

        
        shared_in<BaseAddress>                         address_port;
        BaseAddress                                    base_address;

        // primary outputs
        shared_out<mem_if_t>                           mem_rd_req;
        shared_out<mem_if_t>                           z_rd_req;
        

        // buffer signals
        shared_in <bool>                               buffer_valid_o;
        shared_in <std::array<sc_uint<8>, 4>>          buffer_data_o;

        shared_out<bool>                               hintgen_en;
        bool                                           hint_en;

        shared_in<sc_uint<MLDSA_MEM_ADDR_WIDTH>>       reg_wr_addr_port_in;
        shared_out<sc_uint<MLDSA_MEM_ADDR_WIDTH>>      reg_wr_addr_port;
        sc_uint<MLDSA_MEM_ADDR_WIDTH>                  reg_wr_addr;
        
        //std::array<sc_uint<8>, 4>                      reg_wrdata;
        bool                                           reg_wren;

        std::array<sc_uint<1>, 4>                      hint;
        sc_uint<8>                                     hintsum;

        shared_out<sc_uint<8>>                         index_count_port;
        
        shared_out<std::array<sc_uint<8>, 8>>          max_index_buffer_port;
        std::array<sc_uint<8>, 8>                      max_index_buffer;

        
        sc_uint<14>                                    cnt;
        sc_uint<3>                                     poly_cnt;

        mem_if_t                                       rd_req, zrd_req;

        std::array<sc_uint<1>, 4> hintgen_comp(sc_uint<96> r_var, std::array<sc_uint<1>, 4> z_neq_z_var) const{
            sc_uint<96>       r = r_var;
            std::array<sc_uint<1>, 4> z_neq_z = z_neq_z_var;
            
            sc_uint<1> r_lt_gamma2;
            sc_uint<1> r_gt_q_minus_gamma2;
            sc_uint<1> r_eq_q_minus_gamma2;
            sc_uint<1> or1_res, or2_res, and_res, not_res;

            std::array<sc_uint<1>, 4>                   hint;

            sc_uint<23> r_calc;
            for (sc_uint<23> i = 0; i < sc_uint<23> (4); i++){
                r_calc = r.range(i * sc_uint<23> (REG_SIZE) + sc_uint<23> (22), i * sc_uint<23> (REG_SIZE));
                if (r_calc <= MLDSA_GAMMA2) {
                    r_lt_gamma2 = sc_uint<1> (1);
                }else{
                    r_lt_gamma2 = sc_uint<1> (0);
                }

                if (r_calc >= Q_MINUS_GAMMA2) {
                    r_gt_q_minus_gamma2 = sc_uint<1> (1);
                }else{
                    r_gt_q_minus_gamma2 = sc_uint<1> (0);
                }

                if (r_calc == Q_MINUS_GAMMA2) {
                    r_eq_q_minus_gamma2 = sc_uint<1> (1);
                }else{
                    r_eq_q_minus_gamma2 = sc_uint<1> (0);
                }

                or1_res = r_lt_gamma2 | r_gt_q_minus_gamma2;
                and_res = r_eq_q_minus_gamma2 & z_neq_z[i];
                //not_res = or1_res ? sc_uint<1> (0) : sc_uint<1> (1);
                or2_res = (or1_res ? sc_uint<1> (0) : sc_uint<1> (1)) | and_res;
                hint[i] = or2_res;
            }
            return hint; // !zeroize
        }

        std::array<sc_uint<8>, 4> index_comp(sc_uint<8> index_count) const{
          std::array<sc_uint<8>, 4> index;
          for (sc_uint<8> i = 0; i < 4; i++){
            index[i] = index_count + sc_uint<8> (i);
          }
          return index;
        }

        std::array<sc_uint<8>, 8> max_index_buffer_comp(std::array<sc_uint<8>, 8> max_index_buffer_var, sc_uint<8> hintsum) const{
          std::array<sc_uint<8>, 8> max_index_buffer = max_index_buffer_var;
          for (sc_uint<8> i = 1; i < 8; i++){
            max_index_buffer[i - 1] = max_index_buffer[i];
          }
          max_index_buffer[7] = hintsum;
          return max_index_buffer;
        }

        std::array<sc_uint<8>, 4> max_index_buffer_data_comp(sc_uint<64>  max_index_buffer_var, sc_uint<8> sel) const{
          std::array<sc_uint<8>, 4> wr_data;
          sc_uint<64>               max_index_buffer = max_index_buffer_var;
          if (sel == 0){
            wr_data[3] = max_index_buffer.range(7, 0);
            wr_data[2] = 0;
            wr_data[1] = 0;
            wr_data[0] = 0;
          }
          else if(sel == 1){
            wr_data[3] = max_index_buffer.range(39, 32);
            wr_data[2] = max_index_buffer.range(31, 24);
            wr_data[1] = max_index_buffer.range(23, 16);
            wr_data[0] = max_index_buffer.range(15, 8);
          }
          else if(sel == 2){
            wr_data[3] = 0;
            wr_data[2] = max_index_buffer.range(63, 56);
            wr_data[1] = max_index_buffer.range(55, 48);
            wr_data[0] = max_index_buffer.range(47, 40);
          }
          return wr_data;
        }

        void run(){
            cnt         = 0;
            poly_cnt    = 0;
            hintsum     = 0;
            hint        = {0,0,0,0};

            rd_req.rd_wr_en = RW_IDLE;
            rd_req.addr = 0;
            mem_rd_req->set(rd_req);

            zrd_req.rd_wr_en = RW_IDLE;
            zrd_req.addr     = 0;
            z_rd_req->set(zrd_req);

            while (true){
                rd_req.rd_wr_en = RW_IDLE;
                rd_req.addr     = cnt;
                mem_rd_req->set(rd_req);

                zrd_req.rd_wr_en = RW_IDLE;
                zrd_req.addr     = 0;
                z_rd_req->set(zrd_req);
                
                makehint_enable_port->read(makehint_enable, "MH_IDLE");
                max_index_buffer   = {0,0,0,0,0,0,0,0};
                hintsum            = 0;
                poly_cnt           = 0;
                hint               = {0,0,0,0};
                
                reg_wr_addr_port->set(0);
                index_count_port->set(0);
                hintgen_en->set(false);
            
                address_port->get(base_address);
                cnt = base_address.mem_base_addr;

                while(true){
                    hint              = {0,0,0,0};
                    max_index_buffer_port->set(max_index_buffer);
                    do{ 
                        // sending requests
                        rd_req.rd_wr_en = RW_READ;
                        rd_req.addr     = cnt;
                        mem_rd_req->set(rd_req);

                        zrd_req.rd_wr_en = RW_READ;
                        zrd_req.addr     = cnt - base_address.mem_base_addr;
                        z_rd_req->set(zrd_req);  

                        insert_state("MH_RD_MEM");
                        r_port->get(r);
                        z_port->get(z);


                        hintsum = hintsum + hint[0] + hint[1] + hint[2] + hint[3];
                        hint = hintgen_comp(r, z);
                        
                        index_count_port->set((cnt - base_address.mem_base_addr) * 4);
                        hintgen_en->set(true);

                        buffer_valid_o->get(reg_wren);

                        if(reg_wren){ 
                          reg_wr_addr_port_in->get(reg_wr_addr);
                          //reg_wr_addr = base_address.dest_base_addr + reg_wr_addr + 1; // TODO: check this part again with rtl
                          reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);
                        }

                        cnt = cnt + 1;
  
                    } while (cnt <= (((poly_cnt + 1) * 64) - 1 + base_address.mem_base_addr));
                    
                    if ((poly_cnt + 1) == MLDSA_K){
                      cnt = base_address.mem_base_addr;
                    }
                    
                    rd_req.rd_wr_en = RW_IDLE; // optimize this
                    rd_req.addr     = cnt;
                    mem_rd_req->set(rd_req);
                    
                    zrd_req.rd_wr_en = RW_IDLE;
                    zrd_req.addr     = cnt - base_address.mem_base_addr;
                    z_rd_req->set(zrd_req); 
                    

                    buffer_valid_o->get(reg_wren);
                    
                    if(reg_wren){    
                      reg_wr_addr_port_in->get(reg_wr_addr);
                      reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);
                    }

                    insert_state("MH_WAIT1");

                    index_count_port->set((cnt - base_address.mem_base_addr) * 4);
                    hintgen_en->set(false);
                    buffer_valid_o->get(reg_wren);
                    hintsum = hintsum + hint[0] + hint[1] + hint[2] + hint[3];
                    
                    if(reg_wren){    
                      reg_wr_addr_port_in->get(reg_wr_addr);
                      reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);
                    }

                    insert_state("MH_WAIT2");

                    max_index_buffer = max_index_buffer_comp(max_index_buffer, hintsum);
                    //max_index_buffer_port->set(max_index_buffer);
                    buffer_valid_o->get(reg_wren);
                    
                    if(reg_wren){    
                      reg_wr_addr_port_in->get(reg_wr_addr);
                      reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);
                    }

                    if ((poly_cnt + 1) == MLDSA_K){
                        hint              = {0,0,0,0};
                        poly_cnt          = 0;
                        break;
                    }
                    poly_cnt = poly_cnt + 1;
                } 
                max_index_buffer_port->set(max_index_buffer);

                insert_state("MH_FLUSH_SBUF"); 
                
                reg_wr_addr_port->set(base_address.dest_base_addr + OMEGA/4);

                insert_state("MH_RD_IBUF_LOW");

                reg_wr_addr_port_in->get(reg_wr_addr);
                reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);

                insert_state("MH_RD_IBUF_MID");


                reg_wr_addr_port_in->get(reg_wr_addr);
                reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);

                insert_state("MH_RD_IBUF_HIGH");

                reg_wr_addr_port_in->get(reg_wr_addr);
                reg_wr_addr_port->set(base_address.dest_base_addr + reg_wr_addr + 1);
            }
        }
};



#endif