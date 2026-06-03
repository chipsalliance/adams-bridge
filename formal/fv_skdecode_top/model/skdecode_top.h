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

#ifndef _SKDECODE_TOP_
#define _SKDECODE_TOP_

#include "systemc.h"
#include "Interfaces.h"
#include <array>



#define MLDSA_D  13
#define REG_SIZE  24
#define ETA_SIZE  3
#define MLDSA_Q   8380417


enum class mem_rw_mode {fv_RW_IDLE, fv_RW_READ, fv_RW_WRITE};


struct mem_if_t {
            mem_rw_mode rd_wr_en;
            sc_uint<14> addr;
        };

SC_MODULE(skdecode_top){

    public:
        SC_CTOR(skdecode_top){
            SC_THREAD(run);
        }

        struct BaseAddress {
            sc_uint<14> source;
            sc_uint<14> destination;
        };

        //Inputs
        blocking_in<BaseAddress> start_port;
        shared_in<bool> s1s2_valid_in;
        shared_in<bool> t0_valid_in;
        //Outputs
        master_out<mem_if_t> keymem_a_rd_req;
        master_out<mem_if_t> keymem_b_rd_req;
        master_out<mem_if_t> mem_a_wr_req;
        master_out<mem_if_t> mem_b_wr_req;
        master_out<bool>        skdecode_done;
        master_out<bool>        s1_done;
        master_out<bool>        s2_done;
        master_out<bool>        t0_done;
        shared_out<std::array<sc_uint<REG_SIZE>, 4>> mem_a_wr_data;
        shared_out<std::array<sc_uint<REG_SIZE>, 4>> mem_b_wr_data;
        shared_out<bool> s1s2_stall_dummy_out; //just to  verify stall register given to s1s2 buffer (not real output)
       //Registers
        BaseAddress base_address;
        sc_biguint<10> counter;
        bool s1s2_valid;
        bool t0_valid;
        mem_if_t        rd_req_a, rd_req_b, wr_req_a, wr_req_b;
        sc_uint<14>            fv_kmem_rd_addr, fv_kmem_rd_addr_nxt;
        sc_uint<14>            fv_mem_wr_addr, fv_mem_wr_addr_nxt;
        std::array<sc_uint<ETA_SIZE>, 8> fv_s1s2_buf_data;
        std::array<sc_uint<MLDSA_D>, 4> fv_t0_buf_data;



        // Decoing logic
        std::array<sc_uint<REG_SIZE>, 4> decode_s1s2_a(std::array<sc_uint<ETA_SIZE>, 8> data_to_be_decoded) const {
            std::array<sc_uint<REG_SIZE>, 4> decoded_data = {0, 0, 0, 0};

            for(int i = 0; i < 4; ++i){
                if(data_to_be_decoded[i] >= 0 && data_to_be_decoded[i] < 5  ){
                    decoded_data[i] = (sc_uint<24>(2) - data_to_be_decoded[i] + MLDSA_Q)  % MLDSA_Q  ;
                }else {
                    decoded_data[i] = 0;
                }
            }
            return decoded_data;
        }

        std::array<sc_uint<REG_SIZE>, 4> decode_s1s2_b(std::array<sc_uint<ETA_SIZE>, 8> data_to_be_decoded) const {
            std::array<sc_uint<REG_SIZE>, 4> decoded_data = {0, 0, 0, 0};

            for(int i = 4; i < 8; ++i){
                if(data_to_be_decoded[i] >= 0 && data_to_be_decoded[i] < 5  ){
                    decoded_data[i-4] = (sc_uint<24>(2) - data_to_be_decoded[i] + MLDSA_Q)  % MLDSA_Q  ;
                }else {
                    decoded_data[i-4] = 0;
                }
            }
            return decoded_data;
        }

        std::array<sc_uint<REG_SIZE>, 4> decode_t0(std::array<sc_uint<MLDSA_D>, 4> data_to_be_decoded) const {
            std::array<sc_uint<REG_SIZE>, 4> decoded_data = {0, 0, 0, 0};

            for(int i = 0; i < 4; ++i){
                decoded_data[i] = (sc_uint<24>(4096) - data_to_be_decoded[i] + MLDSA_Q)  % MLDSA_Q  ;
            }
            return decoded_data;
        }

        
    void run(){

        // bool fv_t0_stall;
        counter = 0;

        rd_req_a.addr       = 0;
        rd_req_b.addr       = 0;
        rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
        rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
        keymem_a_rd_req        ->master_write(rd_req_a);
        keymem_b_rd_req        ->master_write(rd_req_b);
        
        wr_req_a.addr       = 0;
        wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
        wr_req_b.addr       = 0;
        wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
        mem_a_wr_req     ->master_write(wr_req_a);
        mem_b_wr_req     ->master_write(wr_req_b);

        mem_a_wr_data -> set({0, 0, 0, 0});
        mem_b_wr_data -> set({0, 0, 0, 0});

        skdecode_done       -> master_write(true);
        s1_done             -> master_write(false);
        s2_done             -> master_write(false);
        t0_done             -> master_write(false);



        while(true) {

            start_port-> read(base_address, "IDLE");
    
            wr_req_a.addr       = 0 /*base_address.destination *2*/ ;
            wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            mem_a_wr_req     -> master_write(wr_req_a);

            wr_req_b.addr       = 0 /*(base_address.destination *2) + 1*/ ;
            wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            mem_b_wr_req     -> master_write(wr_req_b);

            rd_req_a.addr       = base_address.source ;
            rd_req_b.addr       = base_address.source ;
            rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
            rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;

            if ((base_address.source & 1) == 0) {
                keymem_a_rd_req        -> master_write(rd_req_a);
                keymem_b_rd_req        -> master_write(rd_req_b);
            }
            else{
                keymem_a_rd_req        -> master_write(rd_req_b);
                keymem_b_rd_req        -> master_write(rd_req_a);
            }

            
            mem_a_wr_data -> set({0, 0, 0, 0});
            mem_b_wr_data -> set({0, 0, 0, 0});

            skdecode_done       -> master_write(false);
            s1_done             -> master_write(false);
            s2_done             -> master_write(false);
            t0_done             -> master_write(false);

            // t0_full= false;
            s1s2_stall_dummy_out->set(false);
            do {
                insert_state("RD_WR_s1");
                ++counter;
                skdecode_done       -> master_write(false);
                s1_done             -> master_write(false);
                s2_done             -> master_write(false);
                t0_done             -> master_write(false);
                // t0_full= false;

                //a-req will have address +1 except in counts 3,7,11,15,19....
                if ((counter) % 4 != 0) {
                    rd_req_a.addr       = fv_kmem_rd_addr + sc_uint<14>(1);
                    rd_req_b.addr       = fv_kmem_rd_addr + sc_uint<14>(1);
                    s1s2_stall_dummy_out->set(false);
                }
                else {
                    rd_req_a.addr       = fv_kmem_rd_addr + sc_uint<14>(0);
                    rd_req_b.addr       = fv_kmem_rd_addr + sc_uint<14>(0);
                    s1s2_stall_dummy_out->set(true);
                }
                //a-req will have read in counts 0,2,5, 8,10,13, 16,...
                if ((counter % 8 == 0 || counter % 8 == 2 || counter % 8 == 5) && counter != 224) {
                    rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                }
                else {
                    rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                }
                //b-req will have read in counts 1,4,6, 9,12,14, 17,...
                if ((counter % 8 == 1 || counter % 8 == 4 || counter % 8 == 6)) {
                    rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                }
                else {
                    rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                }

                if (s1s2_valid){
                    wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;
                    wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;

                    mem_a_wr_data -> set(decode_s1s2_a(fv_s1s2_buf_data));
                    mem_b_wr_data -> set(decode_s1s2_b(fv_s1s2_buf_data));
                }
                else{
                    wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                    wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;

                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }
                wr_req_a.addr       = fv_mem_wr_addr * 2 /*base_address.destination *2*/ ;
                wr_req_b.addr       = (fv_mem_wr_addr * 2) + 1  /*(base_address.destination *2) + 1*/ ;
                mem_a_wr_req     -> master_write(wr_req_a);
                mem_b_wr_req     -> master_write(wr_req_b);

    

                if ((base_address.source & 1) == 0) {
                    keymem_a_rd_req        -> master_write(rd_req_a);
                    keymem_b_rd_req        -> master_write(rd_req_b);
                }
                else{
                    keymem_a_rd_req        -> master_write(rd_req_b);
                    keymem_b_rd_req        -> master_write(rd_req_a);
                }



            } while (counter < 224 ); //h'df
            counter = 0;


            do {
                insert_state("RD_STG_WR_s1");

                s1s2_stall_dummy_out->set(false);

                s1s2_valid_in-> get(s1s2_valid);
                if (s1s2_valid){
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(false);
                    s2_done             -> master_write(false);
                    t0_done             -> master_write(false);
                    //rd_req_stable
                    //write data and req like prev value
                    mem_a_wr_data -> set(decode_s1s2_a(fv_s1s2_buf_data));
                    mem_b_wr_data -> set(decode_s1s2_b(fv_s1s2_buf_data));
                }
                else{
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(true);
                    s2_done             -> master_write(false);
                    t0_done             -> master_write(false);
                    // t0_full= false;
                    

                    //rd_req_stable
                    //write data zero, write_req idle like prev
                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }
            } while (s1s2_valid);


            insert_state("RD_STG_WR_STG_1");

            
            rd_req_a.addr       = fv_kmem_rd_addr ;
            rd_req_b.addr       = fv_kmem_rd_addr ;
            rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
            rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;


            wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            wr_req_a.addr       = fv_mem_wr_addr * 2 /*base_address.destination *2*/ ;
            wr_req_b.addr       = (fv_mem_wr_addr * 2) + 1  /*(base_address.destination *2) + 1*/ ;
            mem_a_wr_req     -> master_write(wr_req_a);
            mem_b_wr_req     -> master_write(wr_req_b);

            if ((base_address.source & 1) == 0) {
                keymem_a_rd_req        -> master_write(rd_req_a);
                keymem_b_rd_req        -> master_write(rd_req_b);
            }
            else{
                keymem_a_rd_req        -> master_write(rd_req_b);
                keymem_b_rd_req        -> master_write(rd_req_a);
            }

            mem_a_wr_data -> set({0, 0, 0, 0});
            mem_b_wr_data -> set({0, 0, 0, 0});

            skdecode_done       -> master_write(false);
            s1_done             -> master_write(true);
            s2_done             -> master_write(false);
            t0_done             -> master_write(false);
            // t0_full= false;
            s1s2_stall_dummy_out->set(false);


            do {
                insert_state("RD_WR_s2");
                ++counter;
                skdecode_done       -> master_write(false);
                s1_done             -> master_write(true);
                s2_done             -> master_write(false);
                t0_done             -> master_write(false);
                // t0_full= false;

                //a-req will have address +1 except in counts 3,7,11,15,19....
                if ((counter) % 4 != 0) {
                    rd_req_a.addr       = fv_kmem_rd_addr + sc_uint<14>(1);
                    rd_req_b.addr       = fv_kmem_rd_addr + sc_uint<14>(1);
                    s1s2_stall_dummy_out->set(false);
                }
                else {
                    rd_req_a.addr       = fv_kmem_rd_addr + sc_uint<14>(0);
                    rd_req_b.addr       = fv_kmem_rd_addr + sc_uint<14>(0);
                    s1s2_stall_dummy_out->set(true);
                }
                //a-req will have read in counts 0,2,5, 8,10,13, 16,...
                if ((counter % 8 == 0 || counter % 8 == 2 || counter % 8 == 5) && counter != 256) {
                    rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                }
                else {
                    rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                }
                //b-req will have read in counts 1,4,6, 9,12,14, 17,...
                if ((counter % 8 == 1 || counter % 8 == 4 || counter % 8 == 6)) {
                    rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                }
                else {
                    rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                }

                if (s1s2_valid){
                    wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;
                    wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;

                    mem_a_wr_data -> set(decode_s1s2_a(fv_s1s2_buf_data));
                    mem_b_wr_data -> set(decode_s1s2_b(fv_s1s2_buf_data));
                }
                else{
                    wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                    wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;

                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }
                wr_req_a.addr       = fv_mem_wr_addr * 2 /*base_address.destination *2*/ ;
                wr_req_b.addr       = (fv_mem_wr_addr * 2) + 1  /*(base_address.destination *2) + 1*/ ;
                mem_a_wr_req     -> master_write(wr_req_a);
                mem_b_wr_req     -> master_write(wr_req_b);
                
                if ((base_address.source & 1) == 0) {
                    keymem_a_rd_req        -> master_write(rd_req_a);
                    keymem_b_rd_req        -> master_write(rd_req_b);
                }
                else{
                    keymem_a_rd_req        -> master_write(rd_req_b);
                    keymem_b_rd_req        -> master_write(rd_req_a);
                }


            } while (counter < 256 ); //h'ff
            counter = 0;


            do {
                insert_state("RD_STG_WR_s2");

                s1s2_stall_dummy_out->set(false);

                s1s2_valid_in-> get(s1s2_valid);
                if (s1s2_valid){
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(true);
                    s2_done             -> master_write(false);
                    t0_done             -> master_write(false);

                    mem_a_wr_data -> set(decode_s1s2_a(fv_s1s2_buf_data));
                    mem_b_wr_data -> set(decode_s1s2_b(fv_s1s2_buf_data));
                }
                else{
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(true);
                    s2_done             -> master_write(true);
                    t0_done             -> master_write(false);

                    // t0_full= false;

                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }
            } while (s1s2_valid);


            insert_state("RD_STG_WR_STG_2");


            rd_req_a.addr       = fv_kmem_rd_addr ;
            rd_req_b.addr       = fv_kmem_rd_addr  + sc_uint<14>(1) ;
            rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
            rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_READ;
            keymem_a_rd_req        -> master_write(rd_req_a);
            keymem_b_rd_req        -> master_write(rd_req_b);

            wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            wr_req_a.addr       = fv_mem_wr_addr * 2 /*base_address.destination *2*/ ;
            wr_req_b.addr       = (fv_mem_wr_addr * 2) + 1  /*(base_address.destination *2) + 1*/ ;
            mem_a_wr_req     -> master_write(wr_req_a);
            mem_b_wr_req     -> master_write(wr_req_b);

            mem_a_wr_data -> set({0, 0, 0, 0});
            mem_b_wr_data -> set({0, 0, 0, 0});

            skdecode_done       -> master_write(false);
            s1_done             -> master_write(true);
            s2_done             -> master_write(true);
            t0_done             -> master_write(false);
            // t0_full= false;
            s1s2_stall_dummy_out->set(false);


            do {
                insert_state("RD_WR_t0");
                ++counter;
                skdecode_done       -> master_write(false);
                s1_done             -> master_write(true);
                s2_done             -> master_write(true);
                t0_done             -> master_write(false);

                //Read_req can not be checked here, because the stall is combinatorial logic, need additional manual assertions
                // fv_t0_stall_in->get(fv_t0_stall);
                // //it will be read with address increment, except in cycles: 7,15,23...
                // if (fv_t0_stall  || counter == 512) {
                //     rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                //     rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                // }
                // else {
                //     rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                //     rd_req_b.rd_wr_en   = mem_rw_mode::fv_RW_READ;
                // }
                // rd_req_a.addr       = fv_kmem_rd_addr + sc_uint<14>(2) ;
                // rd_req_b.addr       = fv_kmem_rd_addr  + sc_uint<14>(3) ;

                // keymem_a_rd_req        -> master_write(rd_req_a);
                // keymem_b_rd_req        -> master_write(rd_req_b);
    
                t0_valid_in-> get(t0_valid);
                if (t0_valid){
                    if ((fv_mem_wr_addr & 1) == 0) {
                        wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;
                        wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                    }
                    else{
                        wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                        wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_WRITE;
                    }

                    mem_a_wr_data -> set(decode_t0(fv_t0_buf_data));
                    mem_b_wr_data -> set(decode_t0(fv_t0_buf_data));
                }
                else{
                    wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
                    wr_req_b.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;

                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }

                wr_req_a.addr       = fv_mem_wr_addr;
                wr_req_b.addr       = fv_mem_wr_addr;
                mem_a_wr_req     -> master_write(wr_req_a);
                mem_b_wr_req     -> master_write(wr_req_b);
                
            } while (counter < 512 ); //h'1ff
            counter = 0;


            do {
                insert_state("RD_STG_WR_t0");

                t0_valid_in-> get(t0_valid);
                if (t0_valid){
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(true);
                    s2_done             -> master_write(true);
                    t0_done             -> master_write(false);

                    mem_a_wr_data -> set(decode_t0(fv_t0_buf_data));
                    mem_b_wr_data -> set(decode_t0(fv_t0_buf_data));
                }
                else{
                    skdecode_done       -> master_write(false);
                    s1_done             -> master_write(true);
                    s2_done             -> master_write(true);
                    t0_done             -> master_write(true);

                    // t0_full= false;
                    s1s2_stall_dummy_out->set(false);

                    mem_a_wr_data -> set({0, 0, 0, 0});
                    mem_b_wr_data -> set({0, 0, 0, 0});
                }
            } while (t0_valid);


            insert_state("RD_STG_WR_STG_3");
            
            rd_req_a.addr       = fv_kmem_rd_addr ;
            rd_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            keymem_a_rd_req        -> master_write(rd_req_a);
            keymem_b_rd_req        -> master_write(rd_req_a);

            wr_req_a.addr       = fv_mem_wr_addr;
            wr_req_a.rd_wr_en   = mem_rw_mode::fv_RW_IDLE;
            mem_a_wr_req     -> master_write(wr_req_a);
            mem_b_wr_req     -> master_write(wr_req_a);

            mem_a_wr_data -> set({0, 0, 0, 0});
            mem_b_wr_data -> set({0, 0, 0, 0});

            skdecode_done       -> master_write(true);
            s1_done             -> master_write(true);
            s2_done             -> master_write(true);
            t0_done             -> master_write(true);
            // t0_full= false;
            s1s2_stall_dummy_out->set(false);
        }
    }

};

#endif