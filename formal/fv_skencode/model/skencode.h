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

#ifndef _SKENCODE_H_
#define _SKENCODE_H_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q                 8380417
#define MLDSA_Q_1               8380416
#define MLDSA_Q_2               8380415
#define MLDSA_K                 8
#define MLDSA_L                 7
#define MLDSA_N                 256

#define MLDSA_MEM_ADDR_WIDTH    14
#define MEM_ADDR_WIDTH          15
#define AHB_DATA_WIDTH          32
#define REG_SIZE                24

#define THE_LAST_ADDR           959
#define THE_LAST_API            360


enum mem_rw_mode {RW_IDLE, RW_READ, RW_WRITE};

struct mem_if_t {
            mem_rw_mode rd_wr_en;
            sc_uint<14> addr;
        };

/* struct EncodeResult {
    sc_uint<32> encoded_data;
    sc_uint<1> error_flag;
}; */
        



SC_MODULE(skencode){

    public:
        SC_CTOR(skencode){
            SC_THREAD(run);
        }

        // Declare ports as required by the design.
        // For example:
        //blocking_in<data>  port_in;
        //blocking_out<data> port_out;
        //master_in<data>    port_in;
        //master_out<data>   port_out;
        //shared_in<data>    port_in;
        //shared_out<data>   port_out
        //blocking_in<sc_uint<8>> data_in;
        //sc_uint<8> data;
        //sc_uint<8> local_data;

        struct BaseAddress {
            sc_uint<15> source;
            sc_uint<15> destination;
        };

        //blocking_in<bool>   skencode_enable_port;
        //bool                skencode_enable;

        blocking_in<BaseAddress> start_port;
        BaseAddress base_address;

        master_in<std::array<sc_uint<REG_SIZE>, 8>> mem_rd_data_prev;
        master_in<std::array<sc_uint<REG_SIZE>, 8>> mem_rd_data_curr;
        master_in<std::array<sc_uint<REG_SIZE>, 8>> mem_rd_data_prev_3, mem_rd_data_prev_4, mem_rd_data_prev_5;
        std::array<sc_uint<REG_SIZE>, 8> rd_data_prev, rd_data_curr, rd_data_prev_3, rd_data_prev_4, rd_data_prev_5;

        shared_out<sc_uint<AHB_DATA_WIDTH>> keymem_a_wr_data;

        //Interface
        master_out<mem_if_t> mem_a_rd_req;
        master_out<mem_if_t> mem_b_rd_req;
        master_out<mem_if_t> keymem_a_wr_req;

        mem_if_t        rd_req_a, rd_req_b, wr_req_a;

        // shared_in<sc_uint<14>> current_num_mem_operands, current_num_api_operands;
        // shared_in<sc_uint<7>>  current_buffer;
        // shared_in<sc_uint<2>>  prod_select;
        sc_uint<14>            num_mem_operands, num_api_operands;
        sc_uint<2>             consumer_selector;
        sc_uint<2>             producer_selector;

        shared_out<sc_uint<14>> num_mem_operands_new, num_api_operands_new;
        shared_out<sc_uint<2>>  buffer_new;

        master_out<bool>        skencode_done;

        shared_in<sc_uint<32>>  top_bits;
        sc_uint<32>             temp;

        sc_uint<1>                    error_flag;
        bool  exit_loop;
        


        // Declare intermediate variables for each port of the same data type.

            // Encoding logic for each 24-bit input.
            sc_uint<32> encode(std::array<sc_uint<REG_SIZE>, 8> data_to_be_encoded) const {
                sc_uint<32> encoded_data = 0;
                sc_uint<8> encoding_error = 0;
                sc_uint<32> top_zeros = 0x00FFFFFF;

                for(int i = 0; i < 8; ++i){
                    if(2 < data_to_be_encoded[i] && data_to_be_encoded[i] < MLDSA_Q_2 || MLDSA_Q_1 < data_to_be_encoded[i]){
                        encoded_data = ((sc_uint<24>(0)) << sc_uint<24>(i*3)) | encoded_data;
                        encoding_error = ((sc_uint<8>(1)) << sc_uint<8>(i)) | encoding_error;
                    }else {
                        encoded_data = (((sc_uint<24>(2) + MLDSA_Q - data_to_be_encoded[i]) % MLDSA_Q) << sc_uint<24>(i*3)) | encoded_data;
                        encoding_error = ((sc_uint<8>(0)) << sc_uint<8>(i)) | encoding_error;
                    }
                }
                encoded_data = encoded_data & top_zeros;
                return encoded_data;

            }

            /* EncodeResult encode(std::array<sc_uint<REG_SIZE>, 8> data_to_be_encoded) const {
                sc_uint<32> encoded_data = 0;
                sc_uint<8> encoding_error = 0;
                sc_uint<32> top_zeros = 0x00FFFFFF;
            
                for(int i = 0; i < 8; ++i){
                    if(2 < data_to_be_encoded[i] && data_to_be_encoded[i] < MLDSA_Q_2 || MLDSA_Q_1 < data_to_be_encoded[i]){
                        encoded_data = ((sc_uint<24>(0)) << sc_uint<24>(i*3)) | encoded_data;
                        encoding_error = ((sc_uint<8>(1)) << sc_uint<8>(i)) | encoding_error;
                    } else {
                        encoded_data = (((sc_uint<24>(2) + MLDSA_Q - data_to_be_encoded[i]) % MLDSA_Q) << sc_uint<24>(i*3)) | encoded_data;
                        encoding_error = ((sc_uint<8>(0)) << sc_uint<8>(i)) | encoding_error;
                    }
                }
                
                encoded_data = encoded_data & top_zeros;
                sc_uint<1> error_flag = 0;
                for (int i = 0; i < 8; ++i) {
                    error_flag |= (encoding_error[i]);  // Bitwise OR each bit
                }
            
                return {encoded_data, error_flag};
            } */


            sc_uint<1> encode_error(std::array<sc_uint<REG_SIZE>, 8> data_to_be_encoded) const {
                sc_uint<32> encoded_data = 0;
                sc_uint<8> encoding_error = 0;
                sc_uint<32> top_zeros = 0x00FFFFFF;

                for(int i = 0; i < 8; ++i){
                    if(2 < data_to_be_encoded[i] && data_to_be_encoded[i] < MLDSA_Q_2 || MLDSA_Q_1 < data_to_be_encoded[i]){
                        encoding_error = ((sc_uint<8>(1)) << sc_uint<8>(i)) | encoding_error;
                    }else {
                        encoding_error = ((sc_uint<8>(0)) << sc_uint<8>(i)) | encoding_error;
                    }
                }
                sc_uint<1> error_flag = 0;
                for (int i = 0; i < 8; ++i) {
                    error_flag |= (encoding_error[i]);  // Bitwise OR each bit
                }
                return error_flag;

            } 
            

            //Bitwise-OR function to combine output data
            sc_uint<32> bitwise_or(sc_uint<32> operandA, sc_uint<32> operandB) const{

                return operandA | operandB; 
            }

            //modulo function to compute shift amount
            sc_uint<14> shift_amount(sc_uint<14> num_api_operands) const{

                return (num_api_operands%3)*8;
            }

            //modulo function to compute shift amount
            sc_uint<14> shift_amount_first(sc_uint<14> num_api_operands) const{

                return (3-num_api_operands%3)*8;
            }
            


        void run() {
            
            rd_req_a.addr       = 0;
            rd_req_b.addr       = 0;
            rd_req_a.rd_wr_en   = RW_IDLE;
            rd_req_b.rd_wr_en   = RW_IDLE;
            mem_a_rd_req        ->master_write(rd_req_a);
            mem_b_rd_req        ->master_write(rd_req_b);
            
            wr_req_a.addr       =  0;
            wr_req_a.rd_wr_en   =  RW_IDLE;
            keymem_a_wr_req     -> master_write(wr_req_a);

            skencode_done       -> master_write(false);
            error_flag          =  0;

            num_mem_operands = 0;
            num_api_operands = 0;
            consumer_selector = 0;
            producer_selector = 0;


            while (true) {
/* 
                if(error_flag == 0 && !exit_loop){
                    num_mem_operands = 0;
                    consumer_selector = 0;
                    producer_selector = 0;
                } */

                start_port-> read(base_address, "IDLE");
    
                wr_req_a.addr       = 0;
                wr_req_a.rd_wr_en   = RW_IDLE;
                keymem_a_wr_req     -> master_write(wr_req_a);

                rd_req_a.addr       = base_address.source ;
                rd_req_b.addr       = base_address.source + sc_uint<15>(1);
                rd_req_a.rd_wr_en   = RW_READ;
                rd_req_b.rd_wr_en   = RW_READ;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                skencode_done       -> master_write(false);

                num_mem_operands = num_mem_operands + 2;
                num_api_operands = 0;
                consumer_selector = 0;
                producer_selector = 0;

                
                insert_state("READ_and_ENC"); //skipped READ, now in READ_and_ENC state

                wr_req_a.addr       = 0;
                wr_req_a.rd_wr_en   = RW_IDLE;
                keymem_a_wr_req     -> master_write(wr_req_a);

                rd_req_a.addr       = base_address.source + sc_uint<14>(2);
                rd_req_b.addr       = base_address.source + sc_uint<14>(3);
                rd_req_a.rd_wr_en   = RW_READ;
                rd_req_b.rd_wr_en   = RW_READ;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                num_mem_operands = num_mem_operands + 2;
                num_api_operands = 0;
                consumer_selector = 0;
                producer_selector = 0;

                skencode_done       -> master_write(false);
                
                insert_state("READ_ENC_and_CONSUME___IDLE");
                
                mem_rd_data_prev -> master_read(rd_data_prev);
                mem_rd_data_curr -> master_read(rd_data_curr);

                top_bits -> get(temp);
                temp = temp & 0xFF000000;
                keymem_a_wr_data -> set( bitwise_or(temp, encode(rd_data_curr)) ); // call function to call bitwise or 
                error_flag = encode_error(rd_data_curr);

                wr_req_a.addr       = 0;
                wr_req_a.rd_wr_en   = RW_IDLE;
                keymem_a_wr_req     -> master_write(wr_req_a);
                
                rd_req_a.addr       = base_address.source + sc_uint<14>(4);
                rd_req_b.addr       = base_address.source + sc_uint<14>(5);
                rd_req_a.rd_wr_en   = RW_READ;
                rd_req_b.rd_wr_en   = RW_READ;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                num_mem_operands = num_mem_operands + 2;
                num_api_operands = 0;
                consumer_selector = 0;
                producer_selector = producer_selector + 1;

                skencode_done       -> master_write(false);

                if(error_flag == 1){
                    continue;
                }

                do {
                    // prod_select -> get(producer_selector);
                    insert_state("READ_ENC_and_CONSUME___WAIT_BUFFER");
                } while(producer_selector != 1);
 
                mem_rd_data_prev -> master_read(rd_data_prev);
                mem_rd_data_curr -> master_read(rd_data_curr);

                keymem_a_wr_data -> set( bitwise_or( (encode(rd_data_curr)  << 24) , encode(rd_data_prev)  ) );
                error_flag = encode_error(rd_data_curr)  | encode_error(rd_data_prev) ;

                wr_req_a.addr       = base_address.destination;
                wr_req_a.rd_wr_en   = RW_WRITE;
                keymem_a_wr_req     -> master_write(wr_req_a);
                
                rd_req_a.addr       = base_address.source + sc_uint<14>(6);
                rd_req_b.addr       = base_address.source + sc_uint<14>(7);
                rd_req_a.rd_wr_en   = RW_READ;
                rd_req_b.rd_wr_en   = RW_READ;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                num_mem_operands = num_mem_operands + 2;
                num_api_operands = num_api_operands + 1;
                consumer_selector = 0;
                producer_selector = producer_selector + 1;
                
                skencode_done       -> master_write(false);

                if(error_flag == 1){
                    // exit_loop = true;
                    continue;
                }

                do {

                    insert_state("READ_ENC_and_CONSUME___looped");
                    
                    // current_num_mem_operands -> get(num_mem_operands); //num_mem_operands, should be 8 at this point
                    // current_buffer -> get(consumer_selector);      //consumer selector, should be 1 at this point
                    // current_num_api_operands -> get(num_api_operands); //num_api_operands, should be 1 at this point

                    mem_rd_data_prev -> master_read(rd_data_prev);
                    mem_rd_data_curr -> master_read(rd_data_curr);
                    mem_rd_data_prev_3 -> master_read(rd_data_prev_3);

                    
                    
                    

                    if (num_api_operands%3 != 0 && consumer_selector < 2) {   //write req condition

                        wr_req_a.addr       = base_address.destination + num_api_operands;
                        wr_req_a.rd_wr_en   = RW_WRITE;
                        keymem_a_wr_req     -> master_write(wr_req_a);

                        keymem_a_wr_data -> set( bitwise_or( encode(rd_data_curr)  << (shift_amount_first(num_api_operands)), (encode(rd_data_prev) ) >> shift_amount(num_api_operands) ) );
                        error_flag = encode_error(rd_data_curr)  | encode_error(rd_data_prev) ;

                        producer_selector = producer_selector + 1;
                        num_api_operands = num_api_operands + 1;
                        consumer_selector = consumer_selector + 1;

                    }
                    else if (num_api_operands%3 == 0 && consumer_selector == 2){ //stall condition
                        wr_req_a.addr       = 0;
                        wr_req_a.rd_wr_en   = RW_IDLE;
                        keymem_a_wr_req     -> master_write(wr_req_a);
                        
                        // num_api_operands = num_api_operands;
                        consumer_selector = 0;
                        producer_selector = producer_selector +1;

                        top_bits -> get(temp);
                        temp = temp & 0xFF000000;
                        keymem_a_wr_data -> set( bitwise_or( (encode(rd_data_prev_3)  << 24) , encode(rd_data_curr) ) );
                        error_flag = encode_error(rd_data_prev_3)  | encode_error(rd_data_curr) ;

                    }
                    else {  // wait_buffer
                        wr_req_a.addr       = base_address.destination + num_api_operands;
                        wr_req_a.rd_wr_en   = RW_WRITE;
                        keymem_a_wr_req     -> master_write(wr_req_a);

                        keymem_a_wr_data -> set(bitwise_or( (encode(rd_data_curr)  << shift_amount_first(num_api_operands)) , (encode(rd_data_prev)  >> shift_amount(num_api_operands)) ) );
                        error_flag = encode_error(rd_data_prev)  | encode_error(rd_data_curr) ;

                        producer_selector = producer_selector + 1;
                        num_api_operands = num_api_operands + 1;
                        consumer_selector = 0;

                    }
                    if (num_api_operands < THE_LAST_API - 1) { //make sure the last loop cycle outputs only an IDLE read req
                        rd_req_a.addr       = base_address.source + num_mem_operands;
                        rd_req_b.addr       = base_address.source + num_mem_operands + sc_uint<14>(1);
                        rd_req_a.rd_wr_en   = RW_READ;
                        rd_req_b.rd_wr_en   = RW_READ;
                        mem_a_rd_req        -> master_write(rd_req_a);
                        mem_b_rd_req        -> master_write(rd_req_b);

                        num_mem_operands = num_mem_operands + 2;

                        if(error_flag == 1){
                            // exit_loop = true;
                            break;
                        }
                    } else {
                        rd_req_a.addr       = 0;
                        rd_req_b.addr       = 0;
                        rd_req_a.rd_wr_en   = RW_IDLE;
                        rd_req_b.rd_wr_en   = RW_IDLE;
                        mem_a_rd_req        -> master_write(rd_req_a);
                        mem_b_rd_req        -> master_write(rd_req_b);

                        num_mem_operands = 0;
                        if(error_flag == 1){
                            // exit_loop = true;
                            break;
                        }
                    }

                    skencode_done       -> master_write(false);

                } while (num_api_operands < THE_LAST_API - 1); //we leave loop after 3rd to last write request ist made

                if(error_flag == 1){
                    continue;
                }

                insert_state("CONSUME___WRITE");
                // current_num_api_operands -> get(num_api_operands); //num_api_operands, should be 1 at this point

                mem_rd_data_prev -> master_read(rd_data_prev);
                mem_rd_data_curr -> master_read(rd_data_curr);

                keymem_a_wr_data -> set( bitwise_or( (encode(rd_data_curr)  << 8) , (encode(rd_data_prev)  >> 16) ));
                error_flag = encode_error(rd_data_prev)  | encode_error(rd_data_curr) ;

                wr_req_a.addr       = base_address.destination + num_api_operands;
                wr_req_a.rd_wr_en   = RW_WRITE;
                keymem_a_wr_req     -> master_write(wr_req_a);
                
                rd_req_a.addr       = 0;
                rd_req_b.addr       = 0;
                rd_req_a.rd_wr_en   = RW_IDLE;
                rd_req_b.rd_wr_en   = RW_IDLE;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                num_mem_operands = 0;
                num_api_operands = num_api_operands + 1;
                consumer_selector = consumer_selector + 1;
                producer_selector = 0;

                skencode_done       -> master_write(false);

                if(error_flag == 1){
                    continue;
                }

                insert_state("CONSUME_LAST___STALL");

                mem_rd_data_prev_3 -> master_read(rd_data_prev_3); //writes, what was saved in the buffer 3/4 CC ago
                mem_rd_data_prev_4 -> master_read(rd_data_prev_4);

                keymem_a_wr_data -> set( bitwise_or( (encode(rd_data_prev_3)  << 24) , encode(rd_data_prev_4)  ) );
                error_flag = encode_error(rd_data_prev_3)  | encode_error(rd_data_prev_4) ;

                wr_req_a.addr       = 0;
                wr_req_a.rd_wr_en   = RW_IDLE;
                keymem_a_wr_req     -> master_write(wr_req_a);
                
                rd_req_a.addr       = 0;
                rd_req_b.addr       = 0;
                rd_req_a.rd_wr_en   = RW_IDLE;
                rd_req_b.rd_wr_en   = RW_IDLE;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                num_mem_operands = 0;
                consumer_selector = 0;
                producer_selector = 0;

                skencode_done       -> master_write(false);

                if(error_flag == 1){
                    continue;
                }

                insert_state("DONE___GET_LAST");

                mem_rd_data_prev_4 -> master_read(rd_data_prev_4); //writes, what was saved in the buffer 4/5 CC ago
                mem_rd_data_prev_5 -> master_read(rd_data_prev_5);

                keymem_a_wr_data -> set( bitwise_or( (encode(rd_data_prev_4)  << 24) , encode(rd_data_prev_5)  ) );
                error_flag = encode_error(rd_data_prev_4)  | encode_error(rd_data_prev_5) ;

                wr_req_a.addr       = 0;
                wr_req_a.rd_wr_en   = RW_IDLE;
                keymem_a_wr_req     -> master_write(wr_req_a);
                
                rd_req_a.addr       = 0;
                rd_req_b.addr       = 0;
                rd_req_a.rd_wr_en   = RW_IDLE;
                rd_req_b.rd_wr_en   = RW_IDLE;
                mem_a_rd_req        -> master_write(rd_req_a);
                mem_b_rd_req        -> master_write(rd_req_b);

                skencode_done       -> master_write(true);


            }
            
        }
};

#endif