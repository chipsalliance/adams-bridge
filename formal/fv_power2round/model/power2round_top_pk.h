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

#ifndef _POWER2ROUND_
#define _POWER2ROUND_

#include "systemc.h"
#include "Interfaces.h"
#include <array>

#define REG_SIZE 24
#define MLDSA_N 256
#define MLDSA_K 8
#define MLDSA_D 13
#define AHB_DATA_WIDTH 32

#define MLDSA_MEM_ADDR_WIDTH 14
#define MAX_MEM_ADDR 510
#define power2_d_minus_one 4095 // ((1 << (MLDSA_D-1)) - 1)
#define power2_d 4096 // (1 << (MLDSA_D-1))
#define r1_output_size 10 // REG_SIZE-MLDSA_D-1


SC_MODULE(power2round_top){

    public:
        SC_CTOR(power2round_top){
            SC_THREAD(run);
        }


        struct BaseAddress {
            sc_uint<14> source;
            sc_uint<14> destination; 
        };

        blocking_in<BaseAddress> start_port; 
        BaseAddress base_address;

        struct Request {
            std::array<sc_uint<MLDSA_MEM_ADDR_WIDTH>, 2> addresses;
            bool idle;
            bool read;
            bool write;
        };
        master_out<Request> rd_req_out, wr_req_out;
        Request rd_req, wr_req;

        struct PkRequest {
            sc_uint<8> address;
            bool enable;
        };
        master_out<PkRequest> pk_wr_req_out;
        PkRequest pk_wr_req;

        shared_out<sc_uint<14>> rd_cnt_new, wr_cnt_new;
        shared_out<sc_uint<8>> buffer_new;
        shared_in<std::array<sc_uint<REG_SIZE>, 8>> rd_data_port;
        shared_out<std::array<sc_uint<AHB_DATA_WIDTH>, 2>> wr_data_port;
        shared_out<std::array<sc_uint<10>, 8>> pk_wr_data_port;
        shared_out<bool> done_port;
        shared_in<bool> enable_port;
        bool enable;


        shared_in<sc_uint<14>> current_rd_cnt, current_wr_cnt;
        shared_in<sc_uint<8>> current_buffer;
        sc_uint<14> rd_cnt, wr_cnt;
        sc_uint<8> buffer;
        std::array<sc_uint<REG_SIZE>, 8> mem_rd_data;
        std::array<sc_biguint<MLDSA_D>, 8> r0, r0_packed, r0_packed_reg;
        std::array<sc_uint<REG_SIZE-MLDSA_D-1>, 8> r1, r1_reg;
        std::array<sc_uint<AHB_DATA_WIDTH>, 2> sk_data_output;
        sc_biguint<168> buffer_data;

        struct SampleBuffer {
            sc_biguint<168> the_buffer;
            std::array<sc_uint<AHB_DATA_WIDTH>, 2> the_output;
        };
        SampleBuffer computer_o;
        

        std::array<sc_uint<r1_output_size>, 8> compute_r1 (std::array<sc_uint<REG_SIZE>, 8> data) const {
            std::array<sc_uint<r1_output_size>, 8> result;
            sc_uint<REG_SIZE> sum0;
            sc_uint<REG_SIZE> mask = ((1 << (r1_output_size)) - 1); // 1023 == 1111111111, 10 bits

            for(int i = 0; i < 8; i = i + 1){
                sum0 = ((data[i] << 1) >> 1) + power2_d_minus_one;
                result[i] = (sum0 >> MLDSA_D) & mask;
            }
            return result;
        }

        std::array<sc_biguint<MLDSA_D>, 8> compute_r0 (std::array<sc_uint<REG_SIZE>, 8> data) const {
            std::array<sc_biguint<MLDSA_D>, 8> result;
            std::array<sc_uint<r1_output_size>, 8> r1;
            sc_uint<REG_SIZE> sum1;
            sc_uint<REG_SIZE> mask = ((1 << MLDSA_D)-1); // 8191 == 1111111111111, 13 bits
            r1 = compute_r1(data);

            for(int i = 0; i < 8; i = i + 1){
                sum1 = ((data[i] << 1) >> 1) - (r1[i] << MLDSA_D);
                result[i] = sum1 & mask;
            }
            return result;
        }

        std::array<sc_biguint<MLDSA_D>, 8> skencode (std::array<sc_biguint<MLDSA_D>, 8> data) const {
            std::array<sc_biguint<MLDSA_D>, 8> result;

            for(int i = 0; i < 8; i = i + 1){
                result[i] = power2_d - data[i];
            }
            return result;
        }

        std::array<sc_uint<AHB_DATA_WIDTH>, 2> compute_sk_data_output (std::array<sc_biguint<13>, 8> data, sc_biguint<168> thebuffer, sc_uint<8> start, bool isFull) const {
            std::array<sc_uint<AHB_DATA_WIDTH>, 2> result;
            result[0] = (data[0] << 0) | (data[1] << 13) | (data[2] << 26);
            result[1] = (data[2] >> 6) | (data[3] << 7) | (data[4] << 20);
            return result;
        }

        std::array<sc_uint<AHB_DATA_WIDTH>, 2> get_sk_data_output (sc_biguint<168> thebuffer) const {
            std::array<sc_uint<AHB_DATA_WIDTH>, 2> result;
            result[0] = thebuffer;
            result[1] = thebuffer>>32;
            return result;
        }

        sc_biguint<168> compute_buffer (std::array<sc_biguint<13>, 8> data, sc_biguint<168> thebuffer, sc_uint<8> start, bool isFull) const {
            sc_biguint<168> result;
            if(isFull) {
                result = thebuffer>>64;
            } else {
                sc_biguint<168> temp = ((data[0] << 0) | (data[1] << 13) | (data[2] << 26) | (data[3] << 39) | (data[4] << 52) | (data[5] << 65) | (data[6] << 78) | (data[7] << 91));
                sc_uint<8> shifter = start >= 8 ? (start*8)-64 : (start*8);
                temp = temp<<(shifter);
            
                result = thebuffer>>64;
                result = temp | result;
            }
            return result;
        }


    void run(){

        rd_req.addresses[1] = sc_uint<14>(0);
        rd_req.addresses[0] = sc_uint<14>(1);
        rd_req.idle  = true;
        rd_req.read  = false;
        rd_req.write = false;
        rd_req_out->master_write(rd_req);

        wr_req.addresses[1] = sc_uint<14>(0);
        wr_req.addresses[0] = sc_uint<14>(1);
        wr_req.idle  = true;
        wr_req.read  = false;
        wr_req.write = false;
        wr_req_out->master_write(wr_req);

        pk_wr_req.address = sc_uint<8>(0);
        pk_wr_req.enable = false;
        pk_wr_req_out->master_write(pk_wr_req);

        buffer = 0;

        while(true) {

            r0_packed_reg = r0_packed;
            rd_data_port -> get(mem_rd_data);
            r0 = compute_r0(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            r0_packed = skencode(r0);

            if(!enable){
                start_port->read(base_address, "IDLE");
            }

            r0_packed_reg = r0_packed;
            rd_data_port -> get(mem_rd_data);
            r0 = compute_r0(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            r0_packed = skencode(r0);

            rd_req.addresses[1] = base_address.source + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(1);
            rd_req.idle  = false;
            rd_req.read  = true;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<8>(0);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);

            insert_state("REQ_1ST_DATA");

            r0_packed_reg = r0_packed;
            rd_data_port -> get(mem_rd_data);
            r0 = compute_r0(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            r0_packed = skencode(r0);

            rd_req.addresses[1] = base_address.source + sc_uint<14>(2);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(3);
            rd_req.idle  = false;
            rd_req.read  = true;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<8>(0);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);

            insert_state("REQ_2ND_DATA");

            r0_packed_reg = r0_packed;
            rd_data_port -> get(mem_rd_data);
            r0 = compute_r0(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            r0_packed = skencode(r0);

            rd_req.addresses[1] = base_address.source + sc_uint<14>(4);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(5);
            rd_req.idle  = false;
            rd_req.read  = true;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<8>(0);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);

            insert_state("REQ_3RD_DATA");

            r1_reg = r1;
            pk_wr_data_port->set(r1_reg);
            r0_packed_reg = r0_packed;
            rd_data_port -> get(mem_rd_data);
            r0 = compute_r0(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            r0_packed = skencode(r0);
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, 0, false);

            rd_req.addresses[1] = base_address.source + sc_uint<14>(6);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(7);
            rd_req.idle  = false;
            rd_req.read  = true;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<8>(0);
            pk_wr_req.enable = true;
            pk_wr_req_out->master_write(pk_wr_req);
            buffer_new->set(buffer+13);
            
            do {
                insert_state("LOOP"); 
                current_wr_cnt -> get(wr_cnt);
                current_rd_cnt -> get(rd_cnt);
                current_buffer -> get(buffer);

                rd_data_port -> get(mem_rd_data);

                // wr_req.addresses[1] = base_address.destination + wr_cnt + (wr_cnt==0 ? sc_uint<14>(0) : sc_uint<14>(2));
                // wr_req.addresses[0] = base_address.destination + wr_cnt + (wr_cnt==0 ? sc_uint<14>(1) : sc_uint<14>(3));
                wr_req.idle  = false;
                wr_req.read  = false;
                wr_req.write = true;
                // wr_req_out->master_write(wr_req);

                sk_data_output = get_sk_data_output(buffer_data);
                wr_data_port->set(sk_data_output);
                if (buffer+5 > 16 && buffer+5 < 22) { // [12:16]
                    wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2);
                    wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
                    r1_reg = r1;
                    r1 = compute_r1(mem_rd_data);
                    pk_wr_req.address = (rd_cnt-4) / 2;
                    rd_req.addresses[1] = base_address.source + rd_cnt + sc_uint<14>(0);
                    rd_req.addresses[0] = base_address.source + rd_cnt + sc_uint<14>(1);
                    r0_packed_reg = r0_packed;
                    buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, false);
                } else if(buffer+5 >= 22) { // [17:+]
                    wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2);
                    wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
                    pk_wr_req.address = wr_cnt == 818 ? (rd_cnt-4) / 2 : (rd_cnt-6) / 2;
                    rd_req.addresses[1] = base_address.source + rd_cnt + sc_uint<14>(0);
                    rd_req.addresses[0] = base_address.source + rd_cnt + sc_uint<14>(1);
                    rd_cnt_new->set(rd_cnt+2);
                    
                    buffer_new->set(buffer - 8);
                    buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, true);
                } else { // [0:11]
                    wr_req.addresses[1] = base_address.destination + wr_cnt + (wr_cnt==0 ? sc_uint<14>(0) : sc_uint<14>(2));
                    wr_req.addresses[0] = base_address.destination + wr_cnt + (wr_cnt==0 ? sc_uint<14>(1) : sc_uint<14>(3));
                    r1_reg = r1;
                    r1 = compute_r1(mem_rd_data);
                    pk_wr_req.address = (rd_cnt-4) / 2;
                    rd_req.addresses[1] = base_address.source + rd_cnt + (buffer+13 > 16 && buffer+13 < 22 ? sc_uint<14>(0) : sc_uint<14>(2));
                    rd_req.addresses[0] = base_address.source + rd_cnt + (buffer+13 > 16 && buffer+13 < 22 ? sc_uint<14>(1) : sc_uint<14>(3));
                    rd_cnt_new->set(rd_cnt+2);
                    
                    buffer_new->set(buffer + 5);
                    r0_packed_reg = r0_packed;
                    buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, false);
                }
                wr_req_out->master_write(wr_req);
                rd_req.idle  = false;
                rd_req.read  = true;
                rd_req.write = false;
                rd_req_out->master_write(rd_req);

                pk_wr_req.enable = wr_cnt==0 ? !(buffer+13 > 16 && buffer+13 < 22) : !(buffer+5 > 16 && buffer+5 < 22);
                pk_wr_req_out->master_write(pk_wr_req);
                
                wr_cnt_new->set(wr_cnt+2);

                r0 = compute_r0(mem_rd_data);
                r0_packed = skencode(r0);
                pk_wr_data_port->set(r1_reg);

            } while (wr_cnt < 818);

            insert_state("LAST_READ");

            rd_req.addresses[1] = base_address.source + rd_cnt + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + rd_cnt + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2); // 822
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
            wr_req.idle  = false;
            wr_req.read  = false;
            wr_req.write = true;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = (rd_cnt-2) / 2;
            pk_wr_req.enable = !(buffer+5 > 16 && buffer+5 < 22);
            pk_wr_req_out->master_write(pk_wr_req);
            
            r1_reg = r1;
            pk_wr_data_port->set(r1_reg);
            rd_data_port -> get(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            r0_packed_reg = r0_packed;
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, false);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE1");

            rd_req.addresses[1] = base_address.source + rd_cnt + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + rd_cnt + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2); // 824
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
            wr_req.idle  = false;
            wr_req.read  = false;
            wr_req.write = true;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = rd_cnt / 2;
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);

            r1_reg = !(buffer+5 > 16 && buffer+5 < 22) ? r1 : r1_reg;
            pk_wr_data_port->set(r1_reg);
            rd_data_port -> get(mem_rd_data);
            r1 = compute_r1(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            r0_packed_reg = r0_packed;
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, true);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE2");

            rd_req.addresses[1] = base_address.source + rd_cnt + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + rd_cnt + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2); // 826
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
            wr_req.idle  = false;
            wr_req.read  = false;
            wr_req.write = true;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<14>(255);
            pk_wr_req.enable = true;
            pk_wr_req_out->master_write(pk_wr_req);
            rd_data_port -> get(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            buffer_data = compute_buffer(r0_packed, buffer_data, buffer, false);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE3");

            rd_req.addresses[1] = base_address.source + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2); // 828
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
            wr_req.idle  = false;
            wr_req.read  = false;
            wr_req.write = true;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<14>(255);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);
            rd_data_port -> get(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            r0_packed_reg = r0_packed;
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, false);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE4");

            rd_req.addresses[1] = base_address.source + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(2); // 830
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(3);
            wr_req.idle  = false;
            wr_req.read  = false;
            wr_req.write = true;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<14>(255);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);
            rd_data_port -> get(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            r0_packed_reg = r0_packed;
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, true);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE5");

            rd_req.addresses[1] = base_address.source + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<14>(0);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);
            rd_data_port -> get(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            buffer_data = compute_buffer(r0_packed, buffer_data, buffer, false);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            insert_state("ONLY_WRITE6");

            rd_req.addresses[1] = base_address.source + sc_uint<14>(0);
            rd_req.addresses[0] = base_address.source + sc_uint<14>(1);
            rd_req.idle  = true;
            rd_req.read  = false;
            rd_req.write = false;
            rd_req_out->master_write(rd_req);

            wr_req.addresses[1] = base_address.destination + wr_cnt + sc_uint<14>(0);
            wr_req.addresses[0] = base_address.destination + wr_cnt + sc_uint<14>(1);
            wr_req.idle  = true;
            wr_req.read  = false;
            wr_req.write = false;
            wr_req_out->master_write(wr_req);

            pk_wr_req.address = sc_uint<14>(0);
            pk_wr_req.enable = false;
            pk_wr_req_out->master_write(pk_wr_req);
            rd_data_port -> get(mem_rd_data);
            sk_data_output = get_sk_data_output(buffer_data);
            wr_data_port->set(sk_data_output);
            r0_packed_reg = r0_packed;
            buffer_data = compute_buffer(r0_packed_reg, buffer_data, buffer, false);
            r0 = compute_r0(mem_rd_data);
            r0_packed = skencode(r0);

            done_port->set(true);
            enable_port->get(enable);
            insert_state("DONE");
            done_port->set(false);
            pk_wr_data_port->set(std::array<sc_uint<REG_SIZE-MLDSA_D-1>, 8>{0,0,0,0,0,0,0,0});

        }
        
    }


};

#endif

// enable_to_done: cover property (power2round_ctrl_inst.enable ##1 power2round_ctrl_inst.done [->1]);
// enable_to_done: cover property (power2round_ctrl_inst.enable ##1 power2round_ctrl_inst.mem_rd_addr == 'd1010 [->1]);
// mem_to_done: cover property (power2round_ctrl_inst.mem_rd_addr=='d1450 ##1 power2round_ctrl_inst.done [->1]);
