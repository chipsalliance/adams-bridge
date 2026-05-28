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

#ifndef _pkdecode_
#define _pkdecode_

#include "systemc.h"
#include "Interfaces.h"

constexpr unsigned MLDSA_K = 8;
constexpr unsigned MLDSA_N = 256;
constexpr unsigned REG_SIZE = 24;
constexpr unsigned INPUT_COEFF_SIZE = 10;
constexpr unsigned API_ADDR_WIDTH = 16;

SC_MODULE(pkdecode) {
    public:
        SC_CTOR(pkdecode){
            SC_THREAD(run);
        }

        blocking_in<bool>start_port;
        bool start;

        struct BaseAddress {
            sc_uint<16> source;
            sc_uint<14> destination;
        };
        shared_in<BaseAddress> base_address_port;
        BaseAddress base_address;

        shared_out<sc_uint<16>> read_address_port;
        sc_uint<16> read_address;
        shared_in<sc_biguint<80>> read_data_port;
        sc_biguint<80> read_data;

        struct Request {
            std::array<sc_uint<14>, 2> addresses;
            bool idle;
            bool read;
            bool write;
        };
        shared_out<Request> write_request_port;
        Request write_request;
        shared_out<std::array<sc_uint<24>, 8>> write_data_port;

        shared_out<bool> done_port;

        sc_uint<32> api_operands, mem_operands;

        std::array<sc_uint<24>, 8> encoded_coeffs (sc_biguint<80> data) const {
            std::array<sc_uint<24>, 8> result;
            sc_uint<24> temp;
            sc_uint<24> mask = ((1 << 10) - 1); // 1023 == 1111111111, 10 bits
            for(int i = 0; i < 8; i = i + 1){
                temp = (data >> 10*i) & mask;
                result[i] = temp << 13;
            }
            return result;
        }

        void run() {
            write_request.addresses[1] = sc_uint<14>(0);
            write_request.addresses[0] = sc_uint<14>(0);
            write_request.idle  = true;
            write_request.read  = false;
            write_request.write = false;
            write_request_port->set(write_request);
            write_data_port->set({0, 0, 0, 0, 0, 0, 0, 0});

            // done_port->set(false);

            while (true) {
                ////////////////////
                // Initial values //
                ////////////////////
                read_address = sc_uint<14>(0);
                read_address_port->set(read_address);

                api_operands = sc_uint<9>(0);
                mem_operands = sc_uint<9>(0);

                start_port->read(start, "IDLE");
                base_address_port->get(base_address);
                done_port->set(false);
                
                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(encoded_coeffs(read_data));

                read_address = base_address.source;
                read_address_port->set(read_address);

                api_operands += sc_uint<9>(0);
                mem_operands += sc_uint<9>(0);

                insert_state("READ");

                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(encoded_coeffs(read_data));

                read_address = base_address.source + sc_uint<14>(api_operands);
                read_address_port->set(read_address);

                api_operands += sc_uint<9>(1);
                mem_operands += sc_uint<9>(0); 

                insert_state("READ_EXEC");

                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(encoded_coeffs(read_data));
                mem_operands += sc_uint<9>(0);

                do {
                    read_address = base_address.source + sc_uint<14>(api_operands);
                    read_address_port->set(read_address);

                    api_operands += sc_uint<9>(1);
                    insert_state("READ_WRITE");

                    write_request.addresses[1] = base_address.destination + sc_uint<14>(mem_operands);
                    write_request.addresses[0] = base_address.destination + sc_uint<14>(mem_operands+1);
                    write_request.idle  = false;
                    write_request.read  = false;
                    write_request.write = true;
                    write_request_port->set(write_request);
                    read_data_port->get(read_data);
                    write_data_port->set(encoded_coeffs(read_data));
                    mem_operands += sc_uint<9>(2);
                } while(api_operands < sc_uint<9>(256));

                read_address = base_address.source + sc_uint<14>(api_operands);
                read_address_port->set(read_address);

                api_operands += sc_uint<9>(1);

                insert_state("WRITE");

                write_request.addresses[1] = base_address.destination + sc_uint<14>(mem_operands);
                write_request.addresses[0] = base_address.destination + sc_uint<14>(mem_operands+1);
                write_request.idle  = false;
                write_request.read  = false;
                write_request.write = true;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(encoded_coeffs(read_data));

                read_address = sc_uint<14>(0);
                read_address_port->set(read_address);

                api_operands = sc_uint<9>(0);
                mem_operands += sc_uint<9>(2);

                insert_state("DONE");

                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(encoded_coeffs(read_data));

                done_port->set(true);
            }
        }
};

#endif

// till_done: cover property (pkdecode.pkdecode_enable ##1 pkdecode.pkdecode_done [->1]);