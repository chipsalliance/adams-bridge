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

#ifndef _sigdecode_z_top_
#define _sigdecode_z_top_

#include "systemc.h"
#include "Interfaces.h"

// Declare data types here
// I.e., structs (or classes)
constexpr unsigned GAMMA1 = static_cast<unsigned>(1) << static_cast<unsigned>(19);
constexpr unsigned q = 8380417;

SC_MODULE(sigdecode_z_top) {
    public:
        SC_CTOR(sigdecode_z_top){
            SC_THREAD(run);
        }

        // Blocking IDLE state until DUV sees an asserted enable signal
        blocking_in<bool>start_port;
        bool start;

        struct BaseAddress {
            sc_uint<14> source;
            sc_uint<14> destination;
        };
        shared_in<BaseAddress> base_address_port;
        BaseAddress base_address;


        // Interface to read data
        struct Request {
            std::array<sc_uint<14>, 2> addresses;
            bool idle;
            bool read;
            bool write;
        };
        shared_out<Request> read_request_port;
        Request read_request;
        shared_in<std::array<sc_uint<20>, 8>> read_data_port;
        std::array<sc_uint<20>, 8> read_data;

        // Interface to write data
        shared_out<Request> write_request_port;
        Request write_request;
        shared_out<std::array<sc_uint<24>, 8>> write_data_port;

        // Flag when computation is finished
        shared_out<bool> done_port;

        // Declare intermediate variables for each port of the same data type.
        // These variables should be used to read/write data to/from the ports.
        sc_uint<9> operands;

        // Decode data
        sc_uint<24> decode_coefficient(sc_uint<20> data) const {
            sc_uint<24> result;

            result = ((GAMMA1 + q ) - sc_uint<24>(data)) % q;
            return result;
        }

        std::array<sc_uint<24>, 8> decode(std::array<sc_uint<20>, 8> data) const {
            std::array<sc_uint<24>, 8> result;

            for(int i = 0; i < 8; ++i) {
                result[i] = decode_coefficient(data[i]);
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

            done_port->set(false);

            while (true) {
                ////////////////////
                // Initial values //
                ////////////////////
                read_request.addresses[1] = sc_uint<14>(0);
                read_request.addresses[0] = sc_uint<14>(0);
                read_request.idle  = true;
                read_request.read  = false;
                read_request.write = false;
                read_request_port->set(read_request);

                operands = sc_uint<9>(0);

                start_port->read(start, "IDLE");
                base_address_port->get(base_address);

                ////////////////////////
                // Request first data //
                ////////////////////////
                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(decode(read_data));


                read_request.addresses[1] = base_address.source;
                read_request.addresses[0] = base_address.source + sc_uint<14>(1);
                read_request.idle  = false;
                read_request.read  = true;
                read_request.write = false;
                read_request_port->set(read_request);

                operands += sc_uint<9>(2);

                insert_state("READ_EXEC");

                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(decode(read_data));

                while(operands < sc_uint<9>(446)) {

                    read_data_port -> get(read_data);

                    read_request.addresses[1] = base_address.source + sc_uint<14>(operands);
                    read_request.addresses[0] = base_address.source + sc_uint<14>(operands) + sc_uint<14>(1);
                    read_request.idle  = false;
                    read_request.read  = true;
                    read_request.write = false;
                    read_request_port->set(read_request);

                    operands += sc_uint<9>(2);

                    insert_state("READ_EXEC_WRITE");

                    write_request.addresses[1] = base_address.destination + sc_uint<14>(operands) - sc_uint<14>(4); ////check
                    write_request.addresses[0] = base_address.destination + sc_uint<14>(operands) - sc_uint<14>(4)  + 1;
                    write_request.idle  = false;
                    write_request.read  = false;
                    write_request.write = true;
                    write_request_port->set(write_request);
                    read_data_port->get(read_data);
                    write_data_port->set(decode(read_data));
                }

                read_data_port->get(read_data);

                read_request.addresses[1] = base_address.source + sc_uint<14>(operands);
                read_request.addresses[0] = base_address.source + sc_uint<14>(operands) + sc_uint<14>(1);
                read_request.idle  = false;
                read_request.read  = true;
                read_request.write = false;
                read_request_port->set(read_request);

                operands += sc_uint<9>(2);

                insert_state("EXEC_WRITE");

                write_request.addresses[1] = base_address.destination + sc_uint<14>(444);////447
                write_request.addresses[0] = base_address.destination + sc_uint<14>(445);///448
                write_request.idle  = false;
                write_request.read  = false;
                write_request.write = true;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(decode(read_data));

                read_request.addresses[1] = sc_uint<14>(0);
                read_request.addresses[0] = sc_uint<14>(0);
                read_request.idle  = true;
                read_request.read  = false;
                read_request.write = false;
                read_request_port->set(read_request);

                operands = sc_uint<9>(0);

                insert_state("WRITE");

                write_request.addresses[1] = base_address.destination + sc_uint<14>(446);
                write_request.addresses[0] = base_address.destination + sc_uint<14>(447);
                write_request.idle  = false;
                write_request.read  = false;
                write_request.write = true;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(decode(read_data));

                read_request.addresses[1] = sc_uint<14>(0);
                read_request.addresses[0] = sc_uint<14>(0);
                read_request.idle  = true;
                read_request.read  = false;
                read_request.write = false;
                read_request_port->set(read_request);

                insert_state("DONE");

                write_request.addresses[1] = sc_uint<14>(0);
                write_request.addresses[0] = sc_uint<14>(0);
                write_request.idle  = true;
                write_request.read  = false;
                write_request.write = false;
                write_request_port->set(write_request);
                read_data_port->get(read_data);
                write_data_port->set(decode(read_data));

                done_port->set(true);
            }
        }
};

#endif
