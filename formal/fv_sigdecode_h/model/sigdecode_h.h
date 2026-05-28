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

#ifndef _sigdecode_h_
#define _sigdecode_h_
 
#include "systemc.h"
#include "Interfaces.h"
#include <array>
 
constexpr unsigned MLDSA_K = 8;
constexpr unsigned MLDSA_N = 256;
constexpr unsigned REG_SIZE = 24;
constexpr unsigned MLDSA_OMEGA = 75;
 
enum class ReadStatesType {
    ReadIdle,
    ReadInit,
    ReadHintSum,
    ReadExec
};
enum class WriteStatesType {
    WriteIdle,
    WriteInit,
    WriteMem
};
 
SC_MODULE(sigdecode_h_states) {
    public:
        SC_CTOR(sigdecode_h_states){
            SC_THREAD(read);
            SC_THREAD(write);
        }
 
        shared_in<bool>start_port;
        bool start;
 
        shared_in<bool> start_write_fsm;
 
        shared_in<sc_uint<14>> dest_address_port;
        sc_uint<14> dest_address;
 
        shared_in<std::array<sc_uint<8>, 83>> read_data_port;
        std::array<sc_uint<8>, 83> read_data;
 
        struct Request {
            sc_uint<14> address;
            bool idle;
            bool read;
            bool write;
        };
        shared_out<Request> write_request_port;
        Request write_request;
        shared_out<sc_biguint<96>> write_data_port;
        sc_biguint<96> write_data;
 
        shared_out<bool> done_port;
        shared_out<bool> error_port;
 
        sc_uint<8> hintsum, hintsum_prev_poly, hintsum_curr_poly, rem_hintsum, bitmap_ptr, prev_hint;
        sc_uint<4> poly_count, curr_poly_map;
        sc_uint<14> mem_wr_addr;
        sc_biguint<256> bitmap;
        bool error, hint_rd_en_f, OR_remaining_encoded_h_i, hint_ok, first_hint, hintsum_max_error_i;
        sc_uint<7> rd_ptr;
        std::array<sc_uint<8>, 4> hint;
 
        sc_uint<8> upd_rem_hintsum(sc_uint<8> prev_val) const {
            sc_uint<8> result = 0;
            if(prev_val >= sc_uint<8>(4)) {
                result = sc_uint<8>(prev_val - sc_uint<8>(4));
            }
            return result;
        }

        sc_biguint<256> upd_bitmap(sc_uint<4> curr_poly_map_val, std::array<sc_uint<8>, 4> hint_val, sc_biguint<256> bitmap_val) const {
            sc_biguint<256> result;
            result = bitmap_val;
            if(curr_poly_map_val == sc_uint<4>(15)) {
                result[sc_uint<8>(hint_val[0])] = 1;
                result[sc_uint<8>(hint_val[1])] = 1;
                result[sc_uint<8>(hint_val[2])] = 1;
                result[sc_uint<8>(hint_val[3])] = 1;
            } else if (curr_poly_map_val == sc_uint<4>(1)) {
                result[hint_val[0]] = 1;
            } else if (curr_poly_map_val == sc_uint<4>(3)) {
                result[hint_val[0]] = 1;
                result[hint_val[1]] = 1;
            } else if (curr_poly_map_val == sc_uint<4>(7)) {
                result[hint_val[0]] = 1;
                result[hint_val[1]] = 1;
                result[hint_val[2]] = 1;
            }
            return result;
        }

        sc_biguint<96> upd_write_data(sc_biguint<256> bitmap_val, sc_uint<8> bitmap_ptr_val) const {
            sc_biguint<96> result;
            std::array<sc_biguint<96>, 4> temp;
            temp[0] = sc_uint<24>(bitmap_val[sc_uint<8>(bitmap_ptr_val + sc_uint<8>(3))]) << 72;
            temp[1] = sc_uint<24>(bitmap_val[sc_uint<8>(bitmap_ptr_val + sc_uint<8>(2))]) << 48;
            temp[2] = sc_uint<24>(bitmap_val[sc_uint<8>(bitmap_ptr_val + sc_uint<8>(1))]) << 24;
            temp[3] = sc_uint<24>(bitmap_val[sc_uint<8>(bitmap_ptr_val + sc_uint<8>(0))]);
            result = temp[0] | temp[1] | temp[2] | temp[3];
            return result;
        }

        bool upd_remaining_encoded_h_i(std::array<sc_uint<8>, 83> read_data_val) const {
            bool result = 0;
            for(int i = 0; i < 75; i = i + 1){
                if (i >= read_data_val[82]) {
                    bool ored_val = 0;
                    for(int j = 0; j < 8; j = j + 1) {
                        ored_val = ored_val | read_data_val[i][j];
                    }
                    result = result | ored_val;
                } else {
                    result=0;
                }
            }
            return result;
        }
        
        bool upd_hintsum_max_error_i(std::array<sc_uint<8>, 83> read_data_val) const {
            bool result = 0;
            for(int i = 0; i < 8; i = i + 1) {
                if (read_data_val[75+i] > 75) {
                    result = true;
                }
            }
            return result;
        }
        
        bool upd_hint_ok(sc_uint<4> curr_poly_map_val, std::array<sc_uint<8>, 4> hint_val, sc_uint<8> prev_hint_val, bool first_hint_val) const {
            bool result = 0;
            result =    ( curr_poly_map_val[0] ? (first_hint_val ? (prev_hint_val <= hint_val[0]) : (prev_hint_val < hint_val[0])) : true) &&
                        ((curr_poly_map_val[0] & curr_poly_map_val[1]) ? (hint_val[0] < hint_val[1]) : true) && 
                        ((curr_poly_map_val[1] & curr_poly_map_val[2]) ? (hint_val[1] < hint_val[2]) : true) &&
                        ((curr_poly_map_val[2] & curr_poly_map_val[3]) ? (hint_val[2] < hint_val[3]) : true);

            return result;
        }
 
        ReadStatesType read_state;
        WriteStatesType write_state;
 
        void read() {
            read_state = ReadStatesType::ReadIdle;
            prev_hint = 0;
            hint_ok = true;
            while (true) {
                if(read_state == ReadStatesType::ReadIdle) {
                    insert_state("rIDLE");
                    start_port -> get(start);
                    prev_hint = 0;
                    hint_ok = true;

                    if(start) {
                        read_state = ReadStatesType::ReadInit;
                        read_data_port->get(read_data);
                        hintsum = sc_uint<8>(0);
                    } else {
                        read_state = ReadStatesType::ReadIdle;
                        bitmap = (write_state == WriteStatesType::WriteMem && (error || mem_wr_addr.range(5, 0) == sc_uint<6>(63))) ? sc_biguint<256>(0) : bitmap;
                        hintsum_prev_poly = hintsum;
                        hintsum = poly_count == sc_uint<4>(8) || write_state == WriteStatesType::WriteIdle ? sc_uint<8>(0) : read_data[sc_uint<7>(75) + sc_uint<7>(poly_count)];
                        hintsum_curr_poly = hintsum - hintsum_prev_poly;
                    }
                } else if(read_state == ReadStatesType::ReadInit) {
                    insert_state("rINIT");
                    prev_hint = 0;
                        
                    if(error) {
                        read_state = ReadStatesType::ReadIdle;
                        bitmap = (write_state == WriteStatesType::WriteMem && (error || mem_wr_addr.range(5, 0) == sc_uint<6>(63))) ? sc_biguint<256>(0) : bitmap;
                        hint_ok = true;
                    } else if(write_state != WriteStatesType::WriteInit) {
                        read_state = ReadStatesType::ReadInit;
                        bitmap = (write_state == WriteStatesType::WriteMem && (error || mem_wr_addr.range(5, 0) == sc_uint<6>(63))) ? sc_biguint<256>(0) : bitmap;
                        hint_ok = upd_hint_ok(curr_poly_map, hint, prev_hint, first_hint);
                    } else {
                        read_state = ReadStatesType::ReadHintSum;
                        hint_ok = true;
                        hintsum_prev_poly = hintsum;
                        hintsum = poly_count == sc_uint<4>(8) ? sc_uint<8>(0) : read_data[sc_uint<7>(75) + sc_uint<7>(poly_count)];
                        hintsum_curr_poly = hintsum - hintsum_prev_poly;
                    }
                } else if(read_state == ReadStatesType::ReadHintSum) {
                    insert_state("rHINTSUM");
                    rem_hintsum = hintsum_curr_poly;
                    hintsum_prev_poly = hintsum;
                    hintsum = poly_count == sc_uint<4>(8) ? sc_uint<8>(0) : read_data[sc_uint<7>(75) + sc_uint<7>(poly_count)];
                    hintsum_curr_poly = hintsum - hintsum_prev_poly;
                    curr_poly_map = sc_uint<4>(0);
                    read_state = ReadStatesType::ReadExec;
                } else {
                    insert_state("rEXEC");
                    bitmap = upd_bitmap(curr_poly_map, hint, bitmap);
                    hint_ok = upd_hint_ok(curr_poly_map, hint, prev_hint, first_hint);
                    prev_hint = hint[3];
                    curr_poly_map = rem_hintsum >= sc_uint<8>(4) ? sc_uint<4>(15) : (rem_hintsum == sc_uint<8>(3) ? sc_uint<4>(7) : (rem_hintsum == sc_uint<8>(2) ? sc_uint<4>(3) : sc_uint<4>(rem_hintsum)));
                    first_hint = (!error && rem_hintsum > sc_uint<8>(0)) && !hint_rd_en_f;
                    hint_rd_en_f = !error && rem_hintsum != sc_uint<8>(0);

                    if(error || (rem_hintsum == sc_uint<8>(0) && poly_count == sc_uint<4>(7))) {
                        read_state = ReadStatesType::ReadIdle;
                        bitmap = (write_state == WriteStatesType::WriteMem && (error || mem_wr_addr.range(5, 0) == sc_uint<6>(63))) ? sc_biguint<256>(0) : bitmap;
                        hint = {0,0,0,0};
                        rd_ptr = rem_hintsum >= sc_uint<8>(4) ? sc_uint<7>(rd_ptr + 4) : sc_uint<7>(rd_ptr + rem_hintsum);
                    } else if(rem_hintsum == sc_uint<8>(0) && poly_count != sc_uint<4>(7)) {
                        read_state = ReadStatesType::ReadInit;
                        hint = {0,0,0,0};
                        hintsum_curr_poly = hintsum - hintsum_prev_poly;
                    } else {
                        read_state = ReadStatesType::ReadExec;
                        hint[0] = read_data[sc_uint<7>(rd_ptr+0)];
                        hint[1] = read_data[sc_uint<7>(rd_ptr+1)];
                        hint[2] = read_data[sc_uint<7>(rd_ptr+2)];
                        hint[3] = read_data[sc_uint<7>(rd_ptr+3)];
                        rd_ptr = rem_hintsum >= sc_uint<8>(4) ? sc_uint<7>(rd_ptr + 4) : sc_uint<7>(rd_ptr + rem_hintsum);
                        hintsum_prev_poly = hintsum;
                        hintsum = poly_count == sc_uint<4>(8) ? sc_uint<8>(0) : read_data[sc_uint<7>(75) + sc_uint<7>(poly_count)];
                        hintsum_curr_poly = hintsum - hintsum_prev_poly;
                    }
                    rem_hintsum = upd_rem_hintsum(rem_hintsum);
                }
            }
        }
 
        void write() {
            write_request.address = sc_uint<14>(0);
            write_request.idle  = true;
            write_request.read  = false;
            write_request.write = false;
            write_request_port->set(write_request);
            write_data_port->set(0);
            bool write_en = false;
            done_port->set(true);
            error_port->set(false);
            mem_wr_addr = sc_uint<14>(0);
            bitmap_ptr = sc_uint<8>(0);
            read_data_port->get(read_data);
            OR_remaining_encoded_h_i = upd_remaining_encoded_h_i(read_data);
            hintsum_max_error_i = upd_hintsum_max_error_i(read_data);
            write_state = WriteStatesType::WriteIdle;

            while (true) {
                if(write_state == WriteStatesType::WriteIdle) {
                    done_port->set(read_state == ReadStatesType::ReadIdle);
                    insert_state("wIDLE");
                    start_write_fsm->get(write_en);
                    read_data_port->get(read_data);
                    OR_remaining_encoded_h_i = upd_remaining_encoded_h_i(read_data);
                    hintsum_max_error_i = upd_hintsum_max_error_i(read_data);
                    write_request.address = mem_wr_addr;
                    write_request.idle  = true;
                    write_request.read  = false;
                    write_request.write = false;
                    write_request_port->set(write_request);
                    write_data = upd_write_data(bitmap, bitmap_ptr);
                    write_data_port->set(write_data);
                    dest_address_port->get(dest_address);
                    mem_wr_addr = dest_address;

                    if(write_en) {
                        write_state = WriteStatesType::WriteInit;
                        error_port->set(false);
                        done_port->set(false);
                    } else {
                        write_state = WriteStatesType::WriteIdle;
                    }
                } else if(write_state == WriteStatesType::WriteInit ) {
                    insert_state("wINIT");
                    write_request.address = mem_wr_addr;
                    write_request.idle  = true;
                    write_request.read  = false;
                    write_request.write = false;
                    write_request_port->set(write_request);
                    write_data = upd_write_data(bitmap, bitmap_ptr);
                    write_data_port->set(write_data);

                    if(error) {
                        write_state = WriteStatesType::WriteIdle;
                        read_data_port->get(read_data);
                        OR_remaining_encoded_h_i = upd_remaining_encoded_h_i(read_data);
                        hintsum_max_error_i = upd_hintsum_max_error_i(read_data);
                    } else if(hint_rd_en_f || (rem_hintsum == sc_uint<8>(0) && (read_state == ReadStatesType::ReadExec))) {
                        write_state = WriteStatesType::WriteMem;
                        done_port->set(false);
                    } else {
                        write_state = WriteStatesType::WriteInit;
                        done_port->set(false);
                    }
                    error = (hintsum < hintsum_prev_poly) || OR_remaining_encoded_h_i || !hint_ok || hintsum_max_error_i;
                    error_port->set(error);
                } else if(write_state == WriteStatesType::WriteMem) {
                    insert_state("wMEM");
                    write_request.address = mem_wr_addr;
                    write_request.idle  = false;
                    write_request.read  = false;
                    write_request.write = true;
                    write_request_port->set(write_request);
                    write_data = upd_write_data(bitmap, bitmap_ptr);
                    write_data_port->set(write_data);

                    if(error || (mem_wr_addr.range(5, 0) == sc_uint<6>(63) && poly_count == sc_uint<4>(7))) {
                        write_state = WriteStatesType::WriteIdle;
                        poly_count = mem_wr_addr.range(5, 0) == sc_uint<6>(63) && poly_count == sc_uint<4>(8) ? sc_uint<4>(0) : (mem_wr_addr.range(5, 0) == sc_uint<6>(63) ? sc_uint<4>(poly_count + sc_uint<4>(1)) : poly_count);
                        read_data_port->get(read_data);
                        OR_remaining_encoded_h_i = upd_remaining_encoded_h_i(read_data);
                        hintsum_max_error_i = upd_hintsum_max_error_i(read_data);
                    } else if(mem_wr_addr.range(5, 0) == sc_uint<6>(63) && poly_count != sc_uint<4>(7)) {
                        write_state = WriteStatesType::WriteInit;
                        poly_count = poly_count == sc_uint<4>(8) ? 0 : poly_count + sc_uint<4>(1);
                        done_port->set(false);
                    } else {
                        write_state = WriteStatesType::WriteMem;
                        done_port->set(false);
                    }
                    bitmap_ptr = mem_wr_addr.range(5, 0) == sc_uint<6>(63) ? 0 : bitmap_ptr + sc_uint<8>(4);
                    mem_wr_addr = mem_wr_addr == dest_address + sc_uint<14>(511) ? 0 : mem_wr_addr + sc_uint<14>(1);
                    error = (hintsum < hintsum_prev_poly) || OR_remaining_encoded_h_i || !hint_ok || hintsum_max_error_i;
                    error_port->set(error);
                }
            }
        }
};
 
#endif
 
// till_done: cover property (disable iff(rst) sigdecode_h.sigdecode_h_enable ##1 sigdecode_h.sigdecode_h_done [->1]);
// eight_polys: cover property (disable iff(rst) sigdecode_h.poly_count == 8);
// error_inMEM: cover property (disable iff(rst) sigdecode_h.sdh_ctrl_inst.write_fsm_state_ps == sigdecode_h_defines_pkg::SDH_WR_MEM && sigdecode_h.sigdecode_h_error);