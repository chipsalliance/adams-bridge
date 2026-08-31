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

#ifndef _MLDSASAMPLERTOP_H_
#define _MLDSASAMPLERTOP_H_

#include "systemc.h"
#include "Interfaces.h"

#define MuBi4Width 4
#define StateWidthLogic 3


// Define the enum for mubi4_t states
enum mubi4_enum : unsigned int {
    MuBi4True  = 0x6,
    MuBi4False = 0x9
};

// Define the enum for SHA-3 states
enum sha3_st_e : unsigned int {
    StIdle = 0x0,
    StAbsorb = 0x1,
    StSqueeze = 0x2,
    StManualRun = 0x3,
    StFlush = 0x4,
    StError = 0x5
};


SC_MODULE(mldsa_sampler_top){

    public:
        SC_CTOR(mldsa_sampler_top){
            SC_THREAD(run);
        }

        enum states : unsigned int {
            MLDSA_SAMPLER_IDLE = 0x0, 
            MLDSA_SAMPLER_PROC = 0x1, 
            MLDSA_SAMPLER_WAIT = 0x2, 
            MLDSA_SAMPLER_RUN = 0x3, 
            MLDSA_SAMPLER_DONE = 0x4
        };

        sc_uint<3> cur_st, nxt_st;
        
        //outputs
        master_out<sc_uint<MuBi4Width>>  sha3_done;
        sc_uint<MuBi4Width>              sha3_done_temp;
        master_out<bool>  sha3_process, sha3_run;
        bool              sha3_process_temp, sha3_run_temp;

        //inputs
        master_in<bool>   sampler_start_i;
        bool              sampler_start_i_temp;
        // master_in<sc_uint<StateWidthLogic>> sha3_fsm;
        sc_uint<StateWidthLogic>            sha3_fsm_temp;
        master_in<bool>   sampler_done;
        bool              sampler_done_temp;
        master_in<bool>   sha3_state_dv;
        bool              sha3_state_dv_temp;
        master_in<bool>   sha3_state_hold;
        bool              sha3_state_hold_temp;
        master_in<bool>   sha3_squeezing;
        bool              sha3_squeezing_temp;
        
        void run() {

            while (true) {

                cur_st = nxt_st;
                
                if(cur_st == 0x0){
                    sampler_start_i     ->master_read(sampler_start_i_temp);

                    sha3_process_temp   = false;
                    sha3_run_temp       = false;
                    sha3_done_temp      = 0x9;

                    sha3_process        ->master_write(sha3_process_temp);
                    sha3_run            ->master_write(sha3_run_temp);
                    sha3_done           ->master_write(sha3_done_temp);

                    insert_state("IDLE");

                    if(sampler_start_i_temp){
                        nxt_st = 0x1;
                    } else {
                        nxt_st = 0x0; 
                    }
                }

                if(cur_st == 0x1){
                    sha3_process_temp   = true;
                    sha3_run_temp       = false;
                    sha3_done_temp      = 0x9;

                    sha3_process        ->master_write(sha3_process_temp);
                    sha3_run            ->master_write(sha3_run_temp);
                    sha3_done           ->master_write(sha3_done_temp);

                    insert_state("PROC");

                    nxt_st = 0x2; 
                }

                if(cur_st == 0x2){
                    sampler_done        ->master_read(sampler_done_temp);
                    sha3_state_dv       ->master_read(sha3_state_dv_temp);
                    sha3_state_hold     ->master_read(sha3_state_hold_temp);

                    sha3_process_temp   = false;
                    sha3_run_temp       = false;
                    sha3_done_temp      = 0x9;

                    sha3_process        ->master_write(sha3_process_temp);
                    sha3_run            ->master_write(sha3_run_temp);
                    sha3_done           ->master_write(sha3_done_temp);

                    insert_state("WAIT");

                    if(sampler_done_temp){
                        nxt_st = 0x4;
                    } else if(sha3_state_dv_temp && !sha3_state_hold_temp) {
                        nxt_st = 0x3; 
                    } else {
                        nxt_st = 0x2;
                    }
                }

                if(cur_st == 0x3){
                    sampler_done        ->master_read(sampler_done_temp);

                    sha3_process_temp   = false;
                    sha3_run_temp       = (!sampler_done_temp ? true : false);
                    sha3_done_temp      = 0x9;

                    sha3_process        ->master_write(sha3_process_temp);
                    sha3_run            ->master_write(sha3_run_temp);
                    sha3_done           ->master_write(sha3_done_temp);

                    insert_state("RUN");

                    if(sampler_done_temp){
                        nxt_st = 0x4;
                    } else {
                        nxt_st = 0x2;
                    }
                }

                 if(cur_st == 0x4){
                    //sha3_fsm             ->master_read(sha3_fsm_temp);
                    sha3_squeezing       ->master_read(sha3_squeezing_temp);

                    sha3_process_temp   = false;
                    sha3_run_temp       = false;
                    sha3_done_temp      = ((sha3_fsm_temp == 0x2) ? sc_uint<4>(6) : sc_uint<4>(9));

                    sha3_process        ->master_write(sha3_process_temp);
                    sha3_run            ->master_write(sha3_run_temp);
                    sha3_done           ->master_write(sha3_done_temp);

                    insert_state("DONE");

                    if(sha3_squeezing_temp){
                        nxt_st = 0x4;
                    } else {
                        nxt_st = 0x0;
                    }
                }
            } 
        }
};

#endif