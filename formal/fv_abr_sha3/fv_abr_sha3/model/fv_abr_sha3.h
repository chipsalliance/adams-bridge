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

#ifndef abr_sha3_H_
#define abr_sha3_H_

#include <systemc.h>
#include <Interfaces.h>

enum state {IDLE_ST, ABSORB_ST, SQUEEZE_ST, RUN_ST, FLUSH_ST};

SC_MODULE(fv_abr_sha3)
{   
    public:
        shared_in<bool> fv_start_i; 
        blocking_in<bool> fv_keccak_complete_i; 
        shared_in<bool> fv_run_i; 
        //shared_in<bool> fv_done_i; 
        shared_in<bool> fv_state_valid_hold_i;
        shared_in<bool> fv_absorbed_i;
        shared_out<bool> fv_squeezing_o;
        shared_out<bool> fv_absorbed_o;
        shared_out<state> fv_sha3_fsm_o;
        shared_out<bool> fv_state_valid_o;
        SC_CTOR(fv_abr_sha3){
            SC_THREAD(process);
        }

    private:
        bool fv_start;
        bool fv_absorbed;
        bool fv_run;
        //bool fv_done;
        bool fv_keccak_complete;
        bool fv_state_valid_hold;
        void process() {
            while(true) {
                fv_sha3_fsm_o->set(IDLE_ST);

                while(true){
                    insert_state("IDLE");
                    fv_start_i->get(fv_start);
                    fv_state_valid_hold_i->get(fv_state_valid_hold);
                    if(!fv_state_valid_hold){
                        fv_state_valid_o->set(false);
                    }
                    if(fv_start){
                        break;
                    }
                }

                while(true) {
                    fv_sha3_fsm_o->set(ABSORB_ST);
                    insert_state("ABSORB");
                    fv_absorbed_i->get(fv_absorbed);
                    if(fv_absorbed) {
                        fv_absorbed_o->set(true);
                        fv_state_valid_o->set(true);
                        break;
                    } else {
                        fv_state_valid_hold_i->get(fv_state_valid_hold);
                        if(!fv_state_valid_hold){
                            fv_state_valid_o->set(false);
                        }
                    }
                }
                
                while(true){
                    fv_squeezing_o->set(true);
                    fv_sha3_fsm_o->set(SQUEEZE_ST);
                    insert_state("SQUEEZE");

                    fv_state_valid_hold_i->get(fv_state_valid_hold);
                    if(!fv_state_valid_hold){
                        fv_state_valid_o->set(false);
                    }

                    fv_run_i->get(fv_run);
                    //fv_done_i->get(fv_done);
                    fv_absorbed_o->set(false);
                    if(fv_run){
                        fv_squeezing_o->set(true);
                        fv_sha3_fsm_o->set(RUN_ST);
                        fv_keccak_complete_i->read(fv_keccak_complete, "RUN");
                        fv_state_valid_o->set(true);
                    } //else if(fv_done) {
                    //    fv_squeezing_o->set(false);
                    //    fv_sha3_fsm_o->set(FLUSH_ST);
                    //    insert_state("FLUSH");
                    //    fv_state_valid_hold_i->get(fv_state_valid_hold);
                    //    if(!fv_state_valid_hold){
                    //        fv_state_valid_o->set(false);
                    //    }
                    //    break;
                    //}
                }
            }
        }
};

#endif