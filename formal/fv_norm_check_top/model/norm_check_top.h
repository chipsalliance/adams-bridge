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

#ifndef _norm_check_top_
#define _norm_check_top_

#include "systemc.h"
#include "Interfaces.h"

// Declare data types here
#define  MLDSA_N               256
#define  MLDSA_L               7
#define  MLDSA_Q               8380417
#define  BETA                  120
#define  REG_SIZE              24
#define  MLDSA_MEM_ADDR_WIDTH  14
#define  GAMMA1                static_cast<unsigned>(2) << static_cast<unsigned>(19)
#define  MLDSA_GAMMA2          (MLDSA_Q - 1) / 32
#define  GAMMA2_MINUS_BETA     MLDSA_GAMMA2 - BETA
#define  GAMMA1_MINUS_BETA     GAMMA1 - BETA

SC_MODULE(norm_check_top) {
public:
    SC_CTOR(norm_check_top) {
        SC_THREAD(run);
    }

    // Input ports declaration
    blocking_in<sc_uint<MLDSA_MEM_ADDR_WIDTH>> mem_base_addr_port;
    sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_base_addr;

    shared_in<sc_uint<2>> norm_check_mode_port;
    sc_uint<2> norm_check_mode;

    shared_in<bool> shuffling_enable_port;
    bool shuffling_enable;

    shared_in<sc_uint<5>> randomness_port;
    sc_uint<5> randomness;

    shared_in<sc_uint<1>> randomness_lsb_port;
    shared_in<sc_uint<1>> controller_randomness_lsb_port;
    sc_uint<1> randomness_lsb;
    sc_uint<1> controller_randomness_lsb;


    shared_in<std::array<sc_uint<REG_SIZE>, 4>> mem_rd_data_port;
    std::array<sc_uint<REG_SIZE>, 4> mem_rd_data;
    std::array<sc_uint<22>, 4> mem_rd_data_casted;

    // Output ports declaration
    shared_out<bool> norm_check_done_port;
    bool norm_check_done;

    shared_out<bool> invalid_port;
    bool invalid;

    struct mem_if_it {
        sc_uint<MLDSA_MEM_ADDR_WIDTH> address;
        sc_uint<2> rd_wr_en;
    };

    shared_out<mem_if_it> mem_rd_req_port;
    mem_if_it mem_rd_req;

    // Local variables
    bool invalid_0, invalid_1, invalid_2, invalid_3;
    bool incr_rd_addr;
    sc_uint<7> neutral_cnt;
    sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr, mem_rd_addr_out, randomness_var;
    sc_uint<5> incr_addr;  // Added missing variable

    // Function for returning invalid
     bool return_invalid(sc_uint<2> mode, sc_uint<22> operand) const {
        sc_uint<22> bound;
        sc_uint<22> q_minus_bound;
        bool invalid;
        
        // Set bound based on mode
        switch (mode) {
            case 0:  bound =  static_cast< sc_uint<22>>(GAMMA1_MINUS_BETA); break;
            case 1:  bound =  static_cast< sc_uint<22>>(GAMMA2_MINUS_BETA); break;
            case 2:  bound =  static_cast< sc_uint<22>>(MLDSA_GAMMA2); break;
            default: bound =  static_cast< sc_uint<22>>(0); break;
        }
    
        // Ensure no underflow in q_minus_bound calculation
        if (static_cast< sc_uint<22>>(MLDSA_Q) >= bound) {
            q_minus_bound = static_cast< sc_uint<22>>(static_cast<sc_uint<22>>(MLDSA_Q) - bound);
        } else {
            q_minus_bound = static_cast< sc_uint<22>>(0);  // Handle potential underflow case
        }
    
        // Mark as invalid if operand is outside valid range
        invalid = (operand <= bound || operand >= q_minus_bound);
    
        return invalid;
    }


    sc_uint<MLDSA_MEM_ADDR_WIDTH> return_idle_mem_rd_req (sc_uint<5> randomness, sc_uint<1> randomness_lsb) const{
            sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr;

                mem_rd_addr.range(MLDSA_MEM_ADDR_WIDTH,6) = sc_uint<8>(0);
                mem_rd_addr.range(5,1) = randomness;
                mem_rd_addr.range(0,0) = randomness_lsb;

        return mem_rd_addr;
    }

    sc_uint<MLDSA_MEM_ADDR_WIDTH> return_read_mem_mem_rd_req (
        sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr_0, 
        sc_uint<1> randomness_lsb) const 
    {
        sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr;

        // Corrected the range indices and shift logic
        mem_rd_addr.range(MLDSA_MEM_ADDR_WIDTH , 1) = mem_rd_addr_0.range(MLDSA_MEM_ADDR_WIDTH,1);
        mem_rd_addr.range(0,0) = ~randomness_lsb;

        return mem_rd_addr;
    }


    sc_uint<MLDSA_MEM_ADDR_WIDTH> return_wait_mem_mem_rd_req (sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr_0, sc_uint<5> incr_addr , sc_uint<1> randomness_lsb) const{
            sc_uint<MLDSA_MEM_ADDR_WIDTH> mem_rd_addr;

                    mem_rd_addr.range(MLDSA_MEM_ADDR_WIDTH,6)  = (mem_rd_addr_0.range(MLDSA_MEM_ADDR_WIDTH,6) );
                    mem_rd_addr.range(5,1)                     = ( incr_addr      );
                    mem_rd_addr.range(0,0)                     = ( randomness_lsb     );

        return mem_rd_addr;
    }

    void run() {
        //TODO: SHOULD IT BE EQUAL ZERO IN THE BEGINNING?
        mem_rd_data[0]         = static_cast<sc_uint<REG_SIZE>>(0);
        mem_rd_data[1]         = static_cast<sc_uint<REG_SIZE>>(0);
        mem_rd_data[2]         = static_cast<sc_uint<REG_SIZE>>(0);
        mem_rd_data[3]         = static_cast<sc_uint<REG_SIZE>>(0);

        mem_rd_data_casted[0]  = static_cast<sc_uint<22>>(0);
        mem_rd_data_casted[1]  = static_cast<sc_uint<22>>(0);
        mem_rd_data_casted[2]  = static_cast<sc_uint<22>>(0);
        mem_rd_data_casted[3]  = static_cast<sc_uint<22>>(0);

        mem_rd_req.rd_wr_en    = static_cast<sc_uint<2>>(0);
        mem_rd_req.address     = static_cast<sc_uint<MLDSA_MEM_ADDR_WIDTH>>(0);
        mem_rd_addr            = static_cast<sc_uint<MLDSA_MEM_ADDR_WIDTH>>(0);
        incr_rd_addr           = false;
        neutral_cnt            = 0;
        norm_check_done_port  -> set(false);
        invalid_port          -> set(false);
        mem_rd_req_port       -> set(mem_rd_req);

        while (true) {
            ////////////////////
            // Initial values //
            ////////////////////
            invalid_0 = false;
            invalid_1 = false;
            invalid_2 = false;
            invalid_3 = false;
            invalid   = false;
            // Go to state idle
            mem_base_addr_port->read(mem_base_addr, "IDLE");
            // if it's in iddle, should the address increment?
            /// Read values from input ports   
            norm_check_mode_port  -> get(norm_check_mode);
            shuffling_enable_port -> get(shuffling_enable);
            if (shuffling_enable ) {
                randomness_port       -> get(randomness);
                randomness_lsb_port   -> get(randomness_lsb);
            }
            else {
                randomness = 0;
                randomness_lsb = 0;
            }
            mem_rd_data_port      -> get(mem_rd_data);

            // Set invalid to the comparison.
            mem_rd_data_casted[0] = static_cast<sc_uint<22>>(mem_rd_data[0]);
            mem_rd_data_casted[1] = static_cast<sc_uint<22>>(mem_rd_data[1]);
            mem_rd_data_casted[2] = static_cast<sc_uint<22>>(mem_rd_data[2]);
            mem_rd_data_casted[3] = static_cast<sc_uint<22>>(mem_rd_data[3]);
            invalid_0             = return_invalid(norm_check_mode, mem_rd_data_casted[0]);
            invalid_1             = return_invalid(norm_check_mode, mem_rd_data_casted[1]);
            invalid_2             = return_invalid(norm_check_mode, mem_rd_data_casted[2]);
            invalid_3             = return_invalid(norm_check_mode, mem_rd_data_casted[3]);
            invalid               = invalid || invalid_0 || invalid_1 || invalid_2 || invalid_3;
            invalid_port         -> set(invalid);

            incr_addr             = randomness;
            mem_rd_addr           = return_idle_mem_rd_req(randomness, randomness_lsb);
            mem_rd_addr_out       = mem_rd_addr + mem_base_addr;
            mem_rd_req.address    = mem_rd_addr_out;
            mem_rd_req.rd_wr_en   = static_cast<sc_uint<2>>(0); 
            mem_rd_req_port       -> set(mem_rd_req);
            norm_check_done_port  -> set(false);
            incr_rd_addr          = false;

            do {
                controller_randomness_lsb_port   -> get(controller_randomness_lsb);
                if (!incr_rd_addr) {                  
                    insert_state("READ_MEM");

                    incr_rd_addr              = true;
                    mem_rd_addr               = return_read_mem_mem_rd_req(mem_rd_addr, controller_randomness_lsb);
                    incr_addr                += static_cast< sc_uint<5>>(1);

                } else {

                    insert_state("WAIT");
                
                    
                    mem_rd_addr               = return_wait_mem_mem_rd_req(mem_rd_addr, incr_addr, controller_randomness_lsb);
                    incr_rd_addr              = false;
                }
                mem_rd_req.rd_wr_en   = static_cast< sc_uint<2>>(1);  // Read state
                mem_rd_addr_out       = mem_rd_addr + mem_base_addr;
                mem_rd_req.address    = mem_rd_addr_out;
                mem_rd_req_port      -> set(mem_rd_req);                     
                mem_rd_data_casted[0] = static_cast<sc_uint<22>>(mem_rd_data[0]);
                mem_rd_data_casted[1] = static_cast<sc_uint<22>>(mem_rd_data[1]);
                mem_rd_data_casted[2] = static_cast<sc_uint<22>>(mem_rd_data[2]);
                mem_rd_data_casted[3] = static_cast<sc_uint<22>>(mem_rd_data[3]);
                invalid_0             = return_invalid(norm_check_mode, mem_rd_data_casted[0]);
                invalid_1             = return_invalid(norm_check_mode, mem_rd_data_casted[1]);
                invalid_2             = return_invalid(norm_check_mode, mem_rd_data_casted[2]);
                invalid_3             = return_invalid(norm_check_mode, mem_rd_data_casted[3]);
                invalid               = invalid || invalid_0 || invalid_1 || invalid_2 || invalid_3;
                invalid_port         -> set(invalid);

                neutral_cnt          += static_cast< sc_uint<7>>(1);
                norm_check_done_port -> set(false);
            } while (neutral_cnt < static_cast< sc_uint<7>>(((MLDSA_N / 4)))) ;

                insert_state("DONE");
   
                invalid_port         -> set(false);

                mem_rd_req.rd_wr_en   = static_cast< sc_uint<2>>(0);  // Read state
                mem_rd_req_port      -> set(mem_rd_req);
                norm_check_done_port -> set(true);
                shuffling_enable     = false;
                
            
        }
    }
};

#endif
