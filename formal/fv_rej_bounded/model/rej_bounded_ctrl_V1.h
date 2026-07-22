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

#ifndef _REJBOUNDEDCTRL_H_
#define _REJBOUNDEDCTRL_H_

#include "systemc.h"
#include "Interfaces.h"

#define MLDSA_Q                 8380417
#define MLDSA_Q_1               8380416
#define MLDSA_Q_2               8380415

SC_MODULE(rej_bounded_ctrl){

    public:
        SC_CTOR(rej_bounded_ctrl){
            SC_THREAD(run);
        }

        //Interface
        //1 bit signals
        master_in<bool>         data_valid_i;
        master_out<bool>        data_hold_o;
        master_out<bool>        data_valid_o;
        bool                    valid_i, hold_o, valid_o;

        // PI/PO data input and output
        master_in <std::array<sc_uint<4>, 8>>   data_i;
        shared_out<std::array<sc_uint<24>, 4>>  data_o;

        // temp variable for PI data input
        std::array<sc_uint<4>, 8>   data_i_temp;

        // i/o data from/to fifo
        shared_out<std::array<sc_uint<3>, 8>>   fifo_data_i;
        shared_in <std::array<sc_uint<3>, 4>>   fifo_data_o;
        shared_out<sc_uint<8>>                  fifo_valid_i;

        // temp variable for fifo output, serving as an input in model
        std::array<sc_uint<3>, 4>  fifo_data_o_temp;

        //temporary variables
        shared_in<bool> buffer_status;
        bool buffer_full;

        shared_in<sc_uint<4>> sample_status;
        sc_uint<4> valid_samples;

        std::array<sc_uint<3>, 8>   valid_fifo_samples;
        sc_uint<8>                  valid_fifo_signal;

            //function, that rejects value 15 from the PI and serves as input for the FIFO, updates the data to fifo
            std::array<sc_uint<3>, 8> rejBoundedData(std::array<sc_uint<4>, 8> data_in_pi) const {
                std::array<sc_uint<3>, 8>   valid_samples;

                for(int i = 0; i < 8; ++i){
                    if(data_in_pi[i] == sc_uint<4>(15)){
                        valid_samples[i] = sc_uint<3>(0);
                    }else{
                        valid_samples[i] = sc_uint<3>(data_in_pi[i] % sc_uint<4>(5));
                    }
                }
                return valid_samples;
            }

            //function, that rejects value 15 from the PI and serves as input for the FIFO, updates the valid signal
            sc_uint<8> rejBoundedValid(std::array<sc_uint<4>, 8> data_in_pi, bool valid_input) const {
                sc_uint<8>                  valid_data = 0;

                for(int i = 0; i < 8; ++i){
                    if(data_in_pi[i] == sc_uint<4>(15) || !valid_input){
                        valid_data[i] = 0;
                    }else{
                        valid_data[i] = 1;
                    }
                }
                return valid_data;
            }


            //function, that mux'es the FIFO output data before PO to hold values in the range of [eta-2 ; 2]
            std::array<sc_uint<24>, 4> modMux(std::array<sc_uint<3>, 4> fifo_output_data) const {
                std::array<sc_uint<24>, 4> muxed_data;

                for(int i = 0; i < 4; ++i){
                    muxed_data[i] = ((sc_uint<24>(2) + MLDSA_Q - sc_uint<24>(fifo_output_data[i])) % MLDSA_Q);
                }
                return muxed_data;
            }

        
        // as no iterations are given, nor any states are given and
        // the design is completely combinatorial, the idea is to let
        // it run in the while loop, and only distinguish based 
        // on the fifo buffer state, as it dictates the I/O behaviour.

        // the model considers to parts, read data and write data
        // read data: checks if the computation before the fifo is done correctly
        // write data: checks if the computation after the fifo is done correctly
        // hence, read data checks for the PI and write data checks for the PO

        void run() {
            
            // read data
            data_i          -> master_read(data_i_temp);
            fifo_data_i     -> set(rejBoundedData(data_i_temp));
            data_valid_i    -> master_read(valid_i);
            fifo_valid_i    -> set(rejBoundedValid(data_i_temp, valid_i)); 
            
            // write data
            fifo_data_o     -> get(fifo_data_o_temp);
            data_o          -> set(modMux(fifo_data_o_temp));

            while (true) {
                
                insert_state("rej_bounded_loop");

                // read data
                data_i          -> master_read(data_i_temp);
                fifo_data_i     -> set(rejBoundedData(data_i_temp));
                data_valid_i    -> master_read(valid_i);
                fifo_valid_i    -> set(rejBoundedValid(data_i_temp, valid_i)); 

                // write data
                fifo_data_o     -> get(fifo_data_o_temp);
                data_o          -> set(modMux(fifo_data_o_temp));

                buffer_status   ->get(buffer_full);
                sample_status   ->get(valid_samples);

                if (buffer_full){ //no read, but write

                    //stops PISO
                    hold_o          = true;
                    data_hold_o     ->master_write(hold_o);
                    //enables multiplier
                    valid_o         = true;
                    data_valid_o    ->master_write(valid_o);

                } else if(valid_samples < 4){ //no write, but read

                    //enables PISO
                    hold_o          = false;
                    data_hold_o     ->master_write(hold_o);
                    //stops multiplier
                    valid_o         = false;
                    data_valid_o    ->master_write(valid_o);

                } else {

                    //enables PISO
                    hold_o          = false;
                    data_hold_o     ->master_write(hold_o);
                    //enables multiplier
                    valid_o         = true;
                    data_valid_o    ->master_write(valid_o);

                }
            }
        }
};

#endif