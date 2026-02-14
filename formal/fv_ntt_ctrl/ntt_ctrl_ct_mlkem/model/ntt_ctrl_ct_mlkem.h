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

#ifndef _ntt_ctrl_1
#define _ntt_ctrl_1

#include "Interfaces.h"

constexpr unsigned NTT_READ_ADDR_STEP = 16;
constexpr unsigned MEM_LAST_ADDR = 63;
constexpr unsigned MEM_ADDR_WIDTH = 15;
constexpr unsigned NTT_WRITE_ADDR_STEP = 1;

enum class CtReadStatesType {
  CtReadIdle,
  CtReadStage,
  CtReadBuf,
  CtReadExec,
  CtReadExecwait
};

enum class CtWriteStatesType {
  CtWriteIdle,
  CtWriteStage,
  CtWriteMem
};

// Starting with ct-mode
SC_MODULE(ntt_ctrl_ct_mlkem) {
public:
  SC_CTOR(ntt_ctrl_ct_mlkem) {
    SC_THREAD(read)
    SC_THREAD(write)
  }
  
  struct Base_Address{
        sc_uint<14> source;
        sc_uint<14> interim;
        sc_uint<14> destination;
       };

  sc_uint<14> base_address_temp; 
  sc_uint<14> base_address_temp_write;
  sc_uint<16> mem_rd_next_addr; 
  sc_uint<16> mem_wr_next_addr;
  bool last_rd_addr;
  bool rd_wrap_around;
  bool wr_wrap_around;

  struct Request_and_Address {
            bool request;
            sc_uint<15> address;
  };
  //Base_Address base_address;
  shared_in<Base_Address> base_address_port; 
   
     
  shared_out<Request_and_Address> mem_read_req_port; // Read address
  Request_and_Address read_req;
  shared_out<Request_and_Address> mem_write_req_port; // write address
  Request_and_Address write_req;

  // function for twiddle_end_addr
  sc_uint<7> twiddle_end_addr(sc_uint<3> count) const {
    sc_uint<7> result;
         switch (count) {
        case 0:
            result = 0;
            break;
        case 1:
            result = 3;
            break;
        case 2:
            result = 15;
            break;
        case 3:
            result = 63;
            break;
        default:
            result = 0;
            break;
                       }
    
   return result;
 }

// function for twiddle_offset
 sc_uint<7> twiddle_offset(sc_uint<3> count) const {
 sc_uint<7> result;
         switch (count) {
        case 0:
            result = 0;
            break;
        case 1:
            result = 1;
            break;
        case 2:
            result = 5;
            break;
        case 3:
            result = 21;
            break;
        default:
            result = 0;
            break;
                       }
    
    return result;
 }
            
//// function for twiddle_rand_offset
sc_uint<7> twiddle_rand_offset(sc_uint<3>count,sc_uint<2>ptr,sc_uint<4> chunk) const {
  sc_uint<7> result;
           switch (count) {
           case 0:
             result = 0;
              break;
            case 1:
              result = ptr;
              break;
            case 2:
              result = ((chunk % 4) * 4 + ptr);
              break;
            case 3:
              result = ((chunk ) * 4 + ptr);
              break;
            default:
              result = 0;
              break;
    }

       return static_cast<sc_uint<7>>(result);
    }
    
    ////Output Signals
    bool bf_enable_reg;  
    sc_uint<3> opcode;
    bool masking_en_ctrl;
    bool buf_wren_ntt_reg;    
    bool buf_rden_ntt_reg; 
    sc_uint<2> buf_wrptr;   
    sc_uint<2> buf_rdptr_f;    
    bool pw_rden;
    bool pw_wren;
    bool ntt_done;
    sc_uint<7> twiddle_addr_reg;

    //i/p signal
    bool ntt_enable;
    bool butterfly_ready;
    bool buf0_valid;
    bool shuffle_en;
    //sc_uint<6> random;

    sc_biguint<7> rd_valid_count;  
    sc_uint<2>    index_rand_offset;
    sc_uint<4>    chunk_count_reg;
    sc_uint<4>    mlkem_chunk_count_reg;
    sc_biguint<2> buf_count ;  
    sc_biguint<7> wr_valid_count;
    //sc_biguint<3> rounds_count;
    //sc_uint<4>    chunk_count;
    //sc_uint<4>    chunk_rand_offset;
    sc_uint<2>    buf_rdptr_reg; /// proved in read fsm as buf_rdptr_reg_1
    sc_uint<2>    mlkem_buf_rdptr_reg;
    sc_uint<44>   chunk_count_reg_1; /////chunk_count_reg_1 for write fsm chunk count reg
    sc_uint<22>   buf_rdptr_reg_1;/// buf_rdptr_reg_1 for write fsm chunk count reg
    bool wr_stage_set;
   

    shared_out<sc_uint<2>> buf_wrptr_out;
    shared_out<sc_uint<2>> buf_rdptr_f_out;
    shared_out<bool> bf_enable_out;
    shared_out<bool> buf_wren_out;   
    shared_out<bool> buf_rden_out; 
    shared_out<bool> pw_rden_out;
    shared_out<bool> pw_wren_out;
    shared_out<sc_biguint<3>> rounds_count_out;
   
    shared_out<bool> ntt_done_out;
    shared_out<sc_uint<3>> opcode_port;   
    shared_out<bool> masking_en_ctrl_out;
    shared_out<sc_uint<7>>twiddle_addr_reg_out;
    shared_out<bool> ntt_passthrough_out; //added ntt_passthrough PO
 

  
    shared_in<bool> shuffle_en_in;
    shared_in<sc_uint<4>> chunk_count_in; // input for read fsm
    shared_in<sc_uint<4>> chunk_rand_offset_in; // input for read fsm
    shared_in<sc_biguint<3>> rounds_count_in; // input for read fsm
    shared_in<bool> buf0_valid_in;
    shared_in<bool> ntt_enable_in;
    shared_in<bool> mlkem_in; //added mlkem PI
    shared_in<sc_uint<6>> random_in;
    shared_in<bool> butterfly_ready_in;
    shared_in<sc_uint<4>> chunk_count_reg_port;
    shared_in<sc_uint<4>> mlkem_chunk_count_reg_port;
    shared_in<sc_uint<2>> buf_rdptr_reg_port;
    shared_in<sc_uint<2>> mlkem_buf_rdptr_reg_port;

    bool latch_index_rand_offset;
    shared_in<bool> latch_index_rand_offset_port;


private:
  [[noreturn]] void read() {

    CtReadStatesType read_state;
    CtReadStatesType next_state = CtReadStatesType::CtReadIdle;
    bool ntt_done  = false;
    sc_biguint<3> rounds_count;
    sc_uint<4>    chunk_count;
    sc_uint<4>    chunk_rand_offset;
    Base_Address base_address;
    sc_uint<6> random;

    while (true) {
      if (read_state == CtReadStatesType::CtReadIdle) {

          insert_state("read_idle");
        
       
          pw_rden                 = false;
          pw_wren                 = false;
          pw_rden_out             -> set(pw_rden);
          pw_wren_out             -> set(pw_wren); //no changes in pw_rden & pw_wren

          buf_wren_ntt_reg        = false;             
          buf_rden_ntt_reg        = false;   
          buf_wren_out            -> set(buf_wren_ntt_reg);   
          buf_rden_out            -> set(buf_rden_ntt_reg); //no changes in buf_wren_ntt_reg & buf_rden_ntt_reg
          bf_enable_reg           = false;            
          bf_enable_out           -> set(bf_enable_reg); // no change in bf_enable_reg

          masking_en_ctrl         = false;
          opcode                  = sc_uint<2>(0);

          masking_en_ctrl_out    -> set(masking_en_ctrl);
          opcode_port            -> set(opcode); //no changes in opcode & masking_en_ctrl

          shuffle_en_in          -> get(shuffle_en);
          buf_rdptr_f             = shuffle_en ? (static_cast<sc_uint<2>>(index_rand_offset.range(1,0) + buf_count)) :  static_cast<sc_uint<2>>(buf_count);
          buf_rdptr_f_out        -> set(buf_rdptr_f); //no change in buf_rdptr_f
          twiddle_addr_reg        = sc_uint<7>(0);
          twiddle_addr_reg_out   -> set(twiddle_addr_reg); //no change in twiddle_addr_reg
          buf_count               = sc_biguint<2>(0);
          
          rounds_count_in         -> get(rounds_count);
          chunk_rand_offset_in    -> get(chunk_rand_offset);
          shuffle_en_in           -> get(shuffle_en);
          base_address_port       -> get(base_address);

          base_address_temp       = (rounds_count == 0)? base_address.source: (rounds_count[0])? base_address.interim:base_address.destination;
          mem_rd_next_addr        = read_req.address;
          read_req.address        = shuffle_en ?static_cast<sc_uint<15>>(base_address_temp + chunk_rand_offset):static_cast<sc_uint<15>>(base_address_temp);
          read_req.request        = false;
          mem_read_req_port       -> set(read_req);
      

          bool ntt_enable = false;
          ntt_enable_in->get(ntt_enable);

        if (ntt_enable) {
          next_state = CtReadStatesType::CtReadStage;
        } else {
          next_state = CtReadStatesType::CtReadIdle;
        }
        } else if (read_state == CtReadStatesType::CtReadStage) {

         insert_state("read_stage");
            
        
            pw_rden                   = false;
            pw_wren                   =  false;
            pw_rden_out               -> set(pw_rden);
            pw_wren_out               -> set(pw_wren);

            buf_wren_ntt_reg          = false;             
            buf_rden_ntt_reg          = false;   
            buf_wren_out               -> set(buf_wren_ntt_reg);   
            buf_rden_out               -> set(buf_rden_ntt_reg); 

            bf_enable_reg             = false;            
            bf_enable_out              -> set(bf_enable_reg);

            masking_en_ctrl           = false;
            opcode                    = sc_uint<2>(0);
            masking_en_ctrl_out      -> set(masking_en_ctrl);
            opcode_port               -> set(opcode);

            shuffle_en_in             -> get(shuffle_en);
            buf_rdptr_f               = shuffle_en ? (static_cast<sc_uint<2>>(index_rand_offset.range(1,0) + buf_count)) :  static_cast<sc_uint<2>>(buf_count);
            buf_rdptr_f_out          -> set(buf_rdptr_f);
       
            butterfly_ready           = false;
            butterfly_ready_in       -> get(butterfly_ready);
            rounds_count_in          -> get(rounds_count);
            chunk_count_in           -> get(chunk_count);
            twiddle_addr_reg         = !butterfly_ready ? sc_uint<7>(0) : twiddle_addr_reg;
            twiddle_addr_reg_out    -> set(twiddle_addr_reg);
            rounds_count_in          -> get(rounds_count);
            chunk_rand_offset_in     -> get(chunk_rand_offset);
            shuffle_en_in            -> get(shuffle_en);
            base_address_port        -> get(base_address);
            base_address_temp        = (rounds_count == 0)? base_address.source: (rounds_count[0])? base_address.interim:base_address.destination;
            mem_rd_next_addr         = read_req.address;
            read_req.address         = shuffle_en ?static_cast<sc_uint<15>>(base_address_temp + chunk_rand_offset):static_cast<sc_uint<15>>(base_address_temp);
        
        if ( wr_stage_set && !ntt_done) {     
  
           read_req.request        =  false;
           mem_read_req_port       -> set(read_req);
           next_state = CtReadStatesType::CtReadBuf; 
        } else if(ntt_done) {
            read_req.request        =  false;
            mem_read_req_port       -> set(read_req);
            next_state = CtReadStatesType::CtReadIdle;
        } else {
            read_req.request        =  false;
            mem_read_req_port       -> set(read_req);
            next_state = CtReadStatesType::CtReadStage;
        }
      } else if (read_state == CtReadStatesType::CtReadBuf) {

        insert_state("read_buf");
        
            
             pw_rden                  = false;
             pw_wren                  = false;
             pw_rden_out              -> set(pw_rden);
             pw_wren_out              -> set(pw_wren);
             buf_wren_ntt_reg         = true;
             buf0_valid               = false;   
             buf0_valid_in            -> get(buf0_valid);          
             buf_rden_ntt_reg         = buf0_valid;   
             buf_wren_out             -> set(buf_wren_ntt_reg);   
             buf_rden_out             -> set(buf_rden_ntt_reg);             
             buf0_valid_in            -> get(buf0_valid);
             bf_enable_reg            = buf0_valid;            
             bf_enable_out            -> set(bf_enable_reg);
             masking_en_ctrl          = false;
             opcode                   = sc_uint<2>(0);
             masking_en_ctrl_out     -> set(masking_en_ctrl);
             opcode_port             -> set(opcode);
             shuffle_en_in           -> get(shuffle_en);
       
             buf_rdptr_f            = shuffle_en ? (static_cast<sc_uint<2>>(index_rand_offset.range(1,0) + buf_count)) : static_cast<sc_uint<2>>(buf_count);
             buf_rdptr_f_out       -> set(buf_rdptr_f);
      
             bool buf0_valid        = false;
             buf0_valid_in          -> get(buf0_valid);
             butterfly_ready        = false;
             butterfly_ready_in     -> get(butterfly_ready);
             rounds_count_in        -> get(rounds_count);
             chunk_count_in         -> get(chunk_count);
             twiddle_addr_reg       = buf0_valid?(shuffle_en ? static_cast<sc_uint<7>>(twiddle_rand_offset(rounds_count,buf_rdptr_f,chunk_count)) : (twiddle_addr_reg == static_cast<sc_uint<7>>(twiddle_end_addr(rounds_count))) ?  static_cast<sc_uint<7>>(0) : static_cast<sc_uint<7>>(twiddle_addr_reg + 1)):twiddle_addr_reg;
             twiddle_addr_reg_out  -> set(twiddle_addr_reg);
             rounds_count_in        -> get(rounds_count);
             base_address_port      -> get(base_address);
             base_address_temp      = (rounds_count == 0)? base_address.source: (rounds_count[0])? base_address.interim:base_address.destination;
             rd_wrap_around         = (read_req.address + NTT_READ_ADDR_STEP > (base_address_temp + sc_uint<14>(63)));
             mem_rd_next_addr       =  read_req.address + NTT_READ_ADDR_STEP;
             last_rd_addr           = (read_req.address == base_address_temp +sc_uint<14>(63));

             shuffle_en_in          -> get(shuffle_en);

             read_req.address       = shuffle_en ? (last_rd_addr ? static_cast<sc_uint<16>>(base_address_temp) : 
                                            (rd_wrap_around ? static_cast<sc_uint<16>>(mem_rd_next_addr - sc_uint<16>(63)) 
                                           : mem_rd_next_addr.range(14, 0)))
                                           : (rd_wrap_around ? static_cast<sc_uint<16>>(mem_rd_next_addr - sc_uint<16>(63)) 
                                           : mem_rd_next_addr.range(14, 0));
                        
            read_req.request       =  true;
            mem_read_req_port      -> set(read_req);
            buf0_valid             = false;
            buf0_valid_in         -> get(buf0_valid);

         if (buf0_valid ) {
       
           next_state = CtReadStatesType::CtReadExec;
         } else {
           next_state = CtReadStatesType::CtReadBuf;
         }
       }
       else if (read_state == CtReadStatesType::CtReadExec) {  {
        insert_state("read_exec");
           
            pw_rden                 = false;
            pw_wren                 = false;
            pw_rden_out             -> set(pw_rden);
            pw_wren_out             -> set(pw_wren);
            buf_wren_ntt_reg        = true;   
            buf_rden_ntt_reg        = true;   
            buf_wren_out            -> set(buf_wren_ntt_reg);   
            buf_rden_out            -> set(buf_rden_ntt_reg); 
            bf_enable_reg           = true;            
            bf_enable_out           -> set(bf_enable_reg);
            masking_en_ctrl         = false;
            opcode                  = sc_uint<2>(0);
            masking_en_ctrl_out     -> set(masking_en_ctrl);
            opcode_port             -> set(opcode);
            shuffle_en_in           -> get(shuffle_en);
            buf_rdptr_f             = shuffle_en ? (static_cast<sc_uint<2>>(index_rand_offset.range(1,0) + buf_count)) : static_cast<sc_uint<2>>(buf_count);
            buf_rdptr_f_out         -> set(buf_rdptr_f);
      
            buf0_valid              = false;
            buf0_valid_in           -> get(buf0_valid);
            chunk_count_in          -> get(chunk_count);
            rounds_count_in         -> get(rounds_count);
            twiddle_addr_reg        = shuffle_en ? static_cast<sc_uint<7>>(twiddle_rand_offset(rounds_count,buf_rdptr_f,chunk_count)) : (twiddle_addr_reg == static_cast<sc_uint<7>>(twiddle_end_addr(rounds_count))) ?  static_cast<sc_uint<7>>(0) : static_cast<sc_uint<7>>(twiddle_addr_reg + 1);
       
            rounds_count_in          -> get(rounds_count);
            base_address_port        -> get(base_address);
            base_address_temp        = (rounds_count == 0)? base_address.source: (rounds_count[0])? base_address.interim:base_address.destination;
            shuffle_en_in             -> get(shuffle_en);
            /*read_req.request         = shuffle_en ?
                                     (((read_req.address <= MEM_LAST_ADDR + base_address_temp) && !((buf_count == sc_biguint<2>(3)) && (rd_valid_count ==  sc_biguint<7>(60))) ) 
                                     ? true : false)             
                                     : ((read_req.address <= (base_address_temp + MEM_LAST_ADDR)) ? true : false);*/
            read_req.request         =
                                     (((read_req.address <= MEM_LAST_ADDR + base_address_temp) && !((buf_count == sc_biguint<2>(3)) && (rd_valid_count ==  sc_biguint<7>(60))) ) 
                                     ? true : false);                     //shuffle_en condition is no longer there (line 908)
            rd_wrap_around           = (mem_rd_next_addr > (base_address_temp + MEM_LAST_ADDR));
            last_rd_addr             =  (read_req.address == (base_address_temp +MEM_LAST_ADDR));
            mem_rd_next_addr         =  read_req.address + NTT_READ_ADDR_STEP;
            shuffle_en_in            -> get(shuffle_en);
            mem_rd_next_addr        = read_req.address + NTT_READ_ADDR_STEP;
            read_req.address        = shuffle_en ? (last_rd_addr ? static_cast<sc_uint<16>>(base_address_temp) : 
                                      (rd_wrap_around ? static_cast<sc_uint<16>>(mem_rd_next_addr - sc_uint<16>(63)) 
                                    : mem_rd_next_addr.range(14, 0)))
                                    : (rd_wrap_around ? static_cast<sc_uint<16>>(mem_rd_next_addr - sc_uint<16>(63)) 
                                    : mem_rd_next_addr.range(14, 0));

                                 
          // mem_read_req_port  -> set(read_req);

   
        buf0_valid = false;
        buf0_valid_in->get(buf0_valid);
  

        if ((rd_valid_count < static_cast<sc_biguint<7>>(0x40U)) && (buf_count == static_cast<sc_biguint<2>>(0)) && !buf0_valid) {
          next_state = CtReadStatesType::CtReadBuf;
        } else if((buf_count == static_cast<sc_biguint<2>>(0x3U)) && (rd_valid_count == static_cast<sc_biguint<7>>(0x3CU))) {       
         //  read_req.request = true;
      
           mem_read_req_port  -> set(read_req);
           twiddle_addr_reg_out -> set(twiddle_addr_reg);
           next_state = CtReadStatesType::CtReadExecwait;
        } else{

            mem_read_req_port  -> set(read_req);
            twiddle_addr_reg_out -> set(twiddle_addr_reg);
       
            next_state = CtReadStatesType::CtReadExec;
        }
      }
  
    }
    else{
        insert_state("read_exec_wait");

         
             pw_rden             = false;
             pw_wren             = false;
             pw_rden_out         -> set(pw_rden);
             pw_wren_out         -> set(pw_wren);
             buf_wren_ntt_reg    = (buf_count < 3);   
             buf_rden_ntt_reg    = true;
             buf_wren_out        -> set(buf_wren_ntt_reg);   
             buf_rden_out        -> set(buf_rden_ntt_reg); 
             bool bf_enable_reg  = (buf_count <= 3);            
             bf_enable_out       -> set(bf_enable_reg);
      
       
             masking_en_ctrl           = false;
             opcode                    = sc_uint<2>(0);
             masking_en_ctrl_out       -> set(masking_en_ctrl);
             opcode_port               -> set(opcode);
      
             shuffle_en_in             -> get(shuffle_en);
     
  
             buf_rdptr_f               = shuffle_en ? (static_cast<sc_uint<2>>(index_rand_offset.range(1,0) + buf_count)) :  static_cast<sc_uint<2>>(buf_count);
             buf_rdptr_f_out          -> set(buf_rdptr_f);
        
             buf0_valid               = false;
             buf0_valid_in            -> get(buf0_valid);
             chunk_count_in           -> get(chunk_count);
             rounds_count_in          -> get(rounds_count);
             twiddle_addr_reg         = shuffle_en ? static_cast<sc_uint<7>>(twiddle_rand_offset(rounds_count,buf_rdptr_f,chunk_count)) : (twiddle_addr_reg == static_cast<sc_uint<7>>(twiddle_end_addr(rounds_count))) ?  static_cast<sc_uint<7>>(0) : static_cast<sc_uint<7>>(twiddle_addr_reg + 1);
             twiddle_addr_reg_out     -> set(twiddle_addr_reg);
       
             rounds_count_in          -> get(rounds_count);
             base_address_port        -> get(base_address);
             base_address_temp        = (rounds_count == 0)? base_address.source: (rounds_count[0])? base_address.interim:base_address.destination;
             read_req.request         =  false;
             mem_read_req_port        -> set(read_req);

      if ((rd_valid_count == static_cast<sc_biguint<7>>(0x40U)) && (buf_count == static_cast<sc_biguint<2>>(3))) {
        read_req.request  =  false;
        mem_read_req_port  -> set(read_req);
        next_state = CtReadStatesType::CtReadStage;
      } else {
 
        read_req.request  =  false;
        mem_read_req_port  -> set(read_req);
        next_state = CtReadStatesType::CtReadExecwait;
      }
    
      
    }

    bool mlkem = false;
    mlkem_in->get(mlkem);

    rounds_count_in-> get(rounds_count);

    ntt_passthrough_out->set(mlkem && rounds_count == 3);  //new output

   
     
      
        buf0_valid      = false;
        buf0_valid_in   -> get(buf0_valid);
        buf_count       =  (buf0_valid || (buf_count > 0 && buf_count < 3)) ? static_cast<sc_uint<2>>(buf_count + 1)
                         : static_cast<sc_uint<2>>(0);
  
    
       rd_valid_count   = (read_state == CtReadStatesType::CtReadIdle||read_state == CtReadStatesType::CtReadStage||(buf0_valid && (rd_valid_count > sc_biguint<7>(64)))) 
                          ?  sc_biguint<7>(0) : buf0_valid ? static_cast<sc_biguint<7>>(rd_valid_count +  sc_biguint<7>(4)) :rd_valid_count;  
    
     
       random_in                      -> get(random);    
       latch_index_rand_offset_port   -> get(latch_index_rand_offset);
       index_rand_offset               =  (latch_index_rand_offset)? random.range(1,0): index_rand_offset;
  
       butterfly_ready        = false;
       butterfly_ready_in    -> get(butterfly_ready);
     
       chunk_count_reg_1     = (butterfly_ready || ((buf0_valid)&&(read_state == CtReadStatesType::CtReadBuf))||(read_state == CtReadStatesType::CtReadExec)|| (read_state == CtReadStatesType::CtReadExecwait))
                              ? static_cast<sc_uint<44>>(static_cast<sc_uint<44>>(chunk_count_reg_1 >> 4) | (static_cast<sc_uint<44>>(chunk_count) << 40))
                              : static_cast<sc_uint<44>>(chunk_count_reg_1);
     

       butterfly_ready         = false;
       butterfly_ready_in      -> get(butterfly_ready);
       buf_rdptr_reg_1         = (butterfly_ready) ||(((buf0_valid)&&( read_state == CtReadStatesType::CtReadBuf))||((read_state == CtReadStatesType::CtReadExec))|| (read_state == CtReadStatesType::CtReadExecwait))
                                 ? static_cast<sc_uint<24>>(static_cast<sc_uint<24>>(buf_rdptr_reg_1 >> 2) | (static_cast<sc_uint<24>>(buf_rdptr_f ) << 20))
                                 : static_cast<sc_uint<24>>(0);
    
    

     read_state = next_state;
  }
}


  [[noreturn]] void write() {
    CtWriteStatesType write_state;
    CtWriteStatesType next_state = CtWriteStatesType::CtWriteIdle;
    bool latch_chunk_rand_offset = false;

    sc_biguint<3> rounds_count;
    sc_uint<4>    chunk_count;
    sc_uint<4>    chunk_rand_offset;
    Base_Address base_address;
    sc_uint<6> random;
   
    while (true) {
      if (write_state == CtWriteStatesType::CtWriteIdle) {
        insert_state("write_idle");

        latch_chunk_rand_offset  = false;
        rounds_count             = 0;
        rounds_count_out         -> set(rounds_count);
        
        base_address_port        -> get(base_address);
        base_address_temp_write  = (rounds_count[0])? base_address.destination:base_address.interim;
        chunk_count_reg_port     -> get(chunk_count_reg);
        buf_rdptr_reg_port       -> get(buf_rdptr_reg);
        mem_wr_next_addr         = shuffle_en ?
                                   static_cast<sc_uint<16>>((4 * chunk_count_reg) + base_address_temp_write)
                                   :static_cast<sc_uint<16>>(write_req.address);

  
       write_req.address          = shuffle_en? static_cast<sc_uint<15>>((base_address_temp_write) + 4 *(chunk_rand_offset)): static_cast<sc_uint<15>>(base_address_temp_write);
       write_req.request          =  false;
       mem_write_req_port         -> set(write_req);

       bool ntt_enable            = false;
       ntt_enable_in              -> get(ntt_enable);

        if (ntt_enable) {
          latch_chunk_rand_offset = true;
          next_state = CtWriteStatesType::CtWriteStage;
        } else {
          next_state = CtWriteStatesType::CtWriteIdle;
        }
      } else if (write_state == CtWriteStatesType::CtWriteStage) {
        insert_state("write_stage");

        latch_chunk_rand_offset    = false;

        base_address_port          -> get(base_address);
        base_address_temp_write    = (rounds_count[0])? base_address.destination:base_address.interim;
        chunk_count_reg_port       -> get(chunk_count_reg);
        buf_rdptr_reg_port         -> get(buf_rdptr_reg);
        mem_wr_next_addr           = shuffle_en? static_cast<sc_uint<16>>((4 * chunk_count_reg)  + base_address_temp_write)
                                   : static_cast<sc_uint<16>>(write_req.address);
    
        write_req.address          = shuffle_en? static_cast<sc_uint<15>>((base_address_temp_write) + 4 *(chunk_rand_offset)): static_cast<sc_uint<15>>(base_address_temp_write);
        write_req.request          =  false;
        mem_write_req_port         -> set(write_req);
                  
        wr_stage_set = true;
        if (ntt_done) {
          rounds_count      =  sc_uint<3>(0);
          rounds_count_out  -> set(rounds_count);
          next_state = CtWriteStatesType::CtWriteIdle;
        } 
        else if (!ntt_done) {
          next_state = CtWriteStatesType::CtWriteMem;
        } else 
        {
          next_state = CtWriteStatesType::CtWriteStage;
        }

      } else if( write_state == CtWriteStatesType::CtWriteMem) {
        insert_state("write_mem");
        latch_chunk_rand_offset = false;
        
       bool mlkem = false;
       mlkem_in->get(mlkem);

       base_address_port        -> get(base_address);
       base_address_temp_write  = (rounds_count[0])? base_address.destination:base_address.interim;
       chunk_count_reg_port     -> get(chunk_count_reg);
       buf_rdptr_reg_port       -> get(buf_rdptr_reg);
       mlkem_chunk_count_reg_port     -> get(mlkem_chunk_count_reg);
       mlkem_buf_rdptr_reg_port       -> get(mlkem_buf_rdptr_reg);
       mem_wr_next_addr         = shuffle_en ? mlkem ? static_cast<sc_uint<16>>((4 * mlkem_chunk_count_reg) + (mlkem_buf_rdptr_reg) + base_address_temp_write)
                                : static_cast<sc_uint<16>>((4 * chunk_count_reg) + ( buf_rdptr_reg) + base_address_temp_write)
                                : static_cast<sc_uint<16>>((write_req.address)+ NTT_WRITE_ADDR_STEP);
       wr_wrap_around           = (mem_wr_next_addr >  base_address_temp_write + sc_uint<14>(63));
       bool butterfly_ready     = false;
       butterfly_ready_in      -> get(butterfly_ready);
       write_req.request       =  butterfly_ready;
       write_req.address       = butterfly_ready ?static_cast<sc_uint<15>>(wr_wrap_around? static_cast<sc_uint<16>>(mem_wr_next_addr - sc_uint<16>(63)):mem_wr_next_addr.range(14,0)) :write_req.address;
       mem_write_req_port      -> set(write_req);

        bool buf0_valid    = false;
        buf0_valid_in      -> get(buf0_valid);
        

        if (wr_valid_count == 0x3FU) {
          latch_chunk_rand_offset  = true;
          bool  butterfly_ready    = false;
          butterfly_ready_in       -> get(butterfly_ready);
          write_req.request        =  butterfly_ready;
          mem_write_req_port       -> set(write_req);
         
          rounds_count       = (rounds_count < 4 ) ? static_cast<sc_uint<3>>(rounds_count + 1) : sc_uint<3>(0);
          rounds_count_out  -> set(rounds_count);
          next_state = CtWriteStatesType::CtWriteStage;

        }
         else {
            butterfly_ready = false;
            butterfly_ready_in  -> get(butterfly_ready);
            write_req.request   =  butterfly_ready;
            mem_write_req_port  -> set(write_req);
            next_state = CtWriteStatesType::CtWriteMem;
        }
       
      } 
    
      random_in             -> get(random);
      bool butterfly_ready  = false;
      butterfly_ready_in    -> get(butterfly_ready);
      wr_valid_count        = ((write_state == CtWriteStatesType::CtWriteMem)?( (butterfly_ready?static_cast<sc_uint<7>>(wr_valid_count + sc_uint<7>(1)) : static_cast<sc_uint<7>>(wr_valid_count))): sc_uint<7>(0)); 
      chunk_rand_offset       = latch_chunk_rand_offset?random.range(5,2):chunk_rand_offset;
      chunk_count             = latch_chunk_rand_offset?random.range(5,2):(buf_count == 3? static_cast<sc_uint<4>>(chunk_count + 1) : chunk_count);
 
      write_state = next_state;
    }

  }
 
};

#endif