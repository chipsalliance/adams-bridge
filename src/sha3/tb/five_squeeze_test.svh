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
//
//======================================================================
 
//----------------------------------------------------------------
// five_squeeze_test(...)
//
// Simulates generation of Matrix A coefficients 
//----------------------------------------------------------------
task five_squeeze_test(); 
    int fd_r_exp;
    string line_read;

    //open expected results files
    fd_r_exp = $fopen(exp_res_filename, "r");
    if (fd_r_exp == 0) begin
      $error("Cannot open file %s for reading", exp_res_filename);
      error_ctr++;
    end

    for (int iter = 0; iter < VEC_CNT; iter++) begin
      //get the next exp result
      if (!($fgets(line_read, fd_r_exp))) begin
        $error("Failed to read a new line");
        error_ctr++;
      end
      void'($sscanf(line_read, "%h", exp_result));

      //start keccak
      @(posedge clk_tb);
      sha3_start <= 1;
      @(posedge clk_tb);
      sha3_start <= 0;

      if (iter == 0) begin
        mode <= test_vector_q[0].mode;
        strength <= test_vector_q[0].strength;

        //start new message
        @(posedge clk_tb);
        msg_start <= 1;
        @(posedge clk_tb);
        msg_start <= 0;

        //send the input vector
        for (int i = 0; i < MAX_MSG_WR; i++) begin
          if ( |test_vector_q[0].input_valid[i] ) begin
            write_single_msg(test_vector_q[0].input_vector[i], test_vector_q[0].input_valid[i]);
          end
        end
        test_vector_q.pop_front();
    
      end

      //process the block
      sha3_process <= 1;
      @(posedge clk_tb);
      sha3_process <= 0;
  
      wait (sha3_state_vld == 1'b1);
        
      //check absorb
      check_results();

      fork
        begin
          //Do 5 squeeze
          for (int i = 0; i < 5; i++) begin
            sha3_run <= 1'b1;
            @(posedge clk_tb);
            sha3_run <= 1'b0;
            @(posedge clk_tb);


            wait (sha3_state_vld == 1'b1);

            //check squeeze
            check_results(1'b1, i);
          end

          @(posedge clk_tb);
          sha3_done = abr_prim_mubi_pkg::MuBi4True;
          @(posedge clk_tb);
          sha3_done = abr_prim_mubi_pkg::MuBi4False;

        end
        begin
          //send the next vector while squeezing
          //start msg buffer
          if (iter != VEC_CNT-1) begin
            mode <= test_vector_q[0].mode;
            strength <= test_vector_q[0].strength;
          end

          @(posedge clk_tb);
          msg_start <= 1;
          @(posedge clk_tb);
          msg_start <= 0;

          //send the input vector
          for (int i = 0; i < MAX_MSG_WR; i++) begin
            if ( |test_vector_q[0].input_valid[i] ) begin
              write_single_msg(test_vector_q[0].input_vector[i], test_vector_q[0].input_valid[i]);
            end
          end
          test_vector_q.pop_front();
        end
      join

      tc_ctr++;
    end

    $fclose(fd_r_exp);
endtask