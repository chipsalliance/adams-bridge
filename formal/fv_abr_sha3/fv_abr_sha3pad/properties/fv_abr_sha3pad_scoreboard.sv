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

// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Contact: contact@lubis-eda.com
// -------------------------------------------------

module fv_abr_sha3pad_scoreboard
#( 	
    parameter  DATA_WIDTH         = 20                       ,
    parameter  type INPUT_TYPE    = bit [DATA_WIDTH-1:0]     ,
    parameter  type EXP_DATA_TYPE = bit [DATA_WIDTH-1:0]     ,
	parameter  DEPTH              = 128                      ,
    // Set to 1 if push and pop can happen at the same clock cycle, when the system is empty
    parameter  BYPASS             = 0                        ,
    parameter  ASSUME_INVARIANTS  = 0                        ,
  	localparam DEPTH_WIDTH        = (DEPTH == 1 ? 1 : $clog2(DEPTH))
)
(
    input logic  	              clk                 ,
	input logic  	              rst                 ,
    input logic                   soft_rst            ,
    input logic  	              push                ,
	input logic  	              pop                 ,
	input logic  	              full                ,
	input logic  	              empty               ,
	input INPUT_TYPE              data_in             ,
    input EXP_DATA_TYPE           data_out            ,
    input EXP_DATA_TYPE           expected_data       ,
    input logic [DEPTH_WIDTH-1:0] incr_val            ,

    output logic                  sampled_in          ,
    output logic                  sampled_in_reg      ,
    output logic                  sampled_out         ,
    output logic                  sampled_out_reg     ,
    output INPUT_TYPE             chosen_symbolic_data,
    output logic [DEPTH_WIDTH:0]  tracking_counter_out        
);

    default clocking default_clk @(posedge clk); endclocking

    lubis_scoreboard_tracking
    #( 	
        .INPUT_TYPE        (INPUT_TYPE       ),
        .DEPTH             (DEPTH            ),
        .BYPASS            (BYPASS           ),
        .ASSUME_INVARIANTS (ASSUME_INVARIANTS)
    ) lubis_scoreboard_tracking_i
    (
        .clk                 (clk                 ),
        .rst                 (rst                 ),
        .soft_rst            (soft_rst            ),
        .push                (push                ),
        .pop                 (pop                 ),
        .full                (full                ),
        .empty               (empty               ),
        .data_in             (data_in             ),
        .incr_val            (incr_val            ),
        .sampled_in          (sampled_in          ),
        .sampled_in_reg      (sampled_in_reg      ),
        .sampled_out         (sampled_out         ),
        .sampled_out_reg     (sampled_out_reg     ),
        .chosen_symbolic_data(chosen_symbolic_data),
        .tracking_counter_out(tracking_counter_out)        
    );

    lubis_scoreboard_properties
    #( 	
        .EXP_DATA_TYPE(EXP_DATA_TYPE)
    ) lubis_scoreboard_properties_i
    (
        .clk          (clk          ),
        .rst          (rst          ),
        .soft_rst     (soft_rst     ),
        .data_out     (data_out     ),
        .expected_data(expected_data),
        .sampled_in   (sampled_in   ),
        .sampled_out  (sampled_out  )    
    );

endmodule
