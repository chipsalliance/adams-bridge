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

module fv_abr_sha3pad_scoreboard_properties
#( 	
    parameter  DATA_WIDTH         = 20                       ,
    parameter  type EXP_DATA_TYPE = bit [DATA_WIDTH-1:0]     ,
	localparam INDEX_WIDTH        = ($bits(EXP_DATA_TYPE) == 1 ? 1 : $clog2($bits(EXP_DATA_TYPE)))
)
(
    input logic  	    clk          ,
	input logic  	    rst          ,
    input logic         soft_rst     ,
    input EXP_DATA_TYPE data_out     ,
    input EXP_DATA_TYPE expected_data,
    input logic         sampled_in   ,
    input logic         sampled_out      
);

    default clocking default_clk @(posedge clk); endclocking


    logic [INDEX_WIDTH-1:0] idx;
    sym_idx: assume property (##1 $stable(idx) && idx < $bits(EXP_DATA_TYPE));

    data_ordering_and_integrity: assert property (disable iff (rst)
        sampled_out 
    |-> 
        data_out[idx] == expected_data[idx]
    );

endmodule


