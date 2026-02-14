# ABR CTRL (MLKEM)
Date: 26-09-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_abr_ctrl** for the module **abr_ctrl**. 

The **formal/fv_abr_ctrl**  contains the top level verification assertion IP(AIP) named as **fv_abr_ctrl_wrapper.sv**, containing the instantiation of the induction proofs**model/mlkem_abr_ctrl.sv**, constraints**fv_abr_ctrl_constraints.sv** and whitebox checks**fv_abr_ctrl_whitebox.sv**.


## DUT Overview

The DUT **abr_ctrl** has the primary inputs and primary outputs as shown below.

|--------------------------------------------------------------------------------------|
|direction|type                                        |name                           |
|---------|--------------------------------------------|-------------------------------|
|input    |logic                                       |clk                            |
|input    |logic                                       |rst_b                          |
|output   |logic                                       |zeroize                        |
|output   |abr_reg__in_t                               |abr_reg_hwif_in_o              |
|input    |abr_reg__out_t                              |abr_reg_hwif_out_i             |
|output   |abr_sampler_mode_e                          |sampler_mode_o                 |
|output   |logic                                       |sha3_start_o                   |
|output   |logic                                       |msg_start_o                    |
|output   |logic                                       |msg_valid_o                    |
|input    |logic                                       |msg_rdy_i                      |
|output   |logic [MsgStrbW-1:0]                        |msg_strobe_o                   |
|output   |logic [MsgWidth-1:0]                        |msg_data_o                     |
|output   |logic                                       |sampler_start_o                |
|input    |logic                                       |sampler_busy_i                 |
|input    |logic                                       |sampler_state_dv_i             |
|input    |logic [abr_sha3_pkg::StateW-1:0]            |sampler_state_data_i           |
|output   |logic [ABR_MEM_ADDR_WIDTH-1:0]              |dest_base_addr_o               |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_enable_o                   |
|output   |abr_ntt_mode_e [ABR_NUM_NTT-1:0]            |ntt_mode_o                     |
|output   |ntt_mem_addr_t [ABR_NUM_NTT-1:0]            |ntt_mem_base_addr_o            |
|output   |pwo_mem_addr_t [ABR_NUM_NTT-1:0]            |pwo_mem_base_addr_o            |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_masking_en_o               |
|output   |logic [ABR_NUM_NTT-1:0]                     |ntt_shuffling_en_o             |
|input    |logic [ABR_NUM_NTT-1:0]                     |ntt_busy_i                     |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_src0_base_addr_o           |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_src1_base_addr_o           |
|output   |logic [1:0][ABR_MEM_ADDR_WIDTH-1:0]         |aux_dest_base_addr_o           |
|output   |logic                                       |power2round_enable_o           |
|input    |mem_if_t [1:0]                              |pwr2rnd_keymem_if_i            |
|input    |logic [1:0][DATA_WIDTH-1:0]                 |pwr2rnd_wr_data_i              |
|input    |logic                                       |pk_t1_wren_i                   |
|input    |logic [7:0][9:0]                            |pk_t1_wrdata_i                 |
|input    |logic [7:0]                                 |pk_t1_wr_addr_i                |
|input    |logic                                       |power2round_done_i             |
|output   |logic                                       |decompose_enable_o             |
|output   |logic                                       |decompose_mode_o               |
|input    |logic                                       |decompose_done_i               |
|output   |logic                                       |skencode_enable_o              |
|input    |mem_if_t                                    |skencode_keymem_if_i           |
|input    |logic [DATA_WIDTH-1:0]                      |skencode_wr_data_i             |
|input    |logic                                       |skencode_done_i                |
|output   |logic                                       |skdecode_enable_o              |
|input    |mem_if_t [1:0]                              |skdecode_keymem_if_i           |
|output   |logic [1:0][DATA_WIDTH-1:0]                 |skdecode_rd_data_o             |
|input    |logic                                       |skdecode_done_i                |
|input    |logic                                       |skdecode_error_i               |
|output   |logic                                       |makehint_enable_o              |
|input    |logic                                       |makehint_invalid_i             |
|input    |logic                                       |makehint_done_i                |
|input    |logic                                       |makehint_reg_wren_i            |
|input    |logic [3:0][7:0]                            |makehint_reg_wrdata_i          |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |makehint_reg_wr_addr_i         |
|output   |logic                                       |normcheck_enable_o             |
|output   |logic [1:0]                                 |normcheck_mode_o               |
|input    |logic                                       |normcheck_invalid_i            |
|input    |logic                                       |normcheck_done_i               |
|output   |logic                                       |sigencode_enable_o             |
|input    |mem_if_t                                    |sigencode_wr_req_i             |
|input    |logic [1:0][3:0][19:0]                      |sigencode_wr_data_i            |
|input    |logic                                       |sigencode_done_i               |
|output   |logic                                       |pkdecode_enable_o              |
|input    |logic [7:0]                                 |pkdecode_rd_addr_i             |
|output   |logic [7:0][T1_COEFF_W-1:0]                 |pkdecode_rd_data_o             |
|input    |logic                                       |pkdecode_done_i                |
|output   |logic                                       |sigdecode_h_enable_o           |
|output   |logic [SIGNATURE_H_VALID_NUM_BYTES-1:0][7:0]|signature_h_o                  |
|input    |logic                                       |sigdecode_h_invalid_i          |
|input    |logic                                       |sigdecode_h_done_i             |
|output   |logic                                       |sigdecode_z_enable_o           |
|input    |mem_if_t                                    |sigdecode_z_rd_req_i           |
|output   |logic [1:0][3:0][19:0]                      |sigdecode_z_rd_data_o          |
|input    |logic                                       |sigdecode_z_done_i             |
|output   |logic                                       |compress_enable_o              |
|output   |compress_mode_t                             |compress_mode_o                |
|output   |logic                                       |compress_compare_mode_o        |
|output   |logic [2:0]                                 |compress_num_poly_o            |
|input    |logic                                       |compress_done_i                |
|input    |logic                                       |compress_compare_failed_i      |
|input    |logic [1:0]                                 |compress_api_rw_en_i           |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |compress_api_rw_addr_i         |
|input    |logic [DATA_WIDTH-1:0]                      |compress_api_wr_data_i         |
|output   |logic [DATA_WIDTH-1:0]                      |compress_api_rd_data_o         |
|output   |logic                                       |decompress_enable_o            |
|input    |logic                                       |decompress_done_i              |
|output   |decompress_mode_t                           |decompress_mode_o              |
|output   |logic [2:0]                                 |decompress_num_poly_o          |
|input    |logic                                       |decompress_api_rd_en_i         |
|input    |logic [ABR_MEM_ADDR_WIDTH-1:0]              |decompress_api_rd_addr_i       |
|output   |logic [1:0][DATA_WIDTH-1:0]                 |decompress_api_rd_data_o       |
|output   |logic                                       |lfsr_enable_o                  |
|output   |logic [1:0][LFSR_W-1:0]                     |lfsr_seed_o                    |
|output   |mem_if_t                                    |zeroize_mem_o                  |
|input    |logic                                       |debugUnlock_or_scan_mode_switch|
|output   |logic                                       |busy_o                         |
|output   |logic                                       |error_intr                     |
|output   |logic                                       |notif_intr                     |


## Assertion IP Overview
The Assertion IP signals are bound with the respective signals in the dut. The assertions checks the behavior of all outputs using standard assertions.

### fv_abr_ctrl_constraints.sv
Contains the constraints responsible to drive the auxiliary units inputs for compress,decompress,sampler and ntt. And for the main register. Since two techniques were used to verify the controller Initial Value abstraction(IVA) and counter abstraction.Necessary constraints were added.

- IVA on abr_prog_cntr.
- counter abstraction on msg_cnt.
- cut points on process signals so as to help for IVA.

In addition to these we can find macros as below
- NO_ABSTRACTION: This is used if IVA and cut points are not deployed and to verify the abstracted counters.
- EVENTUAL_ASSUME: This is used when expecting an an aux unit input rather than the fixed timing an arbitrary assertion of the aux signal, inorder to avaoid starvation.

### fv_abr_ctrl_whitebox.sv
Assertions in this module are targeting the registers and primary outputs of the design which have a direct influence from the ctrl registers or memory components. 

### model/mlkem_abr_ctrl.sv
Assertions here are verifying the triggers to the submodule compress, decompress,samplers and ntt along with addresses and data sent to keccak. These assertions are induction checks which means for every event in the state and the state itself is an assertion. This gives the confidence that the entire sequential state machine is unrolled and all the states are covered. And these checkers are generated from a high level model **mlkem.h**. This gives the formal tool an advantage with apply Initial Value Abstraction for the prog_cntr(Main driver for the controller) and applied counter abstraction for the msg_cnt.

### model/mlkem_*.sv
Other modules in the model folder except the mlkem_abr_ctrl have the data structures and functions necessary for the assertions and a binding file to connect the aip with the design.

## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load all the .sv files under properties/fv_abr_ctrl with the design.
 
Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 
