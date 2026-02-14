# Compress
Date: 25-08-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_compress** for the module **compress**. 

The **formal/fv_compress**  contains the top level verification assertion IP(AIP) named as **fv_compress_top.sv**, containing the properties. The constraints are written in **fv_compress_constraints.sv**. We also have common aip that implements scoreboard to check the data integrity and ordering of the api and memory interfaces.


## DUT Overview

The DUT **compress** has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                               |
| 2    | reset_n           | input     | The reset signal is active low and resets the design                                   |
| 3    | zeroize           | input     | The design is reset when this signal is triggered.                                     |
| 4    | compress_enable   | input     | Triggers the compression operation                                                     |
| 5    | compare_mode      | input     | Selects if compare mode should be used                                                 | 
| 6    | mode              | input     | Selects the compression mode                                                           | 
| 7    | num_poly          | input     | Selects the number of polynomials to be porcessed                                      | 
| 8    | src_base_addr     | input     | The base address of the read memory                                                    |
| 9    | dest_base_addr    | input     | The base address of the api memory                                                     |
| 10   | mem_rd_req        | output    | The read request interface to the memory                                               |
| 11   | mem_rd_data       | input     | The data that is read from the memory                                                  |
| 12   | api_rw_en         | output    | read/write request interface to the api memory                                         |
| 13   | api_rw_addr       | output    | read/write address of the request to the api memory                                    |
| 14   | api_wr_data       | output    | Write data to the api memory                                                           |
| 15   | api_rd_data       | input     | Data read from the api memory                                                          |
| 16   | compare_failed    | output    | Signals that the comparison mode failed                                                |
| 17   | compress_done     | output    | Signals the end of the compression                                                     |

The design serves as a compression unit that compresses 4 coefficients per polynomial fetched from the memory and the result is written to the API memory as 32-bit chunks

## Assertion IP Overview
The Assertion IP signals are bound with the respective signals in the dut. The assertions checks the behavior of all outputs using standard assertions and scoreboards.

### fv_compress_top.sv
- fv_compress_mem_req_sb: Checks the ordering and integrity of the requests going through the memory read interface.
- fv_compress_api_mem_write_req_sb: Checks the ordering and integrity of the requests going through the api memory write interface.
- fv_compress_api_mem_read_req_sb: Checks the ordering and integrity of the requests going through the api memory read interface.
- assert_compress_done_safety_high and assert_compress_done_after_low: Check the behavior of the compress_done output.
- assert_no_activities: Check the IDLE behaviour
- assert_compare_failed and assert_compare_failed_v2: Check the behaviour of the compare_failed signal during compare mode.

## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load the AIP, the design and fv_compress_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts and common aip. 
