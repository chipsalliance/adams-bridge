# Decompress
Date: 25-08-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_decompress** for the module **decompress**. 

The **formal/fv_decompress**  contains the top level verification assertion IP(AIP) named as **fv_decompress_top.sv**, containing the properties. The constraints are written in **fv_decompress_constraints.sv**. We also have scoreboard aip that implements scoreboard to check the data integrity and ordering of the api and memory interfaces.

## DUT Overview

The DUT **decompress** has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | clk               | input     | The positive edge of the clk is used for all the signals                               |
| 2    | reset_n           | input     | The reset signal is active low and resets the design                                   |
| 3    | zeroize           | input     | The design is reset when this signal is triggered.                                     |
| 4    | decompress_enable | input     | Triggers the decompression operation                                                   |
| 5    | mode              | input     | Selects the decompression mode to be used                                              | 
| 5    | num_poly          | input     | Selects the number of polynomials to be porcessed                                      | 
| 6    | src_base_addr     | input     | The base address of the api memory                                                     |
| 7    | dest_base_addr    | input     | The base address of the memory                                                         |
| 8    | mem_wr_req        | output    | The write request interface to the memory                                              |
| 9    | mem_wr_data       | output    | The data that is should be written to the memory                                       |
| 10   | api_rd_en         | output    | Read request interface to the api memory                                               |
| 11   | api_rd_addr       | output    | Read address of the request to the api memory                                          |
| 12   | api_rd_data       | input     | Read data from the api memory                                                          |
| 13   | decompress_done   | output    | Signals the end of the decompression                                                   |

The design serves as a decompression unit that decompresses 4 coefficients per polynomial fetched from the api memory and the result is written to the memory.

## Assertion IP Overview
The Assertion IP signals are bound with the respective signals in the dut. The assertions checks the behavior of all outputs using standard assertions and scoreboards.

### fv_decompress_top.sv
- fv_decompress_api_mem_req_sb: Checks the ordering and integrity of the requests going through the api memory read interface.
- fv_decompress_mem_write_req_sb: Checks the ordering and integrity of the requests going through the memory write interface.
- assert_decompress_done_high_safety and assert_decompress_done_low_safety: Check the behavior of the decompress_done output.
- assert_no_activities: Check the IDLE behaviour

## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load the AIP, the design and fv_compress_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts and common aip. 
