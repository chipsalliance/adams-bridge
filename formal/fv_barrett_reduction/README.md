# barrett_reduction
Date: 08-08-2025
Author: LUBIS EDA

## Folder Structure
The formal project has individual verification benches for different modules. These are listed under the toplevel directory named **formal**. Under this directory, we have a directory named **fv_barrett_reduction** 

The **formal/fv_barrett_reduction**  contains the top level verification assertion IP(AIP) named as **fv_barrett_reduction_top.sv** where the properties are written, and the constraints are written in **fv_barrett_reduction_constraints.sv**. 


## DUT Overview

The DUT barrett_reduction has the primary inputs and primary outputs as shown below.

| S.No | Port              | Direction | Description                                                                            |
| ---- | ----------------- | --------- | ---------------------------------------------------------------------------------------|
| 1    | x                 | input     | The input which will be used for the division operation with the prime                 |
| 2    | inv               | output    | The quotient result of the division                                                    |
| 3    | r                 | output    | The remainder result of the division                                                   |



The design performs a combinational division of an input with the prime, and returns the quotient and remainder. This block is instantiated in all the ntt computations.

## Assertion IP Overview

The Assertion IP signals are bound with the respective signals in the dut. There assertions inside **fv_barrett_reduction_top.sv** perform end-to-end checks for the barrett_reduction module.

### fv_barrett_reduction_top.sv

- assert_quotient_computation: Checks that the quotient output "inv" result is computed correctly

- assert_remainder_computation: Checks that the remainder output "r" result is computed correctly


## Reproduce results

The AIP has been tested with two major FV tools. 

For reproducing the results:
Load the AIP, the design and fv_constraints together in your formal tool. 

Feel free to reach out to contact@lubis-eda.com to request the loadscripts. 
