![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Adam's Bridge ML-KEM Hardware Specification</p>

<p style="text-align: center;">Version 1.0</p>

<div style="page-break-after: always"></div>

# ML-KEM Overview

ML-KEM (Module-Lattice-Based Key-Encapsulation Mechanism) is a quantum-resistant Key exchange scheme defined in FIPS 203 \[2\].

# High-Level Overview

Adam’s Bridge MK-KEM accelerator has all the necessary components to execute a pure hardware PQC operation. The main operations that involve more computational complexity, such as NTT, hashing, and sampling units, are explained as follows.

 ![ML-KEM diagram](./images/media/MLKEM_image.png)

The security level of ML-KEM defined by NIST are as follows:

| Algorithm Name  | Security Level |
| :-------------- | :------------- |
| ML-KEM-512      | Level-1        |
| ML-KEM-768      | Level-3        |
| **ML-KEM-1024** | **Level-5**    |

CNSA 2.0 only allows the highest security level (Level-5) for PQC which is ML-KEM-1024, and **Adams Bridge only supports ML-KEM-1024 parameter set.**

# API

The ML-KEM-1024 architecture inputs and outputs are described in the following table.


| Name                        | Input/Output    | Operation       | Size (Byte)   |
| --------------------------- | --------------- | --------------- | ------------- |
| name                        | Output          | All             | 8             |
| version                     | Output          | All             | 8             |
| ctrl                        | Input           | All             | 4             |
| status                      | Output          | All             | 4             |
| entropy (SCA)               | Input           | All             | 64            |
| seed_d                      | Input           | Keygen          | 32            |
| seed_z                      | Input           | Keygen          | 32            |
| message                     | Input           | Encaps          | 32            |
| shared_key                  | Output          | Encaps/Decaps   | 32            |
| decaps_key                  | Input/Output    | Keygen/Decaps   | 3168          |
| encaps_key                  | Input/Output    | Keygen/Decaps   | 1568          |
| ciphertext                  | Input/Output    | Encaps/Decaps   | 1568          |
| Interrupt                   | Output          | All             | 520           |
| --------------------------- | --------------- | --------------- | ------------- |
| Total                       |                 |                 | 7040          |

## name

​Read-only register consists of the name of component. 

## version 

​Read-only register consists of the version of component. 

## CTRL 

​The control register consists of the following flags: 

| Bits     | Identifier | Access | Reset | Decoded | Name |
| :------- | :--------- | :----- | :---- | :------ | :--- |
| \[31:4\] | \-         | \-     | \-    |         | \-   |
| \[3\]    | ZEROIZE    | w      | 0x0   |         | \-   |
| \[2:0\]  | CTRL       | w      | 0x0   |         | \-   |

### ​CTRL 

CTRL command field contains two bits indicating:

* ​Ctrl \= 0b000 

​No Operation. 

* ​Ctrl \= 0b001 

​Trigs the core to start the initialization and perform keygen operation. 

* ​Ctrl \= 0b010 

​Trigs the core to start the Encapsulation operation.

* ​Ctrl \= 0b011 

​Trigs the core to start Decapsulation operation.

* Ctrl \= 0b100 

​Trigs the core to start the keygen+Decapsulation operation for a ciphertext block.  This mode decreases storage costs for the decaps_key (dk) by recalling keygen and using an on-the-fly decaps_key during the decapsultion process.

### ZEROIZE

Zeroize all internal registers: Zeroize all internal registers after process to avoid SCA leakage.  
Software write generates only a single-cycle pulse on the hardware interface and then will be erased.

## status 

​The read-only status register consists of the following flags: 

| Bits     | Identifier     | Access | Reset | Decoded | Name |
| :------- | :------------- | :----- | :---- | :------ | :--- |
| \[31:3\] | \-             | \-     | \-    |         | \-   |
| \[2\]    | DECAPS_FAILURE | r      | 0x0   |         | \-   |
| \[1\]    | VALID          | r      | 0x0   |         | \-   |
| \[0\]    | READY          | r      | 0x0   |         | \-   |

### READY 

​Indicates if the core is ready to process the inputs. 

### ​VALID 

​Indicates if the process is computed and the output is valid. 

### DECAPS_FAILURE

​Indicates if the decapsulation process is failed and the shared_key output is invalid. 

## entropy

Entropy is required for SCA countermeasures to randomize the inputs with no change in the outputs. The entropy can be any 512-bit value in \[0 : 2^512-1\]. 

The ML-KEM-1024 countermeasure requires several random vectors to randomize the intermediate values. An internal mechanism is considered to take one random vector of 512-bit (i.e., entropy register) and generate the required random vectors for different countermeasures.

## seed_d

Adams Bridge component seed_d register type definition 8 32-bit registers storing the 256-bit seed_d for keygen in big-endian representation. The seed can be any 256-bit value in \[0 : 2^256-1\].

## seed_z

Adams Bridge component seed_z register type definition 8 32-bit registers storing the 256-bit seed_z for keygen in big-endian representation. The seed can be any 256-bit value in \[0 : 2^256-1\].

## message

Adams Bridge component message register type definition 8 32-bit registers storing the 256-bit message for encapsulation in big-endian representation. The message can be any 256-bit value in \[0 : 2^256-1\].

## shared_key

This register stores the shared_key for generated by encapsulation or decapsulation operations.

## decaps_key

This register stores the decapsulation key generated in keygen. This register should be set before decapsulation operation.

If seed_d or seed_z comes from key vault, this register will not contain the decaps_key to avoid exposing secret assets to software.

## encaps_key

This register stores the encapsulation key generated in keygen. This register should be set before encapsulation operation.

## ciphertext

This register stores the ciphertext generated in encapsulation operation. This register should be set before decapsulation operation.

# ​Pseudocode 

## ​Keygen 

```cpp
Input:
    seed_d
    seed_z  
    entropy

Output:
    encaps_key
    decaps_key

// Wait for the core to be ready (STATUS flag should be 2'b01 or 2'b11)
read_data = 0
while read_data == 0:
    read_data = read(ADDR_STATUS)

// Feed the required inputs
write(ADDR_SEED_D, seed_d)
write(ADDR_SEED_Z, seed_z)
write(ADDR_ENTROPY, entropy)

// Trigger the core for performing Keygen
write(ADDR_CTRL, KEYGEN_CMD)  // (STATUS flag will be changed to 2'b00)

// Wait for the core to be ready and valid (STATUS flag should be 2'b11)
read_data = 0
while read_data == 0:
    read_data = read(ADDR_STATUS)

// Reading the outputs
encaps_key = read(ADDR_EK)
decaps_key = read(ADDR_DK)

// Return the outputs
return encaps_key, decaps_key
```
​ 
## Encapsulation

```cpp
​Input:
    msg            
    encaps_key               
    entropy        

Output:
    shared_key
    ciphertext

// Wait for the core to be ready (STATUS flag should be 2'b01 or 2'b11)
read_data = 0;
while (read_data == 0) {
    read_data = read(ADDR_STATUS);
}

// Feed the required inputs
write(ADDR_MSG, msg);
write(ADDR_EK, encaps_key);
write(ADDR_ENTROPY, entropy);

// Trigger the core for performing Encapsulation
write(ADDR_CTRL, ENCAPS_CMD);  // (STATUS flag will be changed to 2'b00)

// Wait for the core to be ready and valid (STATUS flag should be 2'b11)
read_data = 0;
while (read_data == 0) {
    read_data = read(ADDR_STATUS);
}

// Reading the outputs
shared_key = read(ADDR_SHAREDKEY);
ciphertext = read(ADDR_CIPHERTEXT);

// Return the output
return shared_key, ciphertext;
```

## Decapsulation

```cpp
Input:
    decaps_key
    ciphertext  
    entropy       

Output:
    shared_key
    decaps_failure

// Wait for the core to be ready (STATUS flag should be 2'b01 or 2'b11)
read_data = 0;
while (read_data == 0) {
    read_data = read(ADDR_STATUS);
}

// Feed the required inputs
write(ADDR_DK, decaps_key);
write(ADDR_CIPHERTEXT, ciphertext);
write(ADDR_ENTROPY, entropy);

// Trigger the core for performing decapsulation
write(ADDR_CTRL, DECAPS_CMD);  // (STATUS flag will be changed to 2'b00)

// Wait for the core to be ready and valid (STATUS flag should be 2'b11)
read_data = 0;
while (read_data == 0) {
    read_data = read(ADDR_STATUS);
}

// Reading the outputs
decaps_failure = read(ADDR_STATUS) & DECAPS_FAILURE_MASK;
shared_key = read(ADDR_SHAREDKEY);

// Return the output
return shared_key, decaps_failure;
```

## Keygen \+ Decapsulation

This mode decreases storage costs for the decaps_key (DK) by recalling keygen and using an on-the-fly decaps_key during the decapsulaiton process.

```cpp
Input:
    seed_d
    seed_z  
    ciphertext  
    entropy  

Output:
    shared_key
    decaps_failure

// Wait for the core to be ready (STATUS flag should be 2'b01 or 2'b11)
read_data = 0
while read_data == 0:
    read_data = read(ADDR_STATUS)

// Feed the required inputs
write(ADDR_SEED_D, seed_d)
write(ADDR_SEED_Z, seed_z)
write(ADDR_CIPHERTEXT, ciphertext);
write(ADDR_ENTROPY, entropy)

// Trigger the core for performing Keygen + Decapsulation
write(ADDR_CTRL, KEYGEN_DECAPS_CMD)  // (STATUS flag will be changed to 2'b00)

// Wait for the core to be ready and valid (STATUS flag should be 2'b11)
read_data = 0
while read_data == 0:
    read_data = read(ADDR_STATUS)

// Reading the outputs
decaps_failure = read(ADDR_STATUS) & DECAPS_FAILURE_MASK;
shared_key = read(ADDR_SHAREDKEY);

// Return the outputs
return shared_key, decaps_failure;
```
​ 
# Performance and Area Results

## ML-KEM-1024


# References:

[2] NIST, "FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard," August 13, 2024.