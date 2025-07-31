![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Adam's Bridge Hardware Specification</p>

<p style="text-align: center;">Version 1.0</p>

<div style="page-break-after: always"></div>

# Scope

This document defines technical specifications for a Adam's Bridge Post-Quantum Cryptography (PQC ML-DSA and ML-KEM) subsystem used in the Open Compute Project (OCP). This document shall comprise the Adam's Bridge technical specification.

# Overview

This document provides definitions and requirements for a Adam's Bridge Post-Quantum Cryptography (PQC ML-DSA and ML-KEM) subsystem. The document then relates these definitions to existing technologies, enabling device and platform vendors to better understand those technologies in trusted computing terms.

# Introduction

The advent of quantum computers poses a serious challenge to the security of cloud infrastructures and services, as they can potentially break the existing public-key cryptosystems, such as RSA and elliptic curve cryptography (ECC). Even though the gap between today’s quantum computers and the threats they pose to current public-key cryptography is large, the cloud landscape should act proactively and initiate the transition to the post-quantum era as early as possible. To comply with that, the U.S. government issued a National Security Memorandum in May 2022 that mandated federal agencies to migrate to PQC by 2035 \[1\]. 

The long-term security of cloud computing against quantum attacks depends on developing lattice-based cryptosystems, which are among the most promising PQC algorithms that are believed to be hard for both classical and quantum computers. The American National Institute of Standards and Technology (NIST) recognized this and selected CRYSTALS-KYBER (ML-KEM) \[2\] and CRYSTALS-Dilithium (ML-DSA) \[3\], two lattice-based algorithms, as standards for post-quantum key-establishment and digital signatures, respectively, in July 2022\. These cryptosystems are constructed on the hardness of the module learning-with-errors problem (M-LWE) in module lattices. 

To transition to PQC, we must develop hybrid cryptosystems to maintain industry or government regulations, while PQC updates will be applied thoroughly. Therefore, classical cryptosystems, e.g. ECC, cannot be eliminated even if PQC will significantly be developed.

Adam’s bridge was a mythological structure that existed to cross the formidable gulf that existed between two land masses. Asymmetric cryptography to post quantum is a similar formidable gap that exists in the world of cryptography and Adam’s bridge is the work undertaken to bridge the gap by building post quantum cryptographic accelerators.

This document shares the architectural characteristics of the proposed post-quantum Adams Bridge implementation. The proposed work divides the operations in the algorithms into multiple stages and executes them using pipelined processing architecture. An optimized cascading method is used within each stage and fine-tune each module individually to exploit multi-levels of parallelism to accelerate post-quantum Dilithium computation on hardware platforms to address performance and complexity challenges of PQC implementation. The proposed architecture uses various optimization techniques, including multi-levels of parallelism, designing reconfigurable cores, and implementing interleaved and pipelined architecture achieving significant speedup while maintaining high security and scalability. This work can facilitate the adoption and deployment of PQC in cloud computing and enhance the security and efficiency of cloud services and applications in the post-quantum era.

# Documentation

The project contains comprehensive documentation of all submodules for ML-DSA and ML-KEM:

- [ML-DSA Documentation](./AdamsBridge_MLDSA.md)
- [ML-KEM Documentation](./AdamsBridge_MLKEM.md)

# Memory requirement

The following table shows the required memory instances for Adam's Bridge:

| Instance            | Depth | Data Width | Strobe Width |
| --------------------| ----- | ---------- | ------------ |
| abr_sk_mem_bank0    | 596   | 32         |              |
| abr_sk_mem_bank1    | 596   | 32         |              |
| abr_w1_mem          | 512   | 4          |              |
| abr_mem_inst0_bank0 | 832   | 96         |              |
| abr_mem_inst0_bank1 | 832   | 96         |              |
| abr_mem_inst1       | 576   | 96         |              |
| abr_mem_inst2       | 1472  | 96         |              |
| abr_mem_inst3       | 64    | 384        |              |
| abr_sig_z_mem       | 224   | 160        | 8            |
| abr_pk_mem          | 64    | 320        | 8            |

All memories are modeled as 1 read 1 write port RAMs with a flopped read data.
See abr_1r1w_ram.sv and abr_1r1w_be_ram.sv for examples.
Strobe width describes the number of bits enabled by each strobe. All strobed memories are byte enabled in the design.

# References:

[1] The White House, "National Security Memorandum on Promoting United States Leadership in Quantum Computing While Mitigating Risks to Vulnerable Cryptographic Systems," 2022. [Online]. Available: [White House](https://www.whitehouse.gov/briefing-room/statements-releases/2022/05/04/national-security-memorandum-on-promoting-united-states-leadership-in-quantum-computing-while-mitigating-risks-to-vulnerable-cryptographic-systems/).

[2] NIST, "FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard," August 13, 2024.

[3] NIST, "FIPS 204 Module-Lattice-Based Digital Signature Standard," August 13, 2024.

