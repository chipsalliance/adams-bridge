![OCP Logo](./images/OCP_logo.png)

<p style="text-align: center;">Adam's Bridge Hardware Specification</p>

<p style="text-align: center;">Version 1.0</p>

<div style="page-break-after: always"></div>

# Scope

This document defines technical specifications for a Adam's Bridge Post-Quantum Cryptography (PQC ML-DSA) subsystem used in the Open Compute Project (OCP). This document shall comprise the Adam's Bridge technical specification.

# Overview

This document provides definitions and requirements for a Adam's Bridge Post-Quantum Cryptography (PQC ML-DSA) subsystem. The document then relates these definitions to existing technologies, enabling device and platform vendors to better understand those technologies in trusted computing terms.

# Adam's Bridge Core

## API

| Name                   | Input/Output   | Operation     | Size (Byte) | Start Address | End Address   |
|------------------------|----------------|---------------|-------------|---------------|---------------|
| name                   | Output         | All           | 8           | 0x00000000    | 0x00000007    |
| version                | Output         | All           | 8           | 0x00000008    | 0x0000000F    |
| ctrl                   | Input          | All           | 4           | 0x00000010    | 0x00000013    |
| status                 | Output         | All           | 4           | 0x00000018    | 0x0000001B    |
| IV (SCA)               | Input          | All           | 64          | 0x00000080    | 0x000000BF    |
| seed                   | Input          | Keygen        | 32          | 0x00000100    | 0x0000011F    |
| sign_rnd               | Input          | Sign          | 32          | 0x00000180    | 0x0000019F    |
| message                | Input          | Sign/Verify   | 64          | 0x00000200    | 0x0000023F    |
| verification result    | Output         | Verify        | 64          | 0x00000280    | 0x000002BF    |
| sk_out (software only) | Output         | Keygen        | 4864        | 0x00000300    | 0x000015FF    |
| sk_in                  | Input          | Signing       | 4864        | 0x00001600    | 0x000028FF    |
| pk                     | Input/Output   | Keygen/Verify | 2592        | 0x00002900    | 0x0000331F    |
| signature              | Input/Output   | Sign/Verify   | 4596        | 0x00003400    | 0x000045F3    |
| Interrupt              | Output         | All           | 520         | 0x00004600    | 0x00004807    |
|------------------------|----------------|---------------|-------------|---------------|---------------|
| Total                  |                |               | 18440       | 0x00000000    | 0x00004807    |


