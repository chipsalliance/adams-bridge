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
- [Side-Channel Analysis countermeasures](./AdamsBridgeSCA.md)

# Memory requirement

The following table shows the required memory instances for Adam's Bridge:

| Instance            | Depth | Data Width | Strobe Width |
| --------------------| ----- | ---------- | ------------ |
| abr_sk_mem_bank0    | 596   | 32         |              |
| abr_sk_mem_bank1    | 596   | 32         |              |
| abr_w1_mem          | 512   | 4          |              |
| abr_mem_inst0_bank0 | 800   | 96         |              |
| abr_mem_inst0_bank1 | 800   | 96         |              |
| abr_mem_inst1       | 64    | 96         |              |
| abr_mem_inst2       | 1536  | 96         |              |
| abr_sig_z_mem       | 224   | 160        | 20           |
| abr_pk_mem          | 64    | 320        | 40           |

All memories are modeled as 1 read 1 write port RAMs with a flopped read data.
See abr_1r1w_ram.sv and abr_1r1w_be_ram.sv for examples.
Strobe width describes the number of bits enabled by each strobe. All strobed memories are byte enabled in the design.

## Masking-protected memory (MASKING_EN = 1)

When the top-level `MASKING_EN` parameter is set to 1, four additional SRAM instances are generated to hold the second share of all masked operands. These mirror the dimensions of the corresponding regular memory instances:

| Instance                   | Depth | Data Width | Strobe Width |
| -------------------------- | ----- | ---------- | ------------ |
| abr_mem_inst0_bank0_masked | 800   | 96         |              |
| abr_mem_inst0_bank1_masked | 800   | 96         |              |
| abr_mem_inst1_masked       | 64    | 96         |              |
| abr_mem_inst2_masked       | 1536  | 96         |              |

Regular and masked SRAMs together carry the two-share representation of each coefficient: the regular memory holds `share0` (uniform random) and the masked memory holds `share1` where `share0 + share1 = data`. When `MASKING_EN = 0` the masked instances are not instantiated and their interface read data is tied to zero.

# Zeroize

The ZEROIZE bit in the control register clears all internal data-path registers that hold or have held secret-derived values. This prevents residual sensitive data from leaking through side-channel analysis or from being consumed by a subsequent operation.

Firmware must issue zeroize:
- After every completed operation, before starting the next command.
- After any error or aborted operation, before re-issuing a command or reading results.

Hardware behavior:
- Zeroize takes the highest priority after reset.
- The ZEROIZE control-register field is a pulse command: firmware writes a 1; the register auto-clears after one clock cycle. However, the hardware zeroize operation itself takes multiple cycles because on-chip SRAM is scrubbed one address per cycle. Firmware must poll the STATUS register and wait for ready before issuing the next command.
- After zeroize completes, the STATUS register returns to ready, and the engine accepts a new command.

# Area Results

**TODO: Area numbers predate the architectural masking refactor. Re-synth required to refresh stdcell + RAM area.**
- The required area for the protected Adams Bridge (ML-DSA-87 + ML-KEM-1024) is 0.1096mm2 @5nm:
    - 0.0860mm2 for stdcell
    - 0.0236mm2 for ram area.

For per-algorithm performance breakdowns, see the Performance and Area Results sections in [AdamsBridge\_MLDSA.md](AdamsBridge_MLDSA.md) and [AdamsBridge\_MLKEM.md](AdamsBridge_MLKEM.md).

# Technology-Specific Primitive Instantiation

Adams Bridge uses redundant logic to counteract Fault Injection (FI) and Side Channel Analysis (SCA). In particular, the Domain-Oriented Masking (DOM) datapath relies on primitive cells (buffers, enabled flops, XOR gates) whose logic must **not** be optimized, merged, or reordered by synthesis, otherwise the masking guarantees are broken. This logic is built from generic primitive modules that act as placeholders. Integrators must replace these generic primitives with corresponding technology-specific cells from their standard cell library so that the required constraints can be applied directly to the technology cells.

The generic primitives are instantiated only through abstract prim wrappers (`abr_prim_buf`, `abr_prim_flop`, `abr_prim_flop_en`, `abr_prim_xor2`). Each wrapper selects its implementation through the [`abr_prim_module_name_macros.svh`](../src/abr_prim/rtl/abr_prim_module_name_macros.svh) mechanism, so no design or wrapper RTL needs to be edited to retarget a technology.

The following generic primitives require replacement with technology-specific cells. Ensure the instance names for these replacement cells include the `u__size_only__` tag, as shown in the example below.

*   `abr_prim_generic_buf`
*   `abr_prim_generic_flop`
*   `abr_prim_generic_flop_en`
*   `abr_prim_generic_xor2`

To integrate technology-specific replacements, define the `ABR_PRIM_MODULE_PREFIX` macro (for example on the compile command line, `+define+ABR_PRIM_MODULE_PREFIX=<tech>_prim`) and compile the technology-specific RTL in place of the generic implementation under [`src/abr_prim_generic/rtl`](../src/abr_prim_generic/rtl). When `ABR_PRIM_MODULE_PREFIX` is not defined it defaults to `abr_prim_generic`, so the default build resolves to the generic modules and is functionally unchanged. The replacement library must provide `<prefix>_buf`, `<prefix>_flop`, `<prefix>_flop_en`, and `<prefix>_xor2` with the same port lists as the generic modules. For details on how `ABR_PRIM_MODULE_PREFIX` selects between generic and technology-specific modules, see the implementation in [`abr_prim_module_name_macros.svh`](../src/abr_prim/rtl/abr_prim_module_name_macros.svh).

Integrators shall follow this process to ensure that process-specific library cells are used and appropriately named, shall apply `size_only` constraints on the resulting cells tagged with the `u__size_only__` string, and shall review results from synthesis and place-and-route to ensure that these cells are not optimized away.

**Example: Technology-Specific Buffer**

The following example shows how to create a technology-specific wrapper for the `abr_prim_generic_buf` primitive.

```sv
// In this example:
// - `ABR_PRIM_MODULE_PREFIX` is assumed to be `abr_prim_tech_name`.
// - `TECH_DEPENDENT_BUF` is the name of the technology-specific buffer cell.
// - `PORT_NAME_IN` and `PORT_NAME_OUT` are its input and output ports.

module abr_prim_tech_name_buf #(
  parameter int Width = 1
) (
  input  logic [Width-1:0] in_i,
  output logic [Width-1:0] out_o
);

  for (genvar k = 0; k < Width; k++) begin : gen_bufs
    // The instance name "u__size_only__buf" contains the required tag.
    // Synthesis tools must be configured to apply "size_only"
    // constraints to any instance whose name includes "u__size_only__".
    // This naming convention should be used for all replaced primitives.

    TECH_DEPENDENT_BUF u__size_only__buf (
      .<PORT_NAME_IN>(in_i[k]),
      .<PORT_NAME_OUT>(out_o[k])
    );
  end

endmodule : abr_prim_tech_name_buf
```

# References:

[1] The White House, "National Security Memorandum on Promoting United States Leadership in Quantum Computing While Mitigating Risks to Vulnerable Cryptographic Systems," 2022. [Online]. Available: [White House](https://www.whitehouse.gov/briefing-room/statements-releases/2022/05/04/national-security-memorandum-on-promoting-united-states-leadership-in-quantum-computing-while-mitigating-risks-to-vulnerable-cryptographic-systems/).

[2] NIST, "FIPS 203 Module-Lattice-Based Key-Encapsulation Mechanism Standard," August 13, 2024.

[3] NIST, "FIPS 204 Module-Lattice-Based Digital Signature Standard," August 13, 2024.

