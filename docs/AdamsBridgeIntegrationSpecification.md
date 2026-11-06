# Adams Bridge Integration Specification

# Scope

This document describes what SoC/ASIC integrators need to do to bring Adams
Bridge into a build or synthesis flow, including the required environment
variables and the process for replacing Adams Bridge's generic
Side-Channel-Analysis (SCA) / Fault-Injection (FI) countermeasure primitives
with technology-specific standard cells. For the rationale behind these
countermeasures (what they protect against and why the underlying logic must
not be optimized away), see
[AdamsBridgeHardwareSpecification.md](AdamsBridgeHardwareSpecification.md)
and [AdamsBridgeSCA.md](AdamsBridgeSCA.md).

# Environment Variables

| **Variable** | **Description** |
| :--------- | :--------- |
| `CALIPTRA_WORKSPACE` | Absolute path to the directory containing a `chipsalliance` subdirectory, which in turn contains the project repository root. |
| `ADAMSBRIDGE_ROOT` | Absolute path to the Adams Bridge repository root. Recommended: `${CALIPTRA_WORKSPACE}/chipsalliance/caliptra-rtl/submodules/adams-bridge` when integrated with Caliptra, or the standalone `adams-bridge` checkout root otherwise. |
| `ABR_PRIM_ROOT` | The integrator needs to set this environment variable to the path to technology-specific Adams Bridge primitive wrappers for synthesis. Set to `${ADAMSBRIDGE_ROOT}/src/abr_prim_generic` for the generic implementation (the `.vf` file lists do not provide a default). Not used when Adams Bridge is integrated with Caliptra -- see [Integration with Caliptra](#integration-with-caliptra-shared-technology-cells) below. |
| `ABR_PRIM_MODULE_PREFIX` | The integrator needs to set this environment variable to specify the module name prefix for technology-specific Adams Bridge modules for synthesis. Set to `abr_prim_generic` for the generic implementation. The environment variable only selects the primitive file names in the `.vf` file lists; the RTL module names are selected by the SystemVerilog macro of the same name (see [Standalone Technology Swap](#standalone-technology-swap)). Not used when Adams Bridge is integrated with Caliptra -- see [Integration with Caliptra](#integration-with-caliptra-shared-technology-cells) below. |

# Top-Level Parameters

| **Parameter** | **Default** | **Description** |
| :--------- | :--------- | :--------- |
| `MASKING_EN` | 1 | Enables architectural arithmetic masking. When 1, coefficients are stored as two shares and four additional `_masked` SRAM instances are required. When 0, the masked SRAM instances are not used and their read data is tied to zero. |
| `SHA3_MASKING_EN` | 1 | Enables the two-share, DOM-based masked Keccak. |
| `SRAM_LATENCY` | 1 | SRAM read latency in clock cycles. The UVM testbench exercises values 1 and 2. |

All SRAMs are external to `abr_top` and connected through the `abr_mem_if` memory export interface. See [Memory requirement](AdamsBridgeHardwareSpecification.md#memory-requirement) in the Hardware Specification for the required instances, including the `_masked` instances needed when `MASKING_EN = 1`. [`abr_mem_top.sv`](../src/abr_top/rtl/abr_mem_top.sv) is a reference memory wrapper.

# Technology-Specific Primitive Instantiation

Adams Bridge uses redundant logic to counteract Fault Injection (FI) and Side Channel Analysis (SCA). In particular, the Domain-Oriented Masking (DOM) datapath relies on primitive cells (buffers, enabled flops, XOR gates) whose logic must **not** be optimized, merged, or reordered by synthesis, otherwise the masking guarantees are broken. This logic is built from generic primitive modules that act as placeholders. Integrators must replace these generic primitives with corresponding technology-specific cells from their standard cell library so that the required constraints can be applied directly to the technology cells.

The generic primitives are instantiated only through abstract prim wrappers (`abr_prim_buf`, `abr_prim_flop`, `abr_prim_flop_en`, `abr_prim_xor2`). Each wrapper selects its implementation through the [`abr_prim_module_name_macros.svh`](../src/abr_prim/rtl/abr_prim_module_name_macros.svh) mechanism, so no design or wrapper RTL needs to be edited to retarget a technology.

The following generic primitives require replacement with technology-specific cells. Ensure the instance names for these replacement cells include the `u__size_only__` tag, as shown in the examples below.

*   `abr_prim_generic_buf`
*   `abr_prim_generic_flop`
*   `abr_prim_generic_flop_en`
*   `abr_prim_generic_xor2`

Integrators shall follow this process to ensure that process-specific library cells are used and appropriately named, shall apply `size_only` constraints on the resulting cells tagged with the `u__size_only__` string, and shall review results from synthesis and place-and-route to ensure that these cells are not optimized away.

## Standalone Technology Swap

To integrate technology-specific replacements for a standalone Adams Bridge build (not integrated with Caliptra), set the `ABR_PRIM_MODULE_PREFIX` and `ABR_PRIM_ROOT` environment variables, pass the same prefix to the compile as a macro (`+define+ABR_PRIM_MODULE_PREFIX=<prefix>`), and provide the technology-specific RTL -- named `<prefix>_buf`, `<prefix>_flop`, `<prefix>_flop_en`, and `<prefix>_xor2` -- under `${ABR_PRIM_ROOT}/rtl`, in place of the generic implementation under [`src/abr_prim_generic/rtl`](../src/abr_prim_generic/rtl). The environment variables select which files the `.vf` file lists compile; the macro selects which modules the abstract prim wrappers instantiate, so both must agree. When the macro is not defined it defaults to `abr_prim_generic`, so a build with `ABR_PRIM_MODULE_PREFIX=abr_prim_generic` and `ABR_PRIM_ROOT=${ADAMSBRIDGE_ROOT}/src/abr_prim_generic` resolves to the generic modules.

## Integration with Caliptra (Shared Technology Cells)

When Adams Bridge is compiled as part of Caliptra (i.e. the `` `CALIPTRA `` macro is defined -- the same build-mode flag `abr_ctrl.sv`/`abr_top.sv` already check for their keyvault wiring) and the `` `ABR_PRIM_MODULE_PREFIX `` macro is not defined, `abr_prim_module_name_macros.svh` automatically resolves `` `ABR_PRIM_MODULE_NAME `` using Caliptra's own `CALIPTRA_PRIM_MODULE_PREFIX`/`CALIPTRA_PRIM_ROOT` instead of Adams Bridge's own variables. This means:

*   An integrator who has already built technology-specific `caliptra_prim_*_buf`/`flop`/`flop_en`/`xor2` cells for Caliptra does **not** need to build a second, separate set for Adams Bridge -- the same files, under the same `CALIPTRA_PRIM_ROOT`, satisfy both libraries.
*   The `ABR_PRIM_ROOT`/`ABR_PRIM_MODULE_PREFIX` environment variables are not consulted in this mode. Explicitly defining the `` `ABR_PRIM_MODULE_PREFIX `` macro overrides the Caliptra delegation and selects `<prefix>_*` modules instead.
*   Caliptra's generated file lists route Adams Bridge's primitives through the same `CALIPTRA_PRIM_ROOT`-rooted technology-cell files as Caliptra's own -- so for the four shared primitives, both libraries end up referencing the exact same file, and no separate Adams Bridge-specific primitive files are needed.

This resolution relies on `config_defines.svh` (which defines `` `CALIPTRA ``) having already been compiled ahead of Adams Bridge's own files, and on `caliptra_prim_module_name_macros.svh` being available on the include path (it is `` `include ``d by `abr_prim_module_name_macros.svh`). Both are already satisfied by Caliptra's standard compile order and include directories.

## Reset Port Naming

Adams Bridge's abstract prim wrappers (`abr_prim_flop`, `abr_prim_flop_en`) keep their own external reset port named `rst_b`, matching Adams Bridge's native convention used throughout the rest of the design -- this is unaffected by any of the above and requires no integrator action.

Internally, however, both wrappers connect to whichever module `` `ABR_PRIM_MODULE_NAME `` resolves to using the reset port name `rst_ni`, matching Caliptra's own established convention for its swappable primitives. This applies uniformly whether that module is Adams Bridge's own generic (`abr_prim_generic_flop(_en)`), a standalone technology-specific replacement (under `ABR_PRIM_MODULE_PREFIX`), or a shared Caliptra technology cell (under `CALIPTRA_PRIM_MODULE_PREFIX`) -- there is exactly one reset port name to implement, regardless of build mode.

**Any `<prefix>_flop` / `<prefix>_flop_en` technology-specific replacement must therefore expose its reset port as `rst_ni` (active-low), not `rst_b`.**

## Example: Technology-Specific Buffer

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

## Example: Technology-Specific Flop

The following example shows how to create a technology-specific wrapper for the `abr_prim_generic_flop` primitive, illustrating the `rst_ni` reset port requirement described above. Real standard-cell flops typically only reset to a fixed value (0 or 1 per cell variant), not an arbitrary per-bit `ResetValue`; a complete implementation must select the matching set/reset cell variant per bit based on `ResetValue` -- that selection is omitted below for brevity. See [`abr_prim_generic_flop.sv`](../src/abr_prim_generic/rtl/abr_prim_generic_flop.sv) for the full behavioral reference this must match.

```sv
// In this example:
// - `ABR_PRIM_MODULE_PREFIX` is assumed to be `abr_prim_tech_name`.
// - `TECH_DEPENDENT_FLOP` is the name of the technology-specific flop cell.
// - Port names shown are illustrative of the technology cell's own interface.
// - ResetValue handling is omitted here for brevity (see prose above).
module abr_prim_tech_name_flop #(
  parameter int               Width      = 1,
  parameter logic [Width-1:0] ResetValue = 0
) (
  input                    clk_i,
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  for (genvar k = 0; k < Width; k++) begin : gen_flops
    // The instance name "u__size_only__flop" contains the required tag.
    TECH_DEPENDENT_FLOP u__size_only__flop (
      .CLK(clk_i),
      .RSTB(rst_ni),
      .D(d_i[k]),
      .Q(q_o[k])
    );
  end

endmodule : abr_prim_tech_name_flop
```
