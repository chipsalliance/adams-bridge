// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This file defines macros for generating module names in the abr_prim package.
// It provides the mechanism used to swap the generic prim implementations for
// technology-specific ones without editing the abstract prim wrappers.

`ifndef abr_prim_module_name_macros_SVH
`define abr_prim_module_name_macros_SVH

// Defines the default prefix for abr_prim generic modules.
// This can be overridden by defining ABR_PRIM_MODULE_PREFIX before including
// this file (e.g. on the compile command line). If not defined it defaults to
// 'abr_prim_generic'. The prim generic implementations can be found under
// ${ADAMSBRIDGE_ROOT}/src/abr_prim_generic/rtl
//
// For production use it is recommended to implement the technology-specific
// modules replacing the generic ones and point the compile at that RTL root.
`ifndef ABR_PRIM_MODULE_PREFIX
`define ABR_PRIM_MODULE_PREFIX abr_prim_generic
`endif // ABR_PRIM_MODULE_PREFIX

// Macro to generate the full module name for abr_prim modules.
// Usage: `ABR_PRIM_MODULE_NAME(buf)
// This will result in abr_prim_generic_buf if ABR_PRIM_MODULE_PREFIX is not
// defined.
`define ABR_PRIM_MODULE_NAME_EXPAND(prefix, name) prefix``_``name

`define ABR_PRIM_MODULE_NAME(__name) \
    `ABR_PRIM_MODULE_NAME_EXPAND(`ABR_PRIM_MODULE_PREFIX, __name)

`endif // abr_prim_module_name_macros_SVH
