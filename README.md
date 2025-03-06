_*SPDX-License-Identifier: Apache-2.0<BR>
<BR>
<BR>
Licensed under the Apache License, Version 2.0 (the "License");<BR>
you may not use this file except in compliance with the License.<BR>
You may obtain a copy of the License at<BR>
<BR>
http://www.apache.org/licenses/LICENSE-2.0 <BR>
<BR>
Unless required by applicable law or agreed to in writing, software<BR>
distributed under the License is distributed on an "AS IS" BASIS,<BR>
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.<BR>
See the License for the specific language governing permissions and<BR>
limitations under the License.*_<BR>

# **Adam's Bridge Hands-On Guide** #
## **Post-Quantum Cryptography IP Core**
_*Last Update: 2025/03/05*_

## **Release Consumption and Integration** ##
Prior official releases are available at: https://github.com/chipsalliance/adams-bridge/releases<br>
Releases are published as a tag, and also contain downloadable assets (which should not be used).
Instead of downloading the assets attached to the published release, integrators should consume AdamsBridge releases by pulling code from the repository at the associated tag, due to https://github.com/chipsalliance/caliptra-rtl/issues/471.

## **Tools Used** ##

OS:
 - Build instructions assume a Linux environment

Lint:
 - Synopsys Spyglass
   - `Version S-2021.09-1`
 - Real Intent AscentLint
   - `Version 2019.A.p15 for RHEL 6.0-64, Rev 116515, Built On 12/18/2020`

Simulation:
 - Synopsys VCS with Verdi
   - `Version R-2020.12-SP2-7_Full64`
 - Verilator
   - `Version 5.012`
 - Mentor Graphics QVIP
   - `Version 2021.2.1` of AHB models
 - UVM installation
   - `Version 1.1d`
 - Mentor Graphics UVM-Frameworks
   - `2022.3`

Synthesis:
 - Synopsys Fusion Compiler
   - `Version 2022.12-SP3`

GCC:
 - RISCV Toolchain for generating memory initialization files
   - `Version 2023.04.29`
   - `riscv64-unknown-elf-gcc (g) 12.2.0`
 - G++ Used to compile Verilator objects and test firmware
   - `g++ (GCC) 11.2.0`

CDC:
 - Questa CDC
   - `2023.3 5624840 linux_x86_64 19-Jul-2023`
  
RDC:
 - Real Intent Meridian
   - `2019.A.P16`

RDL Compiler:
 - systemrdl-compiler==1.27.3
 - peakrdl-systemrdl==0.3.0
 - peakrdl-regblock==0.21.0
 - peakrdl-uvm==2.3.0
 - peakrdl-ipxact==3.4.3
 - peakrdl-html==2.10.1
 - peakrdl-cheader==1.0.0
 - peakrdl==1.1.0

Other:
 - Playbook (Microsoft Internal workflow management tool)

## **ENVIRONMENT VARIABLES** ##
Required for simulation:<BR>
`CALIPTRA_WORKSPACE`: Defines the absolute path to the directory where the Verilator "scratch" output directory will be created. Recommended to define as the absolute path to the directory that contains a subdirectory "chipsalliance" which, in turn, contains the Project repository root (called "adams-bridge"")<BR>
`ADAMSBRIDGE_ROOT`: Defines the absolute path to the Project repository root (called "adams-bridge"). Recommended to define as `${CALIPTRA_WORKSPACE}/chipsalliance/caliptra-rtl/submodules/adams-bridge`.<BR>


## **Repository Overview** ##
```
adams-bridge
|-- LICENSE
|-- README.md
|-- Release_Notes.md
|-- SECURITY.md
|-- docs
|   |-- AdamsBridgeHardwareSpecification.md
|   |-- Side-Channel Countermeasures for Adam’s Bridge Accelerator.docx
|   `-- images
|-- src
|   |-- abr_libs
|   |-- abr_prim
|   |-- abr_prim_generic
|   |-- abr_sha3
|   |-- decompose
|   |-- embedded_top
|   |-- exp_mask
|   |-- makehint
|   |-- mldsa_sampler_top
|   |-- mldsa_top
|   |-- norm_check
|   |-- ntt_top
|   |-- pk_decode
|   |-- power2round
|   |-- rej_bounded
|   |-- rej_sampler
|   |-- sample_in_ball
|   |-- sig_decode_z
|   |-- sig_encode_z
|   |-- sigdecode_h
|   |-- sk_decode
|   `-- sk_encode
`-- tools
    |-- README
    |-- scripts
    `-- templates
```
The root of the repository is structured as shown above, to a depth of 2 layers.<BR>
Each sub-component is accompanied by a file list summary (located in src/<component>/config/<name>.vf) that comprises all the filenames required to compile the component, and an optional testbench filelist for unit-level simulation. <BR>
VF files provide absolute filepaths (prefixed by the `ADAMSBRIDGE_ROOT` environment variable) to each compile target for the associated component.<BR>
The "mldsa_top" sub-component contains the top-level fileset for AdamsBridge. `src/mldsa_top/config/compile.yml` defines the required filesets and sub-component dependencies for this build target. All of the files/dependencies are explicitly listed in `src/mldsa_top/config/mldsa_top_tb.vf`. Users may compile the entire design using only this VF filelist.<BR>


## **Verilog File Lists** ##
Verilog file lists are generated via VCS and included in the config directory for each unit. New files added to the design must be included in the vf list. They can be included manually or by using VCS to regenerate the vf file. File lists define the compilation sources (including all dependencies) required to build and simulate a given module or testbench, and should be used by integrators for simulation, lint, and synthesis.

## **Scripts Description** ##

`reg_gen.py`: Used to compile/export RDL files to register source code<BR>
`reg_gen.sh`: Wrapper used to call `reg_gen.py` for all IP cores in AdamsBridge<BR>
`rdl_post_process.py`: Post-processing functionality to make RDL generated SystemVerilog files compatible with lint/Verilator requirements<BR>

## **Simulation Flow ** ##

Follow Caliptra simulation flow as described [here](https://github.com/chipsalliance/caliptra-rtl/tree/main?tab=readme-ov-file#simulation-flow)

### Unit Test VCS Steps: ###
1. Setup tools, add to PATH
1. Define all environment variables above
1. Create a run folder for build outputs (and cd to it)
1. Compile complete project using `src/<block>/config/<name>_tb.vf` as a compilation target in VCS. When running the `vcs` command to generate simv, users should ensure that `<name>_tb` is explicitly specified as the top-level component in their command to ensure this is the sole "top" that gets simulated.
1. Copy the test generator scripts or test vectors to the run output directory
1. Simulate project with `<name>_tb` as the top target

### UVM Unit Test Steps: <BR>

**Description**:<BR>
The UVM Framework generation tool was used to create the baseline UVM testbench for verification of each IP component inside AdamsBridge. The following IP blocks have supported UVM testbenches:
- [MLDSA87](src/mldsa_top/uvmf)

**Prerequisites**:<BR>
- QVIP 2021.2.1 for Mentor Graphics (provides the AHB VIP)
- UVM 1.1d installation
- Mentor Graphics UVM-Framework installation

**Steps:**<BR>
1. Compile UVM 1.1d library
1. Compile the AHB QVIP source
1. Compile the Mentor Graphics UVM-Frameworks base library
1. Compile the UVMF wrapper for AHB in src/abr_libs/uvmf
1. Compile the `verification_ip` provided for the target testbench
1. ALL compilation steps may be completed by using the file-list found at `src/<block>/uvmf_<name>/config/<name>.vf`
1. NOTE: `adams-bridge/src/<block>/uvmf_<name>/uvmf_template_output/project_benches/<block>/tb/testbench/hdl_top.sv` is the top-level TB wrapper for the system
1. Copy the test generator scripts to the run output directory:
    - [src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5](src/mldsa_top/uvmf/Dilithium_ref/dilithium/ref/test/test_dilithium5)
        * Necessary for MLDSA87 unittest
1. Select a test to run from the set of tests in `adams-bridge/src/mldsa_top/uvmf_<name>/uvmf_template_output/project_benches/<block>/tb/tests/src`
1. Provide `+UVM_TESTNAME=<test>` argument to simulation


## **Regression Tests** ##

Follow Caliptra Regression tests as described [here](https://github.com/chipsalliance/caliptra-rtl/blob/main/README.md#regression-tests)

## **NOTES** ##

* The internal registers are auto rendered at the [GitHub page](https://chipsalliance.github.io/caliptra-rtl/main/internal-regs/?p=clp.mldsa_reg)

* Important: The rendered documentation is based on the submodule version of Adams Bridge at [caliptra-rtl repo](https://github.com/chipsalliance/caliptra-rtl/tree/main/submodules), NOT the tip of the Adams Bridge main branch. Changes in the main branch may not be reflected in the documentation until the submodule is updated.