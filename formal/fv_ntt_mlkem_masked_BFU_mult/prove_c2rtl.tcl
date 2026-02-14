// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

# Clear GUI windows
clear -all

# Change working directory to the directory of the script
# Eliminate every symbolic link
set script_path [file dirname [file dirname [file normalize [info script]/___]]]
set design_path $script_path/../../../rtl/original/src/
set property_path $script_path/

cd $script_path

# Parameters
set Q 3329                              ; # Barret reduction n constant
set width 24                            ; # Shouldn't be greater than c_width
set c_width 32                          ; # Max width given by c++ model types
set zw [expr {$c_width - $width}]       ; # Leading zeros up to 64bits for WIDTH values
set zr [expr {$c_width - 14}]           ; # Leading zeros up to 64bits for rnd values (14 bits)
set wc [expr {$width + 1}]              ; # Width + carry bit
set top ntt_mlkem_masked_BFU_mult       ; # Top module name
set imp ${top}_imp                      ; # Implementation
set mbr $imp.masked_barrett_mult_inst   ; # masked_barret_reduction instatiation name from top

# Coverage analysis
check_cov -init -exclude_bind_hierarchies -enable_checker_undetectable -include_assign_scoring

# Spec loading
check_c2rtl -set_dynamic_pruning -spec
check_c2rtl -compile -spec $property_path/$top.cpp

# Imp loading
check_c2rtl -analyze -imp -sv -f filelist.f
check_c2rtl -elaborate -imp -top $top\
    -disable_auto_bbox\
    -parameter WIDTH $width
 
check_c2rtl -setup
set_reset_max_iterations 400
clock $imp.clk
reset -expression ~$imp.reset_n
 
# Assumptions
assume -env -name of_u      [format {u0 + u1 < 'd%s} $Q] 
assume -env -name of_v      [format {v0 + v1 < 'd%s} $Q]
assume -env -name no_zero   [format {!%s.zeroize} $imp]

## Mapping to 64 bits (padding with leadding 0s)
#                                            leading 0s, $imp                              
assume -env -name input_u0      [format {u0   == {%s'd0, %s.u[0]}}      $zw $imp] -replace_if
assume -env -name input_u1      [format {u1   == {%s'd0, %s.u[1]}}      $zw $imp] -replace_if
assume -env -name input_v0      [format {v0   == {%s'd0, %s.v[0]}}      $zw $imp] -replace_if
assume -env -name input_v1      [format {v1   == {%s'd0, %s.v[1]}}      $zw $imp] -replace_if
assume -env -name input_rnd0    [format {rnd0 == {%s'd0, %s.rnd[0]}}    $zr $imp] -replace_if
assume -env -name input_rnd1    [format {rnd1 == {%s'd0, %s.rnd[1]}}    $zr $imp] -replace_if
assume -env -name input_rnd2    [format {rnd2 == {%s'd0, %s.rnd[2]}}    $zr $imp] -replace_if
assume -env -name input_rnd3    [format {rnd3 == {%s'd0, %s.rnd[3]}}    $zr $imp] -replace_if
assume -env -name input_rnd3    [format {rnd4 == {%s'd0, %s.rnd[4]}}    $zr $imp] -replace_if
assume -env -name input_rnd_24b [format {rndw == {%s'd0, %s.rnd_24bit}} $zw $imp] -replace_if

## Top level assertions against spec (.cpp model)
# Check multiplication against spec
assert -name spec_mul [format {
    ##2 %s.mul_res0 + %s.mul_res1 == $past(mul_res[%s-1:0], 2)
}     $imp          $imp                       $width]

# Check modulo (reduction) against spec
assert -name spec_reduce [format {
    ##8 %s.res[0] + %s.res[1] == $past(mul_res_reduced[%s-1:0], 8)
}     $imp        $imp                             $width]

## Top level assertions using design signals
# Check reduce using design signals
assert -name imp_reduce [format {
    ##6 %s'(%s.mul_res_reduced[0] + %s.mul_res_reduced[1]) == $past(%s'(%s'(%s.mul_res0 + %s.mul_res1) %% %s), 6)
}   $width $imp                   $imp                         $width $width $imp        $imp              $Q]

## Internmediate assertions from fv_masked_barrett_reduction
# Check computation of t and tmp based on inputs to submodule
assert -name mbr_check_t [format {
    ##1 (%s.t[1] + %s.t[0]) == 13'($past(%s.tmp[0] + %s.tmp[1], 1)/ 2**%s)
}      $mbr      $mbr                  $mbr        $mbr            $width]

assert -name mbr_check_tmp [format {
    37'(%s.tmp[1] + %s.tmp[0]) == 37'(%s'(%s.x[1] + %s.x[0])*(13'd5039))
}       $mbr        $mbr              $width $mbr   $mbr]

assert -name mbr_check_carry_x [format {
    %s.carry_x_ext == 25'((25'(%s.x[1] + %s.x[0]) >> %s) << %s)
}   $mbr $mbr $mbr $width $width]
assert -name mbr_check_x_reg [format {
    ##1 (%s.x_reg[1] + %s.x_reg[0]) == $past(%s.x[0] + %s.x[1], 1)
}      $mbr          $mbr                  $mbr      $mbr]

# Check combinational assignment of qt
assert -name mbr_check_qt [format {
    %s'(%s.qt[1] + %s.qt[0]) == %s'(13'(%s.t[1] + %s.t[0]) * %s)
} $wc $mbr       $mbr          $wc    $mbr      $mbr         $Q]

# Check computation and propagation of c across cycles in c_reg
assert -name mbr_check_c [format {
    ##2 (%s.c[1] + %s.c[0]) == 13'($past(%s'(%s.x_reg[1] + %s.x_reg[0]) - (%s.qt[1] + %s.qt[0]), 1))
}      $mbr      $mbr                  $wc $mbr          $mbr            $mbr       $mbr]

assert -name mbr_check_c_reg_CC3 [format {
    ##3 ({%s.c_reg[2][1], %s.c_reg[2][0]}) == $past({%s.c[1], %s.c[0]}, 1)
}       $mbr            $mbr                       $mbr     $mbr]

assert -name mbr_check_c_reg_CC5 [format {
    ##5 ({%s.c_reg[0][1], %s.c_reg[0][0]}) == $past({%s.c[1], %s.c[0]}, 3)
}       $mbr             $mbr                      $mbr     $mbr]

# Check condition for input of submodule masked_barrett_if_cond_inst to correct y
assert -name mbr_check_c_rolled0 [format {
    (%s.c_rolled[0]) == ((%s.c[1] + %s.c[0]) >= 14'd8192) ? (%s.c[0] + (10'd767 - 14'h2000)) : (%s.c[0] + 10'd767)
}  $mbr                 $mbr      $mbr                     $mbr                               $mbr]

assert -name mbr_check_c_rolled1 [format {
    (%s.c_rolled[1]) == ({1'b0, %s.c[1]})
}  $mbr                       $mbr]

# Check y, based on the previous computations of c_reg
assert -name mbr_check_y [format {
    12'(%s.y_int[1] + %s.y_int[0]) ==  12'( ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) >= 13'd%s ) ? ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) - 13'd%s ) : 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) )
}     $mbr          $mbr                        $mbr             $mbr                     $Q          $mbr             $mbr                $Q       $mbr             $mbr]

# End-to-End check of y
assert -name mbr_e2e_check_y [format {
    ##6 12'(%s.y[0] + %s.y[1]) == $past(%s'(%s.x[0] + %s.x[1]), 6) %% %s
}         $mbr      $mbr           $width $mbr      $mbr              $Q]


## Proof structures
# Divided in 4 partitions: 
# - MUL: multiplication against spec
# - RED: reduce against spec
# - IMP_RED: reduce using design internla signals
# - MBR: intermediate assertions from Masked Barret Reduction
proof_structure -init INIT -copy_all
proof_structure -create partition -from INIT \
    -op_name P -imp_name {MUL RED IMP_RED X T QT C} \
    -copy {{spec_mul} {spec_reduce} {imp_reduce} {mbr_check_t mbr_check_x_reg mbr_check_tmp} {mbr_check_qt} {mbr_check_c} {mbr_check_c_reg_CC3 mbr_check_c_reg_CC5 mbr_check_c_rolled0 mbr_check_c_rolled1}}

# Stopat
proof_structure -create stopat -from T \
    -op_name qt -imp_name T_QT -add $mbr.t

proof_structure -create stopat -from QT \
    -op_name c -imp_name QT_C -add $mbr.qt
    
proof_structure -create stopat -from C \
    -op_name c_reg -imp_name C_c_reg -add $mbr.c
##proof_structure -create stopat -from MBR -op_name S1 -imp_name MBR_S1 \
  ##  -add [subst {$imp.mul_res0 $imp.mul_res1}]
  #proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_t mbr_check_tmp mbr_check_x_reg} {mbr_check_qt} {mbr_check_c} {mbr_check_c_reg_CC3 mbr_check_c_reg_CC5 mbr_check_c_rolled0 mbr_check_c_rolled1} {mbr_check_y} e2e_mbr_check_y] \
    -op_name AG1 

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_carry_x mbr_check_correction0 mbr_check_correction1 mbr_check_tmp0 mbr_check_tmp1} mbr_check_tmp] \
    -op_name AG1 

source [get_install_dir]/etc/res//tcl_library/jasper_tcl_library.tcl
# prove -bg -all
::jasper::psu::prove_all_serial_limited INIT 10 "-time_limit 16h"
