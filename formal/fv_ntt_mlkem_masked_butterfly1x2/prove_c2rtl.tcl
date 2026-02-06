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

##Clear GUI windows
clear -all

# Change working directory to the directory of the script
# Eliminate every symbolic link
set script_path [file dirname [file dirname [file normalize [info script]/___]]]
cd $script_path

# Parameters
set Q 3329                                              ; # MLKEM Q constant
set width 24                                            ; # Shouldn't be greater than c_width
set c_width 32                                          ; # Max width given by c++ model types
set zw [expr {$c_width - $width}]                       ; # Leading zeros up to 64bits for WIDTH values
set zr [expr {$c_width - 14}]                           ; # Leading zeros up to 64bits for rnd values (14 bits)
set imp ntt_mlkem_masked_butterfly1x2_imp               ; # Top module name
set mgs0 $imp.mlkem_masked_bf_inst00                    ; # masked gs bfu 0 instatiation name under imp
set mgs1 $imp.mlkem_masked_bf_inst01                    ; # masked gs bfu 1 instatiation name under imp
set mul0 $mgs0.mult_inst_0                              ; # mult_inst_0 instatiation name under imp
set mul1 $mgs1.mult_inst_0                              ; # mult_inst_0 instatiation name under imp
set mbr0 $mul0.masked_barrett_mult_inst                 ; # masked_barret_reduction instatiation name under imp.mult_inst_0
set mbr1 $mul1.masked_barrett_mult_inst                 ; # masked_barret_reduction instatiation name under imp.mult_inst_0

# Spec loading
check_c2rtl -set_dynamic_pruning -spec
check_c2rtl -compile -spec formal/fv_ntt_mlkem_masked_butterfly1x2/fv_ntt_mlkem_masked_butterfly1x2.cpp

 # Imp loading
check_c2rtl -analyze -imp -sv -f filelist.f
check_c2rtl -elaborate -imp -top ntt_mlkem_masked_butterfly1x2 -disable_auto_bbox
 
check_c2rtl -setup
set_reset_max_iterations 400
clock ntt_mlkem_masked_butterfly1x2_imp.clk
reset -expression ~ntt_mlkem_masked_butterfly1x2_imp.reset_n
 
# Assumptions:
assume -env -name no_zero [format {!%s.zeroize} $imp]
assume -env -name assume_u00 [format {u00_0 + u00_1 < 'd%s} $Q]
assume -env -name assume_u01 [format {u01_0 + u01_1 < 'd%s} $Q]
assume -env -name assume_w00 [format {w00_0 + w00_1 < 'd%s} $Q]
assume -env -name assume_w01 [format {w01_0 + w01_1 < 'd%s} $Q]
assume -env -name assume_v00 [format {v00_0 + v00_1 < 'd%s} $Q]
assume -env -name assume_v01 [format {v01_0 + v01_1 < 'd%s} $Q]
assume -env -name assume_v10_int [format {v10_int_0 + v10_int_1 < 'd%s} $Q]
assume -env -name assume_v11_int [format {v11_int_0 + v11_int_1 < 'd%s} $Q]
 
# Mapping: 24 bits to 32 bits

assume -env -name input_u00_0 [format {u00_0 == {%s'd0,%s.u00[0]}} $zw $imp] -replace_if
assume -env -name input_u00_1 [format {u00_1 == {%s'd0,%s.u00[1]}} $zw $imp] -replace_if
assume -env -name input_u01_0 [format {u01_0 == {%s'd0,%s.u01[0]}} $zw $imp] -replace_if
assume -env -name input_u01_1 [format {u01_1 == {%s'd0,%s.u01[1]}} $zw $imp] -replace_if
assume -env -name input_w00_0 [format {w00_0 == {%s'd0,%s.w00[0]}} $zw $imp] -replace_if
assume -env -name input_w00_1 [format {w00_1 == {%s'd0,%s.w00[1]}} $zw $imp] -replace_if
assume -env -name input_w01_0 [format {w01_0 == {%s'd0,%s.w01[0]}} $zw $imp] -replace_if
assume -env -name input_w01_1 [format {w01_1 == {%s'd0,%s.w01[1]}} $zw $imp] -replace_if
assume -env -name input_v00_0 [format {v00_0 == {%s'd0,%s.v00[0]}} $zw $imp] -replace_if
assume -env -name input_v00_1 [format {v00_1 == {%s'd0,%s.v00[1]}} $zw $imp] -replace_if
assume -env -name input_v01_0 [format {v01_0 == {%s'd0,%s.v01[0]}} $zw $imp] -replace_if
assume -env -name input_v01_1 [format {v01_1 == {%s'd0,%s.v01[1]}} $zw $imp] -replace_if
assume -env -name input_v10_int_0 [format {v10_int_0 == {%s'd0,%s.v10_int[0]}} $zw $imp] -replace_if
assume -env -name input_v10_int_1 [format {v10_int_1 == {%s'd0,%s.v10_int[1]}} $zw $imp] -replace_if
assume -env -name input_v11_int_0 [format {v11_int_0 == {%s'd0,%s.v11_int[0]}} $zw $imp] -replace_if
assume -env -name input_v11_int_1 [format {v11_int_1 == {%s'd0,%s.v11_int[1]}} $zw $imp] -replace_if

# Assertions for masked gs bfu instantiation 0
assert -name u10_int [format {
    ##15 $past(u10_int[%s-1:0], 15) == %s.u10_int[0][%s-1:0] + %s.u10_int[1][%s-1:0]
}                       $width          $imp         $width    $imp          $width]
assert -name u20_o [format {##16 $past(u10_div2, 16) == %s.uv_o.u20_o}  $imp]
#assert -name v10_int [format {
#    ##15 $past(v10_int[%s-1:0], 15) == %s.v10_int[0][%s-1:0] + %s.v10_int[1][%s-1:0]
#}                       $width          $imp         $width    $imp          $width]
assert -name sub_res_0 [format {
    ##7 $past(sub_res_0[%s-1:0], 7) == %s.sub_res[0][%s-1:0] + %s.sub_res[1][%s-1:0]
}                       $width         $mgs0         $width    $mgs0          $width]
assert -name mul_res_0 [format {
    ##2 $past((%s.sub_res[0] * %s.w_reg[0][0] + %s.sub_res[1] * %s.w_reg[0][0] + %s.sub_res[0] * %s.w_reg[0][1] + %s.sub_res[1] * %s.w_reg[0][1]), 2) == %s.mul_res[%s-1:0][0] + %s.mul_res[%s-1:0][1]
}              $mgs0          $mgs0             $mgs0           $mgs0            $mgs0           $mgs0            $mgs0          $mgs0                   $mul0      $width       $mul0      $width]

## Internal assertions from fv_masked_barrett_reduction
assert -name mbr_check_t_0 [format {
    ##1 (%s.t[1] + %s.t[0]) == 13'($past(%s.tmp[0] + %s.tmp[1], 1)/ 2**%s)
}      $mbr0      $mbr0                  $mbr0        $mbr0           $width]

assert -name mbr_check_tmp_0 [format {
    37'(%s.tmp[1] + %s.tmp[0]) == 37'(%s'(%s.x[1] + %s.x[0])*(13'd5039))
}       $mbr0       $mbr0          $width $mbr0     $mbr0]

assert -name mbr_check_carry_x_0 [format {
    %s.carry_x_ext == 25'((25'(%s.x[1] + %s.x[0]) >> %s) << %s)
} $mbr0                         $mbr0   $mbr0       $width  $width]

assert -name mbr_check_x_reg_0 [format {
    ##1 (%s.x_reg[1] + %s.x_reg[0]) == $past(%s.x[0] + %s.x[1], 1)
}      $mbr0          $mbr0                  $mbr0      $mbr0]

#combinational assignment
assert -name mbr_check_qt_0 [format {
    25'(%s.qt[1] + %s.qt[0]) == (13'(%s.t[1] + %s.t[0]) * %s)
}     $mbr0       $mbr0              $mbr0      $mbr0         $Q]

#in cycle 2
assert -name mbr_check_c_0 [format {
    ##2 (%s.c[1] + %s.c[0]) == 13'($past(25'(%s.x_reg[1] + %s.x_reg[0]) - (%s.qt[1] + %s.qt[0]), 1))
}      $mbr0      $mbr0                      $mbr0          $mbr0            $mbr0       $mbr0]

#c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle, before used in 5th cycle in y_int
assert -name mbr_check_c_reg_CC3_0 [format {
    ##3 ({%s.c_reg[2][1], %s.c_reg[2][0]}) == $past({%s.c[1], %s.c[0]}, 1)
}       $mbr0            $mbr0                       $mbr0     $mbr0]

assert -name mbr_check_c_reg_CC5_0 [format {
    ##5 ({%s.c_reg[0][1], %s.c_reg[0][0]}) == $past({%s.c[1], %s.c[0]}, 3)
}       $mbr0             $mbr0                      $mbr0     $mbr0]

assert -name mbr_check_c_rolled0_0 [format {
    (%s.c_rolled[0]) == ((%s.c[1] + %s.c[0]) >= 14'd8192) ? (%s.c[0] + (10'd767 - 14'h2000)) : (%s.c[0] + 10'd767)
}  $mbr0                 $mbr0      $mbr0                     $mbr0                               $mbr0]

assert -name mbr_check_c_rolled1_0 [format {
    (%s.c_rolled[1]) == ({1'b0, %s.c[1]})
}      $mbr0                       $mbr0]

assert -name mbr_check_y_0 [format {
    12'(%s.y_int[1] + %s.y_int[0]) ==  12'( ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) >= 13'd%s ) ? ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) - 13'd%s ) : 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) )
}     $mbr0          $mbr0                        $mbr0             $mbr0                     $Q         $mbr0             $mbr0                    $Q       $mbr0             $mbr0]

assert -name mbr_e2e_check_y_0 [format {
    ##6 12'(%s.y[0] + %s.y[1]) == $past(%s'(%s.x[0] + %s.x[1]), 6) %% %s
}         $mbr0      $mbr0         $width         $mbr0      $mbr0              $Q]

assert -name u21_o [format {##1 $past(v10_div2, 1) == %s.uv_o.u21_o}  $imp]

# Assertions for masked gs bfu instantiation 1
assert -name u11_int [format {
    ##15 $past(u11_int[%s-1:0], 15) == %s.u11_int[0][%s-1:0] + %s.u11_int[1][%s-1:0]
}                       $width          $imp         $width    $imp          $width]
assert -name v20_o [format {##16 $past(u11_div2, 16) == %s.uv_o.v20_o}  $imp]
#assert -name v10_int [format {
#    ##15 $past(v10_int[%s-1:0], 15) == %s.v10_int[0][%s-1:0] + %s.v10_int[1][%s-1:0]
#}                       $width          $imp         $width    $imp          $width]
assert -name sub_res_1 [format {
    ##7 $past(sub_res_1[%s-1:0], 7) == %s.sub_res[0][%s-1:0] + %s.sub_res[1][%s-1:0]
}                       $width         $mgs1         $width    $mgs1          $width]
assert -name mul_res_1 [format {
    ##2 $past((%s.sub_res[0] * %s.w_reg[0][0] + %s.sub_res[1] * %s.w_reg[0][0] + %s.sub_res[0] * %s.w_reg[0][1] + %s.sub_res[1] * %s.w_reg[0][1]), 2) == %s.mul_res[%s-1:0][0] + %s.mul_res[%s-1:0][1]
}              $mgs1          $mgs1             $mgs1           $mgs1            $mgs1           $mgs1            $mgs1          $mgs1                   $mul1      $width       $mul1      $width]

## Internal assertions from fv_masked_barrett_reduction
assert -name mbr_check_t_1 [format {
    ##1 (%s.t[1] + %s.t[0]) == 13'($past(%s.tmp[0] + %s.tmp[1], 1)/ 2**%s)
}      $mbr1      $mbr1                  $mbr1        $mbr1           $width]

assert -name mbr_check_tmp_1 [format {
    37'(%s.tmp[1] + %s.tmp[0]) == 37'(%s'(%s.x[1] + %s.x[0])*(13'd5039))
}       $mbr1       $mbr1          $width $mbr1     $mbr1]

assert -name mbr_check_carry_x_1 [format {
    %s.carry_x_ext == 25'((25'(%s.x[1] + %s.x[0]) >> %s) << %s)
} $mbr1                         $mbr1   $mbr1       $width  $width]

assert -name mbr_check_x_reg_1 [format {
    ##1 (%s.x_reg[1] + %s.x_reg[0]) == $past(%s.x[0] + %s.x[1], 1)
}      $mbr1          $mbr1                  $mbr1      $mbr1]

#combinational assignment
assert -name mbr_check_qt_1 [format {
    25'(%s.qt[1] + %s.qt[0]) == (13'(%s.t[1] + %s.t[0]) * %s)
}     $mbr1       $mbr1              $mbr1      $mbr1         $Q]

#in cycle 2
assert -name mbr_check_c_1 [format {
    ##2 (%s.c[1] + %s.c[0]) == 13'($past(25'(%s.x_reg[1] + %s.x_reg[0]) - (%s.qt[1] + %s.qt[0]), 1))
}      $mbr1      $mbr1                      $mbr1          $mbr1            $mbr1       $mbr1]

#c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle, before used in 5th cycle in y_int
assert -name mbr_check_c_reg_CC3_1 [format {
    ##3 ({%s.c_reg[2][1], %s.c_reg[2][0]}) == $past({%s.c[1], %s.c[0]}, 1)
}       $mbr1            $mbr1                       $mbr1     $mbr1]

assert -name mbr_check_c_reg_CC5_1 [format {
    ##5 ({%s.c_reg[0][1], %s.c_reg[0][0]}) == $past({%s.c[1], %s.c[0]}, 3)
}       $mbr1             $mbr1                      $mbr1     $mbr1]

assert -name mbr_check_c_rolled0_1 [format {
    (%s.c_rolled[0]) == ((%s.c[1] + %s.c[0]) >= 14'd8192) ? (%s.c[0] + (10'd767 - 14'h2000)) : (%s.c[0] + 10'd767)
}  $mbr1                 $mbr1      $mbr1                     $mbr1                               $mbr1]

assert -name mbr_check_c_rolled1_1 [format {
    (%s.c_rolled[1]) == ({1'b0, %s.c[1]})
}      $mbr1                       $mbr1]

assert -name mbr_check_y_1 [format {
    12'(%s.y_int[1] + %s.y_int[0]) ==  12'( ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) >= 13'd%s ) ? ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) - 13'd%s ) : 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) )
}     $mbr1          $mbr1                        $mbr1             $mbr1                     $Q         $mbr1             $mbr1                    $Q       $mbr1             $mbr1]

assert -name mbr_e2e_check_y_1 [format {
    ##6 12'(%s.y[0] + %s.y[1]) == $past(%s'(%s.x[0] + %s.x[1]), 6) %% %s
}         $mbr1      $mbr1        $width          $mbr1      $mbr1              $Q]

assert -name v21_o [format {##1 $past(v11_div2, 1) == %s.uv_o.v21_o}  $imp]

# Proof structures
proof_structure -init INIT -copy_all
proof_structure -create partition -from INIT \
    -op_name P -imp_name {NONMBR X0 T0 QT0 C0 X1 T1 QT1 C1} \
    -copy {{sub_res_0 mul_res_0 u10_int u20_o u21_o sub_res_1 mul_res_1 u11_int v20_o v21_o} 
    {mbr_check_t_0 mbr_check_x_reg_0 mbr_check_tmp_0} {mbr_check_qt_0} {mbr_check_c_0} {mbr_check_c_reg_CC3_0 mbr_check_c_reg_CC5_0 mbr_check_c_rolled0_0 mbr_check_c_rolled1_0}
    {mbr_check_t_1 mbr_check_x_reg_1 mbr_check_tmp_1} {mbr_check_qt_1} {mbr_check_c_1} {mbr_check_c_reg_CC3_1 mbr_check_c_reg_CC5_1 mbr_check_c_rolled0_1 mbr_check_c_rolled1_1}}

# Stopat
# proof_structure -create stopat -from MBR0 -op_name S0 -imp_name MBR_S0 \
#     -add [subst {$mul0.mul_res}]

# proof_structure -create stopat -from MBR1 -op_name S1 -imp_name MBR_S1 \
#     -add [subst {$mul1.mul_res}]
proof_structure -create stopat -from T0 \
    -op_name qt0 -imp_name T_QT0 -add $mbr0.t

proof_structure -create stopat -from QT0 \
    -op_name c0 -imp_name QT_C0 -add $mbr0.qt
    
proof_structure -create stopat -from C0 \
    -op_name c_reg0 -imp_name C_c_reg0 -add $mbr0.c

#proof_structure -create stopat -from CORR \
#    -op_name y -imp_name CORR_y -add $imp.c_reg

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_t_0 mbr_check_x_reg_0 mbr_check_tmp_0} {mbr_check_qt_0} {mbr_check_c_0} {mbr_check_c_reg_CC3_0 mbr_check_c_reg_CC5_0 mbr_check_c_rolled0_0 mbr_check_c_rolled1_0} {mbr_check_y_0} mbr_e2e_check_y_0] \
    -op_name AG0 

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_carry_x_0 mbr_check_correction0_0 mbr_check_correction1_0 mbr_check_tmp0_0 mbr_check_tmp1_0} mbr_check_tmp_0] \
    -op_name AG0

proof_structure -create stopat -from T1 \
    -op_name qt1 -imp_name T_QT1 -add $mbr1.t

proof_structure -create stopat -from QT1 \
    -op_name c1 -imp_name QT_C1 -add $mbr1.qt
    
proof_structure -create stopat -from C1 \
    -op_name c_reg1 -imp_name C_c_reg1 -add $mbr1.c

#proof_structure -create stopat -from CORR \
#    -op_name y -imp_name CORR_y -add $imp.c_reg

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_t_1 mbr_check_x_reg_1 mbr_check_tmp_1} {mbr_check_qt_1} {mbr_check_c_1} {mbr_check_c_reg_CC3_1 mbr_check_c_reg_CC5_1 mbr_check_c_rolled0_1 mbr_check_c_rolled1_1} {mbr_check_y_1} mbr_e2e_check_y_1] \
    -op_name AG1 

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_carry_x_1 mbr_check_correction0_1 mbr_check_correction1_1 mbr_check_tmp0_1 mbr_check_tmp1_1} mbr_check_tmp_1] \
    -op_name AG1


source [get_install_dir]/etc/res//tcl_library/jasper_tcl_library.tcl
#prove -bg -all
::jasper::psu::prove_all_serial_limited INIT 10 "-time_limit 16h"