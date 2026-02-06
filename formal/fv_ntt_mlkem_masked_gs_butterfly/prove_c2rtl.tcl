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

#Clear GUI windows
clear -all
set_log_timestamp_mode on

# Change working directory to the directory of the script
# Eliminate every symbolic link
set script_path [file dirname [file dirname [file normalize [info script]/___]]]
cd $script_path

check_cov -init -model { branch statement expression toggle functional fsm } -type { stimuli coi proof bound }

# Parameters
set Q 3329                                              ; # Barret reduction n constant
set width 24                                            ; # Shouldn't be greater than c_width
set c_width 32                                          ; # Max width given by c++ model types
set zw [expr {$c_width - $width}]                       ; # Leading zeros up to 64bits for WIDTH values
set zr [expr {$c_width - 14}]                           ; # Leading zeros up to 64bits for rnd values (14 bits)
set imp ntt_mlkem_masked_gs_butterfly_imp               ; # Top module name
set mul $imp.mult_inst_0                                ; # mult_inst_0 instatiation name under imp
set mbr $imp.mult_inst_0.masked_barrett_mult_inst       ; # masked_barret_reduction instatiation name under imp.mult_inst_0

#check_cov -init -model all -type {coi proof}

# Spec loading
set_cfe_compile_extended_math true
check_c2rtl -set_dynamic_pruning -spec
check_c2rtl -compile -spec formal/fv_ntt_mlkem_masked_gs_butterfly/fv_c2rtl_model_ntt_masked_gs_butterfly.cpp

# Imp loading
check_c2rtl -analyze -imp -sv -f ntt_mlkem_masked_gs_butterfly_filelist.f
check_c2rtl -elaborate -imp -top ntt_mlkem_masked_gs_butterfly -disable_auto_bbox
 
check_c2rtl -setup
set_reset_max_iterations 400
clock ntt_mlkem_masked_gs_butterfly_imp.clk
reset -expression ~ntt_mlkem_masked_gs_butterfly_imp.reset_n
 
# Assumptions:
assume -env -name no_zero     [format {!%s.zeroize} $imp]
assume -env -name input_u00      [format {u00_0 + u00_1 < 'd%s} $Q] 
assume -env -name input_v00      [format {v00_0 + v00_1 < 'd%s} $Q]



# Mapping: 24 bits to 32 bits
#                                           leading 0s , $imp  
assume -env -name input_u00_0      [format {u00_0   == {%s'd0, %s.opu_i[0]}}      $zw $imp] -replace_if
assume -env -name input_u00_1      [format {u00_1   == {%s'd0, %s.opu_i[1]}}      $zw $imp] -replace_if
assume -env -name input_v00_0      [format {v00_0   == {%s'd0, %s.opv_i[0]}}      $zw $imp] -replace_if
assume -env -name input_v00_1      [format {v00_1   == {%s'd0, %s.opv_i[1]}}      $zw $imp] -replace_if

assert -name add_res_0 [format {
    ##7 $past(add_res_0[%s-1:0], 7) == %s.add_res[0][%s-1:0] + %s.add_res[1][%s-1:0]
}                       $width          $imp         $width    $imp          $width]
assert -name sub_res_0 [format {
    ##7 $past(sub_res_0[%s-1:0], 7) == %s.sub_res[0][%s-1:0] + %s.sub_res[1][%s-1:0]
}                       $width          $imp         $width    $imp          $width]
assert -name mul_res_0 [format {
    ##2 $past((%s.sub_res[0] * %s.w_reg[0][0] + %s.sub_res[1] * %s.w_reg[0][0] + %s.sub_res[0] * %s.w_reg[0][1] + %s.sub_res[1] * %s.w_reg[0][1]), 2) == %s.mul_res[%s-1:0][0] + %s.mul_res[%s-1:0][1]
}              $imp            $imp             $imp            $imp             $imp             $imp           $imp             $imp                    $mul      $width       $mul       $width]

## Internal assertions from fv_masked_barrett_reduction
assert -name mbr_check_t [format {
    ##1 (%s.t[1] + %s.t[0]) == 13'($past(%s.tmp[0] + %s.tmp[1], 1)/ 2**%s)
}      $mbr      $mbr                  $mbr        $mbr              $width]

assert -name mbr_check_tmp [format {
    37'(%s.tmp[1] + %s.tmp[0]) == 37'(%s'(%s.x[1] + %s.x[0])*(13'd5039))
} $mbr $mbr $width $mbr $mbr]

assert -name mbr_check_carry_x [format {
    %s.carry_x_ext == 25'((25'(%s.x[1] + %s.x[0]) >> %s) << %s)
} $mbr $mbr $mbr $width $width]
assert -name mbr_check_x_reg [format {
    ##1 (%s.x_reg[1] + %s.x_reg[0]) == $past(%s.x[0] + %s.x[1], 1)
}      $mbr          $mbr                  $mbr      $mbr]

#combinational assignment
assert -name mbr_check_qt [format {
    25'(%s.qt[1] + %s.qt[0]) == (13'(%s.t[1] + %s.t[0]) * %s)
}     $mbr       $mbr              $mbr      $mbr         $Q]

#in cycle 2
assert -name mbr_check_c [format {
    ##2 (%s.c[1] + %s.c[0]) == 13'($past(25'(%s.x_reg[1] + %s.x_reg[0]) - (%s.qt[1] + %s.qt[0]), 1))
}      $mbr      $mbr                      $mbr          $mbr            $mbr       $mbr]

#c_reg is 3x2x13 bits, and shifts c (2x13) from 2->1->0. After computing c, it is stored in c_reg[2] in the 3rd cycle, before used in 5th cycle in y_int
assert -name mbr_check_c_reg_CC3 [format {
    ##3 ({%s.c_reg[2][1], %s.c_reg[2][0]}) == $past({%s.c[1], %s.c[0]}, 1)
}       $mbr            $mbr                       $mbr     $mbr]

assert -name mbr_check_c_reg_CC5 [format {
    ##5 ({%s.c_reg[0][1], %s.c_reg[0][0]}) == $past({%s.c[1], %s.c[0]}, 3)
}       $mbr             $mbr                      $mbr     $mbr]

assert -name mbr_check_c_rolled0 [format {
    (%s.c_rolled[0]) == ((%s.c[1] + %s.c[0]) >= 14'd8192) ? (%s.c[0] + (10'd767 - 14'h2000)) : (%s.c[0] + 10'd767)
}  $mbr                 $mbr      $mbr                     $mbr                               $mbr]

assert -name mbr_check_c_rolled1 [format {
    (%s.c_rolled[1]) == ({1'b0, %s.c[1]})
}      $mbr                       $mbr]

assert -name mbr_check_y [format {
    12'(%s.y_int[1] + %s.y_int[0]) ==  12'( ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) >= 13'd%s ) ? ( 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) - 13'd%s ) : 13'(%s.c_reg[0][1] + %s.c_reg[0][0]) )
}     $mbr          $mbr                        $mbr             $mbr                     $Q         $mbr             $mbr                    $Q       $mbr             $mbr]

assert -name mbr_e2e_check_y [format {
    ##6 12'(%s.y[0] + %s.y[1]) == $past(%s'(%s.x[0] + %s.x[1]), 6) %% %s
}         $mbr      $mbr                $width  $mbr      $mbr          $Q]

# Proof Structure
proof_structure -init INIT -copy_all
proof_structure -create partition -from INIT \
    -op_name P -imp_name {NONMBR X T QT C} \
    -copy {{add_res_0 sub_res_0 mul_res_0} {mbr_check_t mbr_check_x_reg mbr_check_tmp} {mbr_check_qt} {mbr_check_c} {mbr_check_c_reg_CC3 mbr_check_c_reg_CC5 mbr_check_c_rolled0 mbr_check_c_rolled1}}


proof_structure -create stopat -from T \
    -op_name qt -imp_name T_QT -add $mbr.t

proof_structure -create stopat -from QT \
    -op_name c -imp_name QT_C -add $mbr.qt
    
proof_structure -create stopat -from C \
    -op_name c_reg -imp_name C_c_reg -add $mbr.c

#proof_structure -create stopat -from CORR \
#    -op_name y -imp_name CORR_y -add $mbr.c_reg

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_t mbr_check_tmp mbr_check_x_reg} {mbr_check_qt} {mbr_check_c} {mbr_check_c_reg_CC3 mbr_check_c_reg_CC5 mbr_check_c_rolled0 mbr_check_c_rolled1} {mbr_check_y} mbr_e2e_check_y] \
    -op_name AG1 

#proof_structure -create assume_guarantee -from INIT \
    -property [list {mbr_check_carry_x mbr_check_correction0 mbr_check_correction1 mbr_check_tmp0 mbr_check_tmp1} mbr_check_tmp] \
    -op_name AG1
# proof_structure -create stopat -from MBR -op_name S1 -imp_name MBR_S1 \
#     -add [subst {$mul.mul_res0 $mul.mul_res1}]

source [get_install_dir]/etc/res//tcl_library/jasper_tcl_library.tcl
#prove -bg -all
::jasper::psu::prove_all_serial_limited INIT 10 "-time_limit 16h"
#check_cov -measure -task {<embedded>} -bg 
#prove -bg -all