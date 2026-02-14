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

clear -all
set_log_timestamp_mode on
set_cfe_compile_extended_math true

set script_path [file dirname [file dirname [file normalize [info script]/___]]]
cd $script_path

# Parameters
set Q 3329                               ; # Barret reduction n constant
set Q_width [expr {ceil(log($Q)/log(2))}]; #Bit width of Q
set width 24                             ; # Register widths
set c_width 32                           ; # Max width given by c++ model types
set zw [expr {$c_width - $width}]        ; # Leading zeros up to 32bits for WIDTH values
set imp ntt_karatsuba_pairwm_imp         ; # Top module name


check_cov -init -model { branch statement expression toggle functional fsm } -type { stimuli coi proof bound }

check_c2rtl -set_dynamic_pruning -spec
check_c2rtl -compile -spec formal/fv_ntt_karatsuba_pairwm.cpp
 
check_c2rtl -analyze -imp -sv -f filelist.f
check_c2rtl -elaborate -imp -top ntt_karatsuba_pairwm -disable_auto_bbox
 
check_c2rtl -setup
set_reset_max_iterations 400
clock $imp.clk
reset -expression ~$imp.reset_n
 
# Assumptions:
assume -env -name assume_stable_accumulate [format {$stable(%s.accumulate)} $imp]
assume -env -name assume_u_range [subst {($imp.pwo_uvw_i.u0_i < 'd$Q) && ($imp.pwo_uvw_i.u1_i < 'd$Q)}]
assume -env -name assume_v_range [subst {($imp.pwo_uvw_i.v0_i < 'd$Q) && ($imp.pwo_uvw_i.v1_i < 'd$Q)}]
assume -env -name assume_w_range [subst {($imp.pwo_uvw_i.w0_i < 'd$Q) && ($imp.pwo_uvw_i.w1_i < 'd$Q)}]
assume -env -name assume_zeta_range [subst {$imp.pwo_z_i < 'd$Q}]
assume -env -name assume_no_zeroize [subst {!$imp.zeroize}]

# Mapping: 
assume -env -name input_u0 [format {u0 == {%s'd0,%s.pwo_uvw_i.u0_i}} $zw $imp] -replace_if
assume -env -name input_u1 [format {u1 == {%s'd0,%s.pwo_uvw_i.u1_i}} $zw $imp] -replace_if
assume -env -name input_v0 [format {v0 == {%s'd0,%s.pwo_uvw_i.v0_i}} $zw $imp] -replace_if
assume -env -name input_v1 [format {v1 == {%s'd0,%s.pwo_uvw_i.v1_i}} $zw $imp] -replace_if
assume -env -name input_w0 [format {w0 == {%s'd0,%s.pwo_uvw_i.w0_i}} $zw $imp] -replace_if
assume -env -name input_w1 [format {w1 == {%s'd0,%s.pwo_uvw_i.w1_i}} $zw $imp] -replace_if
assume -env -name input_z [format {z == {%s'd0,%s.pwo_z_i}} $zw $imp] -replace_if

#Assertions

#STG1
#Modular multiplication for u0*v0
assert -name assert_uv00 [subst {
$imp.uv00_reduced == $Q_width'(($imp.pwo_uvw_i.u0_i * $imp.pwo_uvw_i.v0_i) % 'd$Q)
}]
#Modular multiplication for u1*v1
assert -name assert_uv11 [subst {
$imp.uv11_reduced == $Q_width'(($imp.pwo_uvw_i.u1_i * $imp.pwo_uvw_i.v1_i) % 'd$Q)
}]
#Modular addition of u0+u1
assert -name assert_u0_plus_u1 [format {
##1 %s.add_res_u == $past(%s'((%s.pwo_uvw_i.u0_i + %s.pwo_uvw_i.u1_i) %% 'd%s), 1)
}   $imp                  $Q_width  $imp           $imp                   $Q]
#Modular multiplication of v0+v1
assert -name assert_v0_plus_v1 [format {
##1 %s.add_res_v == $past(%s'((%s.pwo_uvw_i.v0_i + %s.pwo_uvw_i.v1_i) %% 'd%s), 1)
}   $imp                  $Q_width  $imp           $imp                   $Q]

#STG2
#Modular multiplication of u*v
assert -name assert_uv12 [subst {
$imp.mul_res_uv12_reduced == $Q_width'(($imp.add_res_u * $imp.add_res_v) % 'd$Q)
}]

#STG3
#Subtraction of uv12 and uv00
assert -name assert_uv12_sub_uv00 [format {
##1 %s.sub_res0 == $past(((%s.mul_res_uv12_reduced < %s.uv00_reduced_reg[0]) ? (((%s.mul_res_uv12_reduced - %s.uv00_reduced_reg[0]) + 'd%s) %% 'd%s) : ((%s.mul_res_uv12_reduced - %s.uv00_reduced_reg[0]) %% 'd%s)), 1)
}   $imp                   $imp                     $imp                          $imp                      $imp                        $Q      $Q      $imp                      $imp                        $Q ]

#STG4
#Final result uv1_o in case of no accumulate
#Subtraction of res0 and uv11
assert -name assert_uv1_o_no_accumulate [format {
!accumulate |-> ##2 %s.pwo_uv_o.uv1_o == $past(((%s.sub_res0 < %s.uv11_reduced_reg[1]) ? (((%s.sub_res0 - %s.uv11_reduced_reg[1]) + 'd%s) %% 'd%s) : ((%s.sub_res0 - %s.uv11_reduced_reg[1]) %% 'd%s)), 2)
}                   $imp                          $imp         $imp                          $imp         $imp                        $Q       $Q      $imp          $imp                         $Q]

#STG5
#Modular multiplication of zeta*uv11
assert -name assert_uvz11 [format {
%s.uvz11_reduced == %s'((%s.uv11_reduced_reg[2] * %s.z1_reg[2]) %% 'd%s)
} $imp              $Q_width $imp                 $imp              $Q]

#STG6
#Final result uv0_o in case of no accumulate
#Modular addition of uvz11 and uv00
assert -name assert_uv0_o_no_accumulate [format {
!accumulate |-> ##1 %s.pwo_uv_o.uv0_o == $past(((%s.uvz11_reduced + %s.uv00_reduced_reg[2]) %% 'd%s), 1)
}                   $imp                         $imp               $imp                        $Q]

#STG7
#Final results in case of accumulate
#Modular additions
assert -name assert_uv0_o_accumulate [format {
accumulate |-> ##1 %s.pwo_uv_o.uv0_o == $past(((%s.uv0_o_int + %s.w0_reg[3]) %% 'd%s), 1)
}                  $imp                         $imp           $imp              $Q] 
assert -name assert_uv1_o_accumulate [format {
accumulate |-> ##1 %s.pwo_uv_o.uv1_o == $past(((%s.uv1_o_int_reg + %s.w1_reg[3]) %% 'd%s), 1)
}                  $imp                         $imp               $imp              $Q] 



source [get_install_dir]/etc/res//tcl_library/jasper_tcl_library.tcl
prove -bg -all
