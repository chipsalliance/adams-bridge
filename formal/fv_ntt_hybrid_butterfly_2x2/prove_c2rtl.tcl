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
set Q_width [expr {ceil(log($Q)/log(2))}]           ; # Bit-width of Q
set width 24                                            ; # Shouldn't be greater than c_width
set c_width 32                                          ; # Max width given by c++ model types
set zw [expr {$c_width - $width}]                       ; # Leading zeros up to 64bits for WIDTH values
set zr [expr {$c_width - 14}]                           ; # Leading zeros up to 64bits for rnd values (14 bits)
set imp ntt_hybrid_butterfly_2x2_imp                    ; # Top module name
set bf12 $imp.mlkem_masked_bf_1x2_inst0                   ; # butterfly 1x2 instatiation name under imp
set pawm $imp.mlkem_masked_pawm_inst0                  ; # masked pairwm instatiation name under imp
set mgs0 $bf12.mlkem_masked_bf_inst00                    ; # masked gs bfu 0 instatiation name under imp
set mgs1 $bf12.mlkem_masked_bf_inst01                    ; # masked gs bfu 1 instatiation name under imp
set mul0 $mgs0.mult_inst_0                              ; # mult_inst_0 instatiation name under imp
set mul1 $mgs1.mult_inst_0                              ; # mult_inst_0 instatiation name under imp
set mbr0 $mul0.masked_barrett_mult_inst                 ; # masked_barret_reduction instatiation name under imp.mult_inst_0
set mbr1 $mul1.masked_barrett_mult_inst                 ; # masked_barret_reduction instatiation name under imp.mult_inst_0

# Spec loading
check_c2rtl -set_dynamic_pruning -spec
check_c2rtl -compile -spec formal/fv_ntt_hybrid_butterfly_2x2/fv_ntt_hybrid_butterfly_2x2.cpp

# Imp loading
check_c2rtl -analyze -imp -sv -f filelist.f
check_c2rtl -elaborate -imp -top ntt_hybrid_butterfly_2x2 -disable_auto_bbox
 
check_c2rtl -setup
set_reset_max_iterations 400
clock ntt_hybrid_butterfly_2x2_imp.clk
reset -expression ~ntt_hybrid_butterfly_2x2_imp.reset_n
 
# Assumptions:
assume -env -name no_zero [format {!%s.zeroize} $imp]
#assume -env -name assume_acc {acc == 1'd1}
assume -env -name assume_stable_accumulate {$stable(acc)}
assume -env -name stable_mode {$stable(mode)}
assume -env -name assume_mlkem {mlkem == 1'd1}
assume -env -name stable_mask {$stable(masking_en)}
assume -env -name stable_intt_passthrough {$stable(intt_passthrough)}
assume -env -name stable_ntt_passthrough {$stable(ntt_passthrough)}
assume -env -name assume_no_intt_passthrough_during_ct {(mode == 'd0) |-> !intt_passthrough}
assume -env -name assume_no_ntt_passthrough_during_gs {(mode == 'd1) |-> !ntt_passthrough}
assume -env -name assume_input_u00 [format {u00 < 'd%s} $Q]
assume -env -name assume_input_v00 [format {v00 < 'd%s} $Q]
assume -env -name assume_input_w00 [format  {w00 < 'd%s} $Q]
assume -env -name assume_input_u01 [format {u01 < 'd%s} $Q]
assume -env -name assume_input_v01 [format {v01 < 'd%s} $Q]
assume -env -name assume_input_w01 [format {w01 < 'd%s} $Q]
assume -env -name assume_input_w10 [format {w10 < 'd%s} $Q]
assume -env -name assume_input_w11 [format {w11 < 'd%s} $Q]
assume -env -name assume_input_u0 [format {u0_0 + u0_1 < 'd%s} $Q]
assume -env -name assume_input_v0 [format {v0_0 + v0_1 < 'd%s} $Q]
assume -env -name assume_input_w0 [format {w0_0 + w0_1 < 'd%s} $Q]
assume -env -name assume_input_u00share [format {u00_0 + u00_1 < 'd%s} $Q]
assume -env -name assume_input_v00share [format {v00_0 + v00_1 < 'd%s} $Q]
assume -env -name assume_input_u01share [format {u01_0 + u01_1 < 'd%s} $Q]
assume -env -name assume_input_v01share [format {v01_0 + v01_1 < 'd%s} $Q]
assume -env -name assume_input_v11_int [format {v11_int_0 + v11_int_1 < 'd%s} $Q]
assume -env -name assume_input_v10_int [format {v10_int_0 + v10_int_1 < 'd%s} $Q]

#assume -env -name no_overflow {24'(ntt_hybrid_butterfly2x2_imp.mlkem_masked_bf_1x2_inst0.mlkem_masked_bf_inst00.mult_inst_0.masked_barrett_mult_inst.x[0] + ntt_hybrid_butterfly2x2_imp.mlkem_masked_bf_1x2_inst0.mlkem_masked_bf_inst00.mult_inst_0.masked_barrett_mult_inst.x[1]) < 24'((3329**2)-1)}


assume -env -name input_u0_0 [format {u0_0 == {%s'd0,%s.pwm_shares_uvw_i.u0_i[0]}} $zw $imp]  -replace_if
assume -env -name input_u0_1 [format {u0_1 == {%s'd0,%s.pwm_shares_uvw_i.u0_i[1]}} $zw $imp] -replace_if
assume -env -name input_v0_0 [format {v0_0 == {%s'd0,%s.pwm_shares_uvw_i.v0_i[0]}} $zw $imp] -replace_if
assume -env -name input_v0_1 [format {v0_1 == {%s'd0,%s.pwm_shares_uvw_i.v0_i[1]}} $zw $imp] -replace_if
assume -env -name input_w0_0 [format {w0_0 == {%s'd0,%s.pwm_shares_uvw_i.w0_i[0]}} $zw $imp] -replace_if
assume -env -name input_w0_1 [format {w0_1 == {%s'd0,%s.pwm_shares_uvw_i.w0_i[1]}} $zw $imp] -replace_if
assume -env -name input_acc [format {acc == %s.accumulate} $imp] -replace_if
assume -env -name input_mlkem [format {mlkem == %s.mlkem} $imp] -replace_if
assume -env -name input_u00 [format {u00 == {%s'd0,%s.u00}} $zw $imp] -replace_if
assume -env -name input_v00 [format {v00 == {%s'd0,%s.v00}} $zw $imp] -replace_if
assume -env -name input_w00 [format {w00 == {%s'd0,%s.w00}} $zw $imp] -replace_if
assume -env -name input_u01 [format {u01 == {%s'd0,%s.u01}} $zw $imp] -replace_if
assume -env -name input_v01 [format {v01 == {%s'd0,%s.v01}} $zw $imp] -replace_if
assume -env -name input_w01 [format {w01 == {%s'd0,%s.w01}} $zw $imp] -replace_if
assume -env -name input_w10 [format {w10 == {%s'd0,%s.uvw_i.w10_i}} $zw $imp] -replace_if
assume -env -name input_w11 [format {w11 == {%s'd0,%s.uvw_i.w11_i}} $zw $imp] -replace_if
assume -env -name input_mode [format {mode == {5'd0,%s.mode}} $imp] -replace_if
assume -env -name input_masking_en [format {masking_en == %s.masking_en} $imp] -replace_if
assume -env -name input_intt_passthrough [format {intt_passthrough == %s.intt_passthrough} $imp] -replace_if
assume -env -name input_ntt_passthrough [format {ntt_passthrough == %s.ntt_passthrough} $imp] -replace_if
assume -env -name input_u00_0 [format {u00_0 == {%s'd0,%s.u00[0]}} $zw $bf12] -replace_if
assume -env -name input_u00_1 [format {u00_1 == {%s'd0,%s.u00[1]}} $zw $bf12] -replace_if
assume -env -name input_v00_0 [format {v00_0 == {%s'd0,%s.v00[0]}} $zw $bf12] -replace_if
assume -env -name input_v00_1 [format {v00_1 == {%s'd0,%s.v00[1]}} $zw $bf12] -replace_if
assume -env -name input_v10_int_0 [format {v10_int_0 == {%s'd0,%s.v10_int[0]}} $zw $bf12] -replace_if
assume -env -name input_v10_int_1 [format {v10_int_1 == {%s'd0,%s.v10_int[1]}} $zw $bf12] -replace_if
assume -env -name input_u01_0 [format {u01_0 == {%s'd0,%s.u01[0]}} $zw $bf12] -replace_if
assume -env -name input_u01_1 [format {u01_1 == {%s'd0,%s.u01[1]}} $zw $bf12] -replace_if
assume -env -name input_v01_0 [format {v01_0 == {%s'd0,%s.v01[0]}} $zw $bf12] -replace_if
assume -env -name input_v01_1 [format {v01_1 == {%s'd0,%s.v01[1]}} $zw $bf12] -replace_if
assume -env -name input_v11_int_0 [format {v11_int_0 == {%s'd0,%s.v11_int[0]}} $zw $bf12] -replace_if
assume -env -name input_v11_int_1 [format {v11_int_1 == {%s'd0,%s.v11_int[1]}} $zw $bf12] -replace_if


#butterfly 1st stage checks
assert -name ct_bfu_00_u_mlkem [format {(mode == 'd0 & !masking_en) |-> ##3 $past(u_ct_mlkem, 3) == %s.u10_int} $imp] 
assert -name ct_bfu_00_v_mlkem [format {(mode == 'd0 & !masking_en) |-> ##3 $past(v_ct_mlkem, 3) == %s.u11_int} $imp]
assert -name gs_bfu_00_u_mlkem [format {(mode == 'd1 & !masking_en) |-> ##3 $past(u_gs_mlkem, 3) == %s.u10_int} $imp]
assert -name gs_bfu_00_v_mlkem [format {(mode == 'd1 & !masking_en) |-> ##3 $past(v_gs_mlkem, 3) == %s.u11_int} $imp]

assert -name ct_bfu_01_u_mlkem [format {(mode == 'd0 & !masking_en) |-> ##3 $past(u_ct_mlkem_1, 3) == %s.v10_int} $imp]
assert -name ct_bfu_01_v_mlkem [format {(mode == 'd0 & !masking_en) |-> ##3 $past(v_ct_mlkem_1, 3) == %s.v11_int} $imp]
assert -name gs_bfu_01_u_mlkem [format {(mode == 'd1 & !masking_en) |-> ##3 $past(u_gs_mlkem_1, 3) == %s.v10_int} $imp]
assert -name gs_bfu_01_v_mlkem [format {(mode == 'd1 & !masking_en) |-> ##3 $past(v_gs_mlkem_1, 3) == %s.v11_int} $imp] 

#butterfly 2nd stage checks
assert -name ct_bfu_10_u_mlkem [format {(mode == 'd0 & !masking_en) |-> ##6 $past(u_ct_mlkem_2, 6) == %s.u20_int} $imp]
assert -name ct_bfu_10_v_mlkem [format {(mode == 'd0 & !masking_en) |-> ##6 $past(v_ct_mlkem_2, 6) == %s.v20_int} $imp]
assert -name gs_bfu_10_u_mlkem [format {(mode == 'd1 & !masking_en) |-> ##6 $past(u_gs_mlkem_2, 6) == %s.u20_int} $imp]
assert -name gs_bfu_10_v_mlkem [format {(mode == 'd1 & !masking_en) |-> ##6 $past(v_gs_mlkem_2, 6) == %s.v20_int} $imp]

assert -name ct_bfu_11_u_mlkem [format {(mode == 'd0 & !masking_en) |-> ##6 $past(u_ct_mlkem_3, 6) == %s.u21_int} $imp]
assert -name ct_bfu_11_v_mlkem [format {(mode == 'd0 & !masking_en) |-> ##6 $past(v_ct_mlkem_3, 6) == %s.v21_int} $imp]
assert -name gs_bfu_11_u_mlkem [format {(mode == 'd1 & !masking_en) |-> ##6 $past(u_gs_mlkem_3, 6) == %s.u21_int} $imp]
assert -name gs_bfu_11_v_mlkem [format {(mode == 'd1 & !masking_en) |-> ##6 $past(v_gs_mlkem_3, 6) == %s.v21_int} $imp]

assert -name u20_no_passthrough [format {(((mode == 'd0 & !ntt_passthrough) | (mode == 'd1 & !intt_passthrough)) & !masking_en) |-> %s.uv_o.u20_o == %s.u20_int} $imp $imp]
assert -name v20_no_passthrough [format {(((mode == 'd0 & !ntt_passthrough) | (mode == 'd1 & !intt_passthrough)) & !masking_en) |-> %s.uv_o.v20_o == %s.v20_int} $imp $imp]
assert -name u21_no_passthrough [format {(((mode == 'd0 & !ntt_passthrough) | (mode == 'd1 & !intt_passthrough)) & !masking_en) |-> %s.uv_o.u21_o == %s.u21_int} $imp $imp]
assert -name v21_no_passthrough [format {(((mode == 'd0 & !ntt_passthrough) | (mode == 'd1 & !intt_passthrough)) & !masking_en) |-> %s.uv_o.v21_o == %s.v21_int} $imp $imp]

#checks for outputs during CT mode ntt passthrough
assert -name u20_ntt_passthrough [format {(mode == 'd0 & ntt_passthrough & !masking_en) |-> ##6 $past(u_ct_mlkem, 6) == %s.uv_o.u20_o} $imp]
assert -name v20_ntt_passthrough [format {(mode == 'd0 & ntt_passthrough & !masking_en) |-> ##6 $past(u_ct_mlkem_1, 6) == %s.uv_o.v20_o} $imp]
assert -name u21_ntt_passthrough [format {(mode == 'd0 & ntt_passthrough & !masking_en) |-> ##6 $past(v_ct_mlkem, 6) == %s.uv_o.u21_o} $imp]
assert -name v21_ntt_passthrough [format {(mode == 'd0 & ntt_passthrough & !masking_en) |-> ##6 $past(v_ct_mlkem_1, 6) == %s.uv_o.v21_o} $imp]

#checks for outputs during GS mode intt passthrough
assert -name u20_intt_passthrough [format {(mode == 'd1 & intt_passthrough & !masking_en) |-> ##6 $past(u_gs_mlkem, 6) == %s.uv_o.u20_o} $imp]
assert -name v20_intt_passthrough [format {(mode == 'd1 & intt_passthrough & !masking_en) |-> ##6 $past(v_gs_mlkem, 6) == %s.uv_o.v20_o} $imp]
assert -name u21_intt_passthrough [format {(mode == 'd1 & intt_passthrough & !masking_en) |-> ##6 $past(u_gs_mlkem_1, 6) == %s.uv_o.u21_o} $imp]
assert -name v21_intt_passthrough [format {(mode == 'd1 & intt_passthrough & !masking_en) |-> ##6 $past(v_gs_mlkem_1, 6) == %s.uv_o.v21_o} $imp]

##checks for outputs during GS mode intt passthrough masked
assert -name u20_intt_passthrough_m [format {(mode == 'd1 & intt_passthrough & masking_en) |-> %s.uv_o.u20_o == %s.uv_o.u20_o} $imp $bf12]
assert -name v20_intt_passthrough_m [format {(mode == 'd1 & intt_passthrough & masking_en) |-> %s.uv_o.v20_o == %s.uv_o.u21_o} $imp $bf12]
assert -name u21_intt_passthrough_m [format {(mode == 'd1 & intt_passthrough & masking_en) |-> %s.uv_o.u21_o == %s.uv_o.v20_o} $imp $bf12]
assert -name v21_intt_passthrough_m [format {(mode == 'd1 & intt_passthrough & masking_en) |-> %s.uv_o.v21_o == %s.uv_o.v21_o} $imp $bf12]

#checks for masked_bfu_1x2
assert -name u10_int [format {
    ##15 $past(u10_int[%s-1:0], 15) == %s.u10_int[0][%s-1:0] + %s.u10_int[1][%s-1:0]
}               $width                $bf12        $width    $bf12        $width]
assert -name u20_o [format {##16 $past(u10_div2, 16) == %s.uv_o.u20_o}  $bf12]
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

assert -name u21_o [format {##1 $past(v10_div2, 1) == %s.uv_o.u21_o}  $bf12]

assert -name u11_int [format {
    ##15 $past(u11_int[%s-1:0], 15) == %s.u11_int[0][%s-1:0] + %s.u11_int[1][%s-1:0]
}               $width                $bf12        $width    $bf12        $width]
assert -name v20_o [format {##16 $past(u11_div2, 16) == %s.uv_o.v20_o}  $bf12]
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
}      $mbr1      $mbr1                  $mbr1        $mbr1          $width]

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

assert -name v21_o [format {##1 $past(v10_div2, 1) == %s.uv_o.u21_o}  $bf12]

#masked pairwm subblock checks

#MUL1
assert -name assert_u0v0 [format {##2 
(%s.u0v0_packed[0] + %s.u0v0_packed[1]) == $past(((%s.u0[0] + %s.u0[1]) * (%s.v0[0] + %s.v0[1])), 2)
} $pawm             $pawm                           $pawm       $pawm       $pawm      $pawm]
assert -name assert_u0v1 [format {##2 
(%s.u0v1_packed[0] + %s.u0v1_packed[1]) == $past(((%s.u0[0] + %s.u0[1]) * (%s.v1[0] + %s.v1[1])), 2)
} $pawm                $pawm                      $pawm        $pawm      $pawm        $pawm]
assert -name assert_u1v0 [format {##2 
(%s.u1v0_packed[0] + %s.u1v0_packed[1]) == $past(((%s.u1[0] + %s.u1[1]) * (%s.v0[0] + %s.v0[1])), 2)
} $pawm             $pawm                           $pawm       $pawm       $pawm       $pawm]
assert -name assert_zeta_v1 [format {##2 
(%s.zeta_v1_packed[0] + %s.zeta_v1_packed[1]) == $past(((%s.zeta[0] + %s.zeta[1]) * (%s.v1[0] + %s.v1[1])), 2)
} $pawm                 $pawm                           $pawm          $pawm        $pawm       $pawm]

#RED1
assert -name assert_u0v0_red [format {##6 
12'(%s.u0v0_reduced[0] + %s.u0v0_reduced[1]) == $past((24'(%s.u0v0_packed[0] + %s.u0v0_packed[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]
assert -name assert_u0v1_red [format {##6 
12'(%s.u0v1_reduced[0] + %s.u0v1_reduced[1]) == $past((24'(%s.u0v1_packed[0] + %s.u0v1_packed[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm                  $Q]
assert -name assert_u1v0_red [format {##6 
12'(%s.u1v0_reduced[0] + %s.u1v0_reduced[1]) == $past((24'(%s.u1v0_packed[0] + %s.u1v0_packed[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]
assert -name assert_zeta_v1_red [format {##6 
12'(%s.zeta_v1_reduced[0] + %s.zeta_v1_reduced[1]) == $past((24'(%s.zeta_v1_packed[0] + %s.zeta_v1_packed[1]) %% %s), 6)
}   $pawm                   $pawm                               $pawm                   $pawm                   $Q]

#MUL2
assert -name assert_u1_v1 [format {##2 
(%s.u1v1_packed[0] + %s.u1v1_packed[1]) == $past(((%s.u1_reg[0][0] + %s.u1_reg[0][1]) * (%s.zeta_v1_reduced[0] + %s.zeta_v1_reduced[1])), 2)
} $pawm               $pawm                           $pawm            $pawm          $pawm               $pawm]

#RED2
assert -name assert_u1_v1_red [format {##6 
12'(%s.u1v1_reduced[0] + %s.u1v1_reduced[1]) == $past((24'(%s.u1v1_packed[0] + %s.u1v1_packed[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]

#ADD
assert -name assert_u0v0_plus_u1v1 [format {##1 
(%s.uv0[0] + %s.uv0[1]) == $past(((%s.u0v0_reduced_reg[0][0] + %s.u0v0_reduced_reg[0][1]) + (%s.u1v1_reduced[0] + %s.u1v1_reduced[1])), 1)
} $pawm               $pawm                           $pawm            $pawm          $pawm               $pawm]
assert -name assert_u0v1_plus_u1v0 [format {##1 
(%s.uv1[0] + %s.uv1[1]) == $past(((%s.u0v1_reduced_reg[0][0] + %s.u0v1_reduced_reg[0][1]) + (%s.u1v0_reduced_reg[0][0] + %s.u1v0_reduced_reg[0][1])), 1)
} $pawm               $pawm                           $pawm            $pawm          $pawm               $pawm]

#ACC
assert -name assert_acc_uv0_w0 [format {##1 
(%s.uvw0[0] + %s.uvw0[1]) == $past(((%s.uv0[0] + %s.uv0[1]) + (%s.w0[0] + %s.w0[1])), 1)
} $pawm               $pawm                           $pawm            $pawm          $pawm               $pawm]
assert -name assert_acc_uv1_w1 [format {##1 
(%s.uvw1[0] + %s.uvw1[1]) == $past(((%s.uv1[0] + %s.uv1[1]) + (%s.w1[0] + %s.w1[1])), 1)
} $pawm               $pawm                           $pawm            $pawm          $pawm               $pawm]

#RED3
assert -name assert_res0_no_acc [format {
!acc |-> ##6 %s'(%s.res0[0] + %s.res0[1]) == $past(%s'(%s'(%s.uv0[0] + %s.uv0[1]) %% 'd%s), 6)
}   $Q_width $pawm   $pawm                          $Q_width $width     $pawm   $pawm               $Q]
assert -name assert_res1_no_acc [format {
!acc |-> ##6 12'(%s.res1[0] + %s.res1[1]) == $past((24'(%s.uv1[0] + %s.uv1[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]
assert -name assert_res0_acc [format {
acc |-> ##6 12'(%s.res0[0] + %s.res0[1]) == $past((24'(%s.uvw0[0] + %s.uvw0[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]
assert -name assert_res1_acc [format {
acc |-> ##6 12'(%s.res1[0] + %s.res1[1]) == $past((24'(%s.uvw1[0] + %s.uvw1[1]) %% %s), 6)
}   $pawm               $pawm                               $pawm               $pawm               $Q]

proof_structure -init INIT -copy_all

proof_structure -create partition -from INIT \
    -op_name P -imp_name {BFU BFUPT BFU12 MUL1 RED1 MUL2 RED2 ADD ACC RED3 X0 T0 QT0 C0 X1 T1 QT1 C1} \
    -copy { {ct_bfu_00_u_mlkem ct_bfu_00_v_mlkem gs_bfu_00_u_mlkem gs_bfu_00_v_mlkem
            ct_bfu_01_u_mlkem ct_bfu_01_v_mlkem gs_bfu_01_u_mlkem gs_bfu_01_v_mlkem
            ct_bfu_10_u_mlkem ct_bfu_10_v_mlkem gs_bfu_10_u_mlkem gs_bfu_10_v_mlkem
            ct_bfu_11_u_mlkem ct_bfu_11_v_mlkem gs_bfu_11_u_mlkem gs_bfu_11_v_mlkem}
            {u20_no_passthrough v20_no_passthrough u21_no_passthrough v21_no_passthrough
            u20_ntt_passthrough v20_ntt_passthrough u21_ntt_passthrough v21_ntt_passthrough
            u20_intt_passthrough v20_intt_passthrough u21_intt_passthrough v21_intt_passthrough
            u20_intt_passthrough_m v20_intt_passthrough_m u21_intt_passthrough_m v21_intt_passthrough_m}
            {u10_int u20_o sub_res_0 mul_res_0 u21_o u11_int v20_o sub_res_1 mul_res_1 v21_o}
            {assert_u0v0 assert_u0v1 assert_u1v0 assert_zeta_v1 }
            {assert_u0v0_red assert_u0v1_red assert_u1v0_red assert_zeta_v1_red}
            {assert_u1_v1} {assert_u1_v1_red} {assert_u0v0_plus_u1v1 assert_u0v1_plus_u1v0} {assert_acc_uv0_w0 assert_acc_uv1_w1}
            {assert_res0_no_acc assert_res1_no_acc assert_res0_acc assert_res1_acc}
            {mbr_check_t_0 mbr_check_x_reg_0 mbr_check_tmp_0} {mbr_check_qt_0} {mbr_check_c_0} {mbr_check_c_reg_CC3_0 mbr_check_c_reg_CC5_0 mbr_check_c_rolled0_0 mbr_check_c_rolled1_0}
            {mbr_check_t_1 mbr_check_x_reg_1 mbr_check_tmp_1} {mbr_check_qt_1} {mbr_check_c_1} {mbr_check_c_reg_CC3_1 mbr_check_c_reg_CC5_1 mbr_check_c_rolled0_1 mbr_check_c_rolled1_1}}

proof_structure -create stopat -from RED1 \
    -op_name R0 -imp_name RED1_U0V0 -add [subst {$pawm.u0v0_packed}]

proof_structure -create stopat -from RED1 \
    -op_name R1 -imp_name RED1_U0V1 -add [subst {$pawm.u0v1_packed}]

proof_structure -create stopat -from RED1 \
    -op_name R2 -imp_name RED1_U1V0 -add [subst {$pawm.u1v0_packed}]

proof_structure -create stopat -from RED1 \
    -op_name R3 -imp_name RED1_Z_V1 -add [subst {$pawm.zeta_v1_packed}]

proof_structure -create stopat -from MUL2 \
    -op_name M0 -imp_name MUL2_Z_V1 -add [subst {$pawm.zeta_v1_reduced}]

proof_structure -create stopat -from RED2 \
    -op_name R4 -imp_name RED2_U1_V1 -add [subst {$pawm.u1v1_packed}]

proof_structure -create stopat -from ADD \
    -op_name A0 -imp_name ADD_UV0 -add [subst {$pawm.u0v0_reduced_reg $pawm.u1v1_reduced}]

proof_structure -create stopat -from ADD \
    -op_name A1 -imp_name ADD_UV1 -add [subst {$pawm.u0v1_reduced_reg $pawm.u1v0_reduced_reg}]

proof_structure -create stopat -from ACC \
    -op_name A2 -imp_name ACC_W0 -add [subst {$pawm.uv0}]

proof_structure -create stopat -from ACC \
    -op_name A3 -imp_name ACC_W1 -add [subst {$pawm.uv1}]

proof_structure -create stopat -from RED3 \
    -op_name R5 -imp_name RED3_UV0 -add [subst {$pawm.uv0}]

proof_structure -create stopat -from RED3 \
    -op_name R6 -imp_name RED3_UV1 -add [subst {$pawm.uv1}]

proof_structure -create stopat -from RED3 \
    -op_name R7 -imp_name RED3_W0 -add [subst {$pawm.uvw0}]

proof_structure -create stopat -from RED3 \
    -op_name R8 -imp_name RED3_W1 -add [subst {$pawm.uvw1}]
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