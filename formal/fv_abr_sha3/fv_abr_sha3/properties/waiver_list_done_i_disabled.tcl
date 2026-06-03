# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

#
# Any disclosure about the Cadence Design Systems software or its use
# model to any third party violates the written Non-Disclosure Agreement
# between Cadence Design Systems, Inc. and the customer.
#
# THIS SOFTWARE CONTAINS CONFIDENTIAL INFORMATION AND TRADE SECRETS OF
# CADENCE DESIGN SYSTEMS, INC. USE, DISCLOSURE, OR REPRODUCTION IS
# PROHIBITED WITHOUT THE PRIOR EXPRESS WRITTEN PERMISSION OF CADENCE
# DESIGN SYSTEMS, INC.
#
# Copyright (C) 2000-2023 Cadence Design Systems, Inc. All Rights
# Reserved.  Unpublished -- rights reserved under the copyright laws of
# the United States.
#
# This product includes software developed by others and redistributed
# according to license agreement. See doc/third_party_readme.txt for
# further details.
#
# RESTRICTED RIGHTS LEGEND
#
# Use, duplication, or disclosure by the Government is subject to
# restrictions as set forth in subparagraph (c) (1) (ii) of the Rights in
# Technical Data and Computer Software clause at DFARS 252.227-7013 or
# subparagraphs (c) (1) and (2) of Commercial Computer Software -- Restricted
# Rights at 48 CFR 52.227-19, as applicable.
#
#
#                           Cadence Design Systems, Inc.
#                           2655 Seely Avenue
#                           San Jose, CA 95134
#                           Phone: 408.943.1234
#
# For technical assistance visit http://support.cadence.com.


check_cov -waiver -add -type {*} -instance {u_pad} -comment {Added by GUI, apply waiver on instance 'u_pad'} -tag {*}


check_cov -waiver -add -type {*} -instance {u_keccak} -comment {Added by GUI, apply waiver on instance 'u_keccak'} -tag {*}


check_cov -waiver -add -type {*} -instance {abr_prim_mubi_pkg} -comment {Added by GUI, apply waiver on instance 'abr_prim_mubi_pkg'} -tag {*}


check_cov -waiver -add -type {*} -instance {abr_sha3_pkg} -comment {Added by GUI, apply waiver on instance 'abr_sha3_pkg'} -tag {*}


check_cov -waiver -add -type {*} -instance {u_state_regs} -comment {Added by GUI, apply waiver on instance 'u_state_regs'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 133 -end_line 133 -start_column 3 -end_column 63 -expression {1'b1} -persistency {AAAA4HicdYxBDoJAEASLH/iEfQKKosSY+BMjrqAHJQFNPPB4avGq2fTOTE/1ABlwpCJXNRc2NGyJdtF6ptCvWFE6Fez8G9ncutZL7FIfFrI1PScGbnPuezvp4zz47rQ8Cd7ueNu9pK9meueU7NwdVJidRETd33RgVA+vtn+Z/QSTDSNj} -type {branch} -top -comment {Added by GUI, apply waiver on ' 1 2 3'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 139 -end_line 139 -start_column 3 -end_column 97 -expression {1'b1} -persistency {AAABJHichY5ZCsJAEESfN/AIOUI0bkEEbxKyqohGYvzzaB7Olwnil0jTU9U11TUDTIA9KbFdULKkYU0lq8ScRD1lzsopYePZ6I3FhdrgnanDVG9BR8adY9gbs4d+Od+tEweuRLKbSifW+hvxItYqHW3IaHXtgnPMGlJ7WR82vs6Ip31WKa1cloWbh+9Uf7Y+2cNffnu3b+9EMNM=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 1 2 3'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 143 -end_line 143 -start_column 3 -end_column 64 -expression {1'b1} -persistency {AAAA4nicnYzbCcJQEESPHViCJURj1CBCOgl5qgS8cONXqvfkpgNZ9jGzMwPsgIqSzG7pKBi50nv17oZcvuTERZRzc45qM/dZbtUe5WGvtiVSM/NKvi177UU8W2+efDgwMZjfyU5J/yXobPwO4piY2jtaIWUGXY8/nPcf+xwkNA==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 1 2 3'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 282 -end_line 286 -start_column 31 -end_column 10 -expression {(st == 6'b111010)} -persistency {AAABHnicbY7NCsIwEIQ/PXoSn8Cb19aqtYgggjdvei+tSVXwj9T3x0kigiJhMjub2dkAHWBFQSLUHJjSkGNUGXFFpn7BmJlUxlx3I28inqjnvan60Je3xlHScgpzMbsr9PRiOXLmJrVl+HNanpozqpbCTmovv+MaJioubKQc93f+Qz0ntiyUt/6TF39QhuRKsKrtJyPuSRnpX559yuArwWqveQFu4iXf} -type {branch} -top -comment {Added by GUI, apply waiver on ' 77 80'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 288 -end_line 291 -start_column 16 -end_column 10 -expression {~|{(st == 6'b101100), (st == 6'b100001), (st == 6'b1011), (st == 6'b10000), (st == 6'b110), (st == 6'b111010)}} -persistency {AAABHnicbY5LC8IwEIQ/PXoSf4E3r631VUQQwZs3vZfUpCr4IvX/4yQtgiJhMjub2dkAHWBNTiKUHJlSMceqsmJDpn7OmJlUxkJ3JW8inqgXvKn60Je3xFNQc45z0G3R04vjxIW71I7hz6l5ac6qWgl7qYP8nlucMFzZSnkebf5TPS92LJW3+ZPX/KCIyUZwqt0no9mTMtK/AoeUwVeC0177Bm+hJeA=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 77 80'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 312 -end_line 312 -start_column 19 -end_column 50 -expression {~|{(mux_sel == 3'b10), (mux_sel == 3'b101)}} -persistency {AAAAqHicLYxLEoJADAVbT+AR2LEdwR9aVHETSz6DC1cIK8q72065eMlL5yXABmioCKql40jkTK/r7Q9KeUXByankYo1mg/0g+2X3ctiZbZm48+aZ7mD7VyObZTOD+5FFP/l/UBm1ylnTHN0svExeEw18uJF9Ae+TFsw=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 94'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 331 -end_line 337 -start_column 61 -end_column 12 -expression {((st == 6'b101100) & ((4'b1001 != done_i) | run_i | process_i))} -persistency {AAAB0HicdZC9TsNgDEUPAwsTE2JkK0gd2pS/gpCQELxAHwA1+RKoVKUoCTCgvjsnhm6pLMexfX2v/QEHwCNzJnpOwRUVNyT/knHJzPqcjGuzGbd+K7ET46W1Hju1DsdicxpeaXmPuT/uQ/3ITskbK2qzMWcDVjrbsAmGjfmDPuJHfDaI7+1LnbWsiTuzqfg84tipl71ThfxJvX7mOVQX/xsv+ObJbk0Xu6yDqdvL1N9TieuZMt9jxLkbp2AovWMVtzZ8mu+yj2Au7LfartqqsrTTRWXLhbqng5pb7u2dDLxfTfoF/kE47Q==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 330 -end_line 331 -start_column 9 -end_column 59 -expression {((st == 6'b101100) & ~((4'b1001 != done_i) | run_i | process_i))} -persistency {AAABFHicZY5JCsJAEEWfN/AILnUXE6e48iZiTNRGY8Rp5eF93SIIUlTX78evAegBK0oys2LLlB1zalVt3VDIS3Jm/goWvju9mXUii96xHPp6K66suXFIfZ/ZMXOCzgFDLjo6Zze6bnqD9GUM5A/OPwSeqv/4bomTAq2qtbNSR3Zkz9L4son0nrbdk4pbGtXJKzpp40216pxoYMToDTTAKck=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 340 -end_line 349 -start_column 24 -end_column 10 -expression {(st == 6'b100001)} -persistency {AAAC6HicdZG9TsNAEISHlgpRIMqrsCO5CE74CQgJCcELpKOJcGwHCydGsYEi5F14VL47YhTHjlZ3tze3O3O7K+lA0r1G6rMiTXWhVFeK8WLOFw3ARwp1yW2ga/aU2D7nEMzGnoNLR8RGWmqiUq8u74/brkNeEs2UacHtR2bHMniMfDIrMpfsEzCjb8xw/yBvG6mV3tkzzfHmxET4FntD6QarsSFohX7peCvHl+DlKrAS36fWAo3EqfT443Prj+Zf3Xe6BR2ynOXmZ2eY2Xmx9c7g6/Gy3YGgkz0h12bbygrudyxPK+LDznhrn/QihzWmXsMkPHTsGZD1tDdrCn+Mns15dKrjzczG+tKD60Xl/pI7pmovk60nJc4yhXTaozurRjeDxgSDVo9qtDn7tZvCaafmWre8nXT0b4GydNxGfwGJZGXZ} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 352 -end_line 358 -start_column 35 -end_column 12 -expression {((st == 6'b1011) & (process_i | start_i))} -persistency {AAAB0HicdZDNSsNgEEWPiBtXrsSluyp00ab+VREE0RfoA0iTL9FCSSWJupC+uyeD3aUMk8nM3Ll35gMOgCfmTPScgmsqbkn+JeOSmfU5GTdmM+78VmInxitrPXZqHU7E5jS80fIRc3CoH+nHdkreWVGbjTkfsNLZhk0wbMwf9RG/4rNBfG/f6qxlTdybTcXnEcdOve6dKuRP6vUzL6G6+N94wQ/Pdmu62GUdTN1epv6eSlzPlPkeIy7cOAVD6R2ruLXhy3yXfQZzYb/VdtVWlaWdLipbLtU9G9Tc8mDvdOD9atIfATI47w==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 352 -end_line 352 -start_column 9 -end_column 33 -expression {((st == 6'b1011) & ~(process_i | start_i))} -persistency {AAAAmnicJY07DoMwEAUnN8gRXIaOAIHQcRPEV6QCASWHZyCydp897+0aeAAVJbHV0vFhpKD31qsNqbwkIfeV8rWPZmM1k13ZtxyeZltWajame+6/+6qEn8nAS2/XW+21LHB4Aotk9sdBf7ud6ASr3hUI} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 374 -end_line 380 -start_column 61 -end_column 12 -expression {((st == 6'b110) & ((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAAB0HicdZC9TsNgDEUPAwsTE2JkK0gd2pS/gpCQELxAHwA1+RKoVKUoCTCgvjsnVrulshzH9vW99gccAc/Mmeg5BTdU3JH8S8YlM+tzMm7NZtz7rcROjNfWeuzUOpyKzWl4p+Uz5uB45yd2Sj5YUZuNuRiw0tmGTTBszJ/0EX/is0F8bz/qrGVNPJhNxecRx069HZwq5E/q9TOvobrYbbzglxe7NV3ssg6m7iBTf08lrmfKfI8Rl26cgqH0jlXc2vBtvs++grmw32r7aqvK0k4XlS1X6p4Pam55tHc28H416R8EFDjx} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 361 -end_line 370 -start_column 27 -end_column 10 -expression {(st == 6'b10000)} -persistency {AAACyHicdZExT8NADIUfjJ0QA2K8LSBlKGkLFISEhOAPdOlWkSaBiDRBaYChdOGX8/mgQqGprLvzPdvPz3eS9iTdaqw+K9ZcI2W6UIKXcD5qAD5WpHNuA12yZ+T2OYdglnsGLh2QG6vWTEs9+7of7n1Wj0iqJ+UquU3l/lkOj9MJlQ2VNfsMzOkTc3oFqdCTEl+2IrXeYPxDpK8tbrONMmPKtcBbUBnjG/aCsitsgw1BG9+t8Z51SfEKVFSgKUoTvNKjuU4x15ow7FSRwmSTmJKK+w0r0Ir8qDPf7B3tBawJ+hwvHdDHzpCqh51Vc/gT+lnNve86+f2TiT5057U3XkvhmZqdTDZPRp4xRbxMwOyr1vRh6x/Czv8ytP23a95MOu7sudY1saOO9yvpLB1uo99T3mCg} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 374 -start_column 9 -end_column 59 -expression {((st == 6'b110) & ~((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAABKnicZY5NDoJQDAZHT+ARWOoO/8WVS29hRFCJAgbQlYd3IJpoTNP2e9P2tUAP2BAR6jEH5hxZkqgS856pPGLCwteUlfFob2ieydresRwG9sZU7Kg5d3PQf/uWzM6AobXGWmXcyQKeWsBNUroxtV7/VCruFF8EHqp/++xuf8rIVbmTsbplF06stQ+bSZtuW9OpdkuqunpFKU29NFEVHc0YMXoBQpguDw==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 383 -end_line 384 -start_column 16 -end_column 10 -expression {~|{(st == 6'b101100), (st == 6'b100001), (st == 6'b1011), (st == 6'b10000), (st == 6'b110)}} -persistency {AAAAiHicTYw7DoAwDEMfKxPiBBwBKL9u3ARR2gILA9xfwsCCIsex4wRIgBFLKTgWWiI9XpMXzxj5lppOyjCoR2VLcSPvyVbyIVPWcTJxsb133+8HqTaBlZ1DKqf4VZDnbzN2D7k=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 329 -end_line 338 -start_column 22 -end_column 10 -expression {(st == 6'b101100)} -persistency {AAACsnicdZHNTsNADISHKyfEAXHcW0DKoaTlpyAkBIIX6AOgpkkgIk0QXeBQeuHJ+bxQVSGprM3as/Z47EjakXSjsQacVDOdqtC5MryMe6oh+FiJzoiGuuBbkDvgHoFZ7gm4tEduqjc9aqHnUPfLbWeXl1xPKlUT3cr9sxIepyO9Ut/QOYdjAVMJ+oU58HdqN4j03WExW2swplJzvDmVKb5hL2i4xNbYCNSHbj541iXHq1DRgOZoyvDqgJY6xlxrlrhXRQ6TTWJKGuJrTqQl+UlvvtkH2itYM/Q5dhrRx+6YqoetVTP4M/pZzX3oOvnb/kSfugvafdBSBSa/lcnmKcgzpoTNRMy+bE0ft/6DRd3/Zahtc8qLD8iKnUmHvT1XuuLtoGd/NZ2l/S76A5jAXFs=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 363 -end_line 369 -start_column 61 -end_column 12 -expression {((st == 6'b10000) & ((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAAB0HicdZDNSsNgEEWPoBtXrsSluyp00ab+VREE0RfoA0iTL9FCSSWJupC+uyeD3aUMk8nM3Ll35gMOgCfmTPScgmsqbkn+JeOSmfU5GTdmM+78VmInxitrPXZqHU7E5jS80fIRc3CoH+nHdkreWVGbjTkfsNLZhk0wbMwf9RG/4rNBfG/f6qxlTdybTcXnEcdOve6dKuRP6vUzL6G6+N94wQ/Pdmu62GUdTN1epv6eSlzPlPkeIy7cOAVD6R2ruLXhy3yXfQZzYb/VdtVWlaWdLipbLtU9G9Tc8mDvdOD9atIfAqM48A==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 348 -start_column 41 -end_column 12 -expression {((st == 6'b100001) & ((processing & process_i) | (4'b1001 != done_i) | run_i | start_i))} -persistency {AAAB0HicdZDNSsNgEEWPghtXrsSluyp00ab+VREE0RfoA0iTL9FCSSWJupC+uyeD3aUMk8nM3Ll35gMOgCfmTPScgmsqbkn+JeOSmfU5GTdmM+78VmInxitrPXZqHU7E5jS80fIRc3CoH+nHdkreWVGbjTkfsNLZhk0wbMwf9RG/4rNBfG/f6qxlTdybTcXnEcdOve6dKuRP6vUzL6G6+N94wQ/Pdmu62GUdTN1epv6eSlzPlPkeIy7cOAVD6R2ruLXhy3yXfQZzYb/VdtVWlaWdLipbLtU9G9Tc8mDvdOD9atIf/7I47g==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 363 -start_column 9 -end_column 59 -expression {((st == 6'b10000) & ~((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAABKnicZY7LDsFgEEYPT+ARumRXd7Wy9BaiWjS0lbasPLzTioTIZP75/jNXoAdsiAj1mANzjixJVIlxz1QeMWHhb8rK92htaJzJ2tqxHAbWxlTsqDl3fe/ZfX1LZmXA0FxjrvLdyQKeWsBNUroxNV//ZCruFF8EHqp/++xuJ2XkqtzOWN2yCyfW2ofNpE23relUuyVVXb2ilKZemqiKjmaMGL0AQc0uDg==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 341 -end_line 342 -start_column 9 -end_column 39 -expression {((st == 6'b100001) & ~((processing & process_i) | (4'b1001 != done_i) | run_i | start_i))} -persistency {AAABSnicZZBNEsFAFIQ/N3CErFTs/P+tnMAVlBCkiKgkdg7hyL4JFqhX86anX0/3JEALWDKn50rYMmbPlJ1o575hKD9nwMTTkJl9r7bnPpIL2r48tNUmlKypODb3Xt5hPchURsTOamelfS0XcbcizzcuX8zH62rPyEW5mkQcuBMHFtaHG8nWpI17QMEvFZ0prEoc+zWFGWmT0vVNK1P+65UeN7mF/yB4Vu+XdazoZ5LpedCv+wQ6+TNH} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 372 -end_line 381 -start_column 23 -end_column 10 -expression {(st == 6'b110)} -persistency {AAACyHicdZG9TsNAEIQHylSIAlFeZ5BcBCf8BISEhOAF0qSLcGwHC8dGjoEipOHJ+faUCJk4Wt3d3uzu7OydpANJDxqpz4o106UyXSvBSzhfNAAfKdIVt4Fu2DNy+5xDMMu9AJeOyI1Va6qlXn2ddLhZPSKp5spVcpvI/bMcHqczKhsqa/YpmNM35vQOUqEnJb5sRWp9wPiHSD873GZbZcaUa4G3oDLGN+wNZbfYFhuCNr5b4z3rkuIVqKhAU5QmeKVHc51jrjVh2KkihckmMSUV93tWoBX5UWe+2SfaC1gT9DleOqCPnSFVz3urZvAn9LOaJ991vPmTsb706LU3XkvhmZq9TDZPRp4xRbxMwOyr1vRh6x/Czv8ytP23a95MOu3sudYdsZOO9yvpLB3vor9WR2Ch} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 351 -end_line 359 -start_column 25 -end_column 10 -expression {(st == 6'b1011)} -persistency {AAACOHicdZBLS8NQEIU/t67EhbjMrgpd9OGriiCILt30BxTTJFooqaRVF7X/3W+igpqU4eZmzpxz5s4AO8ANI3qelCmnFJyT+Zd5PzIUHzHgzGzIhd9Cbs/7RCy4fXHYk5tSMWHJc6378o6zayXniRml2QPJv5jpk3CkcqWy8jsRS/gwEl5EFr4nt76sK8eivx27DceIXF0o400L82tPh7X8QSs/4s3+c10zLs368tP67qq636qa6p/ZLzR3ddfx9w7GvHNrtXSmeMu8dlptdYp5CnnhNHDDHbey1jsc8nr2mLXi1fwna+4n0L+73LgzOGztueHK2kHL/ko7w34T/QRtSEea} -type {branch} -top -comment {Added by GUI, apply waiver on ' 103 104 105 122 123 140 124 141 142 97 131 115 132 116 133 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 217 -end_line 217 -start_column 5 -end_column 15 -expression {1'b1} -persistency {AAAAfHicJYzLDYAwDEMfG3BgAEYolF+FkNgEUaqKM7C/cODgJH5xAhTASsBJkYOezEjSlNR3vHigZZDzTKpZWafeiVm2EYdS2cjFxs353f2/TZXYo02iZpHMzS+HBg7+} -type {statement} -top -comment {Added by GUI, apply waiver on ' 35 36 41 44'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 220 -end_line 220 -start_column 5 -end_column 26 -expression {1'b1} -persistency {AAAAknicJYxJCsMwFENfb9AjZFfoKkMnUwq5SYjthkJ2bu9PntOF9PWFJOAAjARaEUlcWbiTVdk7M+gHem5+Aw95Mdt6L3o12+nD0WykMPHls/f+2xVnVt4uJv11T/xURW54iY6T3cbV5wYK5hJ8} -type {statement} -top -comment {Added by GUI, apply waiver on ' 35 36 41 44'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 227 -end_line 227 -start_column 5 -end_column 30 -expression {1'b1} -persistency {AAAAmnicPYxNCoNgEEOfN/AI7tz6U7UiBW9SalXcCV+9P77PgotMMplMgAQY6SnExJeGlY5ZNcsfav2eitat5ulczRbyQy9mS31IzU4E3vzYrr9/d0R1e/F6qA4W9WI+sIuMlyjJ7chsH06xIxQN} -type {statement} -top -comment {Added by GUI, apply waiver on ' 35 36 41 44'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 234 -end_line 234 -start_column 11 -end_column 32 -expression {((st == 6'b101100) & start_i)} -persistency {AAAAknicJYxJCsJAFESfN8gR3Amuuo1DmiB4EzGJQciuzf3J686ihl9UfeAAvEgEMTByY+bBpJvUD6154sLdq6WTZ7tBvZqVbjSHxu5A5s2fX93tvwvOLHz9OJovtbHqsnzkKSInt0X7DQrpEn0=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 35 36 41 44'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 332 -end_line 336 -start_column 11 -end_column 13 -expression {((st == 6'b101100) & ((4'b1001 != done_i) | run_i | process_i))} -persistency {AAABlHicdZDNasJQEEZPF9136dKdFrrQWLVWBKG0L+ADFJMYDIgWE9tF8d09GXWnXCZzZ76fmRvgAZgzoWekZAwpGJN7y81LBvYnJIysBrz5LeT2zK/2Gm7fPjzJTdnzTcU6dGfvR6PFSmTPLvAdbWZGh3+xxNvt86vLhtI93q368tPIL6q+7qoy/XPnNZrPmLq47LPgjw/RLXXssgmn+q5TKbOQ1zglvrZD143zcFj5jlJ9W6eD9bX6CedMvPJcu5VTliJ1dI48xz+5NfPI9ASOEjM9} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 353 -end_line 357 -start_column 11 -end_column 13 -expression {((st == 6'b1011) & (process_i | start_i))} -persistency {AAABlHicdZDLasJQEIY/Kd27dOlOhS40tt5KoVD0BXyAYhKDAali0nZRfPd+GXSnHCZzZv7LzAnQAt6ZMzRSMl4omJJ7y80bxvbnJEysxsz8FnKH5md7DXdkH9pyU058UrELHTwYj0aHrciJQ+AHurwZPf7EEm+3z48ue0r3WFiN5KeRn1St7qoy/XPnNZplTF1f9lnzy4foF3Xssg+n+q5TKbOQ1zglvrZH343zcNj6jlJ9V6dv62t1DOdMvPJcu5VTNiJ1dM4M4p/cmnnm9R+QfDM/} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 375 -end_line 379 -start_column 11 -end_column 13 -expression {((st == 6'b110) & ((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAABlHicdZDNasJQEEaPC/cuu3SnQhcabdWWQqHUF/ABxCQGA6Ji0nYhvntPBt0pl8ncme9n5gZoAZ/MGRopGS8UTMm95eY1Y/tzEl6txsz8FnKH5om9hjuyDx25KSdWVGxDB+1rPLEROXEI/ECXD6PHWSzxdv/86rKjdI83q5H8NPKzqsVDVaZ/7rxG8x1Tl9d9lvzxJbqnjl124VQ/dCplFvIap8TX9ui7cR4OG99Rqu/q9GN9q47hnIlXnlu3cspapI7OhUH8k3szL7z/A5LmM0E=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 284 -end_line 284 -start_column 9 -end_column 39 -expression {(st == 6'b111010)} -persistency {AAAApHicLYxLDoJAEESfnsAjeAQEFQiYuOEEuDfiQDQBNaP3j8/Porqmqt80MAP2lCSq48yGgZzgK+gnMvuSlK0po3AOsom+tvuwK3tYyHZEjjy5fP/9bs9VbfdyE1iyU63pQC89ceUmPdKYIvf/hYdd1HuqN4uZFzo=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 312 -end_line 312 -start_column 19 -end_column 50 -expression {~|{(mux_sel == 3'b10), (mux_sel == 3'b101)}} -persistency {AAAAqHicLYxLEoJADAVbT+AR2LEdwR9aVHETSz6DC1cIK8q72065eMlL5yXABmioCKql40jkTK/r7Q9KeUXByankYo1mg/0g+2X3ctiZbZm48+aZ7mD7VyObZTOD+5FFP/l/UBm1ylnTHN0svExeEw18uJF9Ae+TFsw=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 285 -end_line 285 -start_column 9 -end_column 34 -expression {(st == 6'b111010)} -persistency {AAAAmnicPYxLCoNgEIM/PYFH6M6tj9oqRfAm4pPuBOv98fsruMgkk8kEiICOhkyMTFSsvJlVszxQ6jcUvNxKaudqNpOfeiGb60NidmSn58f3/3d1x6K4vXA9VAeLejG/s4kHrchJ7Qj8OQGxXRQP} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 326 -end_line 326 -start_column 5 -end_column 55 -expression {1'b1} -persistency {AAAAzHicJYw7CsJAFEWPO3AJdjYWE+MvEcHG1i2IkxgMiIEINuLePTMW73fufReYAEcqghVpWNOxpXVrnVdKecWSjVfJzt7pDc6VLHkLOUz1RkYuvLjnv392qpabysiQ9YEZB2vOh7fOB72OWlLIotkL90Zf+kv8lL/Pkqckqb1b513nnMCX/Q9cFBvL} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 364 -end_line 368 -start_column 11 -end_column 13 -expression {((st == 6'b10000) & ((4'b1001 != done_i) | run_i | process_i | start_i))} -persistency {AAABlHicdZDLasJQEIY/od27dOlOhS40tt5KoVD0BXyAYhKDAali0nZRfPd+GXSnHCZzZv7LzAnQAt6ZMzRSMl4omJJ7y80bxvbnJEysxsz8FnKH5md7DXdkH9pyU058UrELHTwYj0aHrciJQ+AHurwZPf7EEm+3z48ue0r3WFiN5KeRn1St7qoy/XPnNZplTF1f9lnzy4foF3Xssg+n+q5TKbOQ1zglvrZH343zcNj6jlJ9V6dv62t1DOdMvPJcu5VTNiJ1dM4M4p/cmnnm9R+RsTNA} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 343 -end_line 347 -start_column 11 -end_column 13 -expression {((st == 6'b100001) & ((processing & process_i) | (4'b1001 != done_i) | run_i | start_i))} -persistency {AAABlHicdZDLasJQEIY/C927dOlOhS40tt5KoVD0BXyAYhKDAali0nZRfPd+GXSnHCZzZv7LzAnQAt6ZMzRSMl4omJJ7y80bxvbnJEysxsz8FnKH5md7DXdkH9pyU058UrELHTwYj0aHrciJQ+AHurwZPf7EEm+3z48ue0r3WFiN5KeRn1St7qoy/XPnNZplTF1f9lnzy4foF3Xssg+n+q5TKbOQ1zglvrZH343zcNj6jlJ9V6dv62t1DOdMvPJcu5VTNiJ1dM4M4p/cmnnm9R+PRzM+} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 289 -end_line 289 -start_column 9 -end_column 39 -expression {~|{(st == 6'b101100), (st == 6'b100001), (st == 6'b1011), (st == 6'b10000), (st == 6'b110), (st == 6'b111010)}} -persistency {AAAApHicLYxLDoJAEESfnsAjeAQEfwRM3HAC3BtxIJiAmtH7x4dhUV1T1a8HWABnchLVcGdHx4HgK+g3MvuclL0p4+jsZBN9azexG3tYyTZErnzo/3ewnFXafd0E1pxUbbrQSo88eEoPVKbIa/7hbRf1luIHi94XOw==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 290 -end_line 290 -start_column 9 -end_column 34 -expression {~|{(st == 6'b101100), (st == 6'b100001), (st == 6'b1011), (st == 6'b10000), (st == 6'b110), (st == 6'b111010)}} -persistency {AAAAmnicPYxLCoNQEARLT+ARsnPrJyZKELyJ+CU7wXh/rBfERb/uV9MzQAR0NGRqZKJi5c1smvWBUt5Q8PJXUvuudjP9KQvdXA6J3ZGdnh/f/x7El4qbhelhOljMi/2dTT1oVU7qjeCfE7GYFBA=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 102 121 139 78 95 79 96 130 114 81 82'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 330 -end_line 330 -start_column 32 -end_column 34 -expression {(~(|process_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_0:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicJYxBDoAgEAPHxKuJT0FBkZs/MSIhnPXK46l66HZ30i7QATsBI0UuFjKepC3JT6x4YGbVZdk0s7JG7sTe7CQOo7KRm4OH8vX+34PUU6kNqpYMqQ==} -type {expression} -top -comment {Added by GUI, apply waiver on ' 101'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 11 -end_column 13 -expression {(|start_i & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose) & ~(|(process_i && processing)))} -persistency {AAAAbnicHYtLDkBQEATLgp3EERzh+bNzE/HJizVbh1dk0tMznWogAWYmgtrY6YgMHF6HvtKYT9T0fg2jO8oGvTX72MocCtmNi4Wb8+9BqnKV8TjlC8RSDM8=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 11 -end_column 13 -expression {(~(|start_i) & |run_i & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose) & ~(|(process_i && processing)))} -persistency {AAAAbnicHYtLDkBQEATLgp3EERzh+bNzE/HJizVbh1dk0tMznWogAWYmgtrY6YgMHF6HvtKYT9T0fg2jO8oGvTX72MocCtmNi4Wb8+9BqnKV8TjlC8RSDM8=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 11 -end_column 13 -expression {(~(|start_i) & ~(|run_i) & |:func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose & ~(|(process_i && processing)))} -persistency {AAAAbnicHYtLDkBQEATLgp3EERzh+bNzE/HJizVbh1dk0tMznWogAWYmgtrY6YgMHF6HvtKYT9T0fg2jO8oGvTX72MocCtmNi4Wb8+9BqnKV8TjlC8RSDM8=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 11 -end_column 13 -expression {(~(|start_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose) & |(process_i && processing))} -persistency {AAAAbnicHYtLDkBQEATLgp3EERzh+bNzE/HJizVbh1dk0tMznWogAWYmgtrY6YgMHF6HvtKYT9T0fg2jO8oGvTX72MocCtmNi4Wb8+9BqnKV8TjlC8RSDM8=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 11 -end_column 13 -expression {(~(|start_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose) & ~(|(process_i && processing)))} -persistency {AAAAbnicHYtLDkBQEATLgp3EERzh+bNzE/HJizVbh1dk0tMznWogAWYmgtrY6YgMHF6HvtKYT9T0fg2jO8oGvTX72MocCtmNi4Wb8+9BqnKV8TjlC8RSDM8=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 25 -end_column 27 -expression {(~(|(start_i || run_i || :func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose)) & ~(|process_i) & |processing)} -persistency {AAAAbnicLYs7DoAgEESfFtQewcoaBD903sSIhFjj/RNHYzazszt5AzTARsRKiZOJwkLWleUHXnlkZNbnWbWLWCsPyl7WKYdObKKyc3N9PWh/GQZN/wDA/AwV} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 25 -end_column 27 -expression {(~(|(start_i || run_i || :func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose)) & |process_i & ~(|processing))} -persistency {AAAAbnicLYs7DoAgEESfFtQewcoaBD903sSIhFjj/RNHYzazszt5AzTARsRKiZOJwkLWleUHXnlkZNbnWbWLWCsPyl7WKYdObKKyc3N9PWh/GQZN/wDA/AwV} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 342 -end_line 342 -start_column 25 -end_column 27 -expression {(~(|(start_i || run_i || :func_abr_prim_mubi_pkg::mubi4_test_true_loose_1:abr_prim_mubi_pkg::mubi4_test_true_loose)) & |process_i & |processing)} -persistency {AAAAbnicLYs7DoAgEESfFtQewcoaBD903sSIhFjj/RNHYzazszt5AzTARsRKiZOJwkLWleUHXnlkZNbnWbWLWCsPyl7WKYdObKKyc3N9PWh/GQZN/wDA/AwV} -type {expression} -top -comment {Added by GUI, apply waiver on ' 106 107 108 109 110 111 112 113'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 352 -end_line 352 -start_column 21 -end_column 23 -expression {(~(|start_i) & |process_i)} -persistency {AAAAbnicHYu5DYBADASHhAyJEiiBHy6jE8SjEzGkFM9wstZrr2aBDFgI1GrnYCAycXqd+kZnHmgZ/Tpmd5St9d7sZxtzKGV3blYertSDXBXJX6f6AMRhDNA=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 119 120 118'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 352 -end_line 352 -start_column 21 -end_column 23 -expression {(~(|start_i) & ~(|process_i))} -persistency {AAAAbnicHYu5DYBADASHhAyJEiiBHy6jE8SjEzGkFM9wstZrr2aBDFgI1GrnYCAycXqd+kZnHmgZ/Tpmd5St9d7sZxtzKGV3blYertSDXBXJX6f6AMRhDNA=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 119 120 118'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 352 -end_line 352 -start_column 21 -end_column 23 -expression {(|start_i & ~(|process_i))} -persistency {AAAAbnicHYu5DYBADASHhAyJEiiBHy6jE8SjEzGkFM9wstZrr2aBDFgI1GrnYCAycXqd+kZnHmgZ/Tpmd5St9d7sZxtzKGV3blYertSDXBXJX6f6AMRhDNA=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 119 120 118'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 362 -start_column 43 -end_column 45 -expression {(|start_i & ~(|process_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_2:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLEIwEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWq5Ayv} -type {expression} -top -comment {Added by GUI, apply waiver on ' 125 126 127 128 129'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 362 -start_column 43 -end_column 45 -expression {(~(|start_i) & |process_i & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_2:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLEIwEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWq5Ayv} -type {expression} -top -comment {Added by GUI, apply waiver on ' 125 126 127 128 129'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 362 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & |run_i & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_2:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLEIwEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWq5Ayv} -type {expression} -top -comment {Added by GUI, apply waiver on ' 125 126 127 128 129'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 362 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & ~(|run_i) & |:func_abr_prim_mubi_pkg::mubi4_test_true_loose_2:abr_prim_mubi_pkg::mubi4_test_true_loose)} -persistency {AAAAbHicHYs5CoBAEARLEIwEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWq5Ayv} -type {expression} -top -comment {Added by GUI, apply waiver on ' 125 126 127 128 129'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 362 -end_line 362 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_2:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLEIwEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWq5Ayv} -type {expression} -top -comment {Added by GUI, apply waiver on ' 125 126 127 128 129'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 373 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & |run_i & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_3:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLMBIEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWrCwyy} -type {expression} -top -comment {Added by GUI, apply waiver on ' 136 137 138 134 135'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 373 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & ~(|run_i) & |:func_abr_prim_mubi_pkg::mubi4_test_true_loose_3:abr_prim_mubi_pkg::mubi4_test_true_loose)} -persistency {AAAAbHicHYs5CoBAEARLMBIEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWrCwyy} -type {expression} -top -comment {Added by GUI, apply waiver on ' 136 137 138 134 135'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 373 -start_column 43 -end_column 45 -expression {(~(|start_i) & ~(|process_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_3:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLMBIEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWrCwyy} -type {expression} -top -comment {Added by GUI, apply waiver on ' 136 137 138 134 135'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 373 -start_column 43 -end_column 45 -expression {(|start_i & ~(|process_i) & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_3:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLMBIEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWrCwyy} -type {expression} -top -comment {Added by GUI, apply waiver on ' 136 137 138 134 135'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 373 -end_line 373 -start_column 43 -end_column 45 -expression {(~(|start_i) & |process_i & ~(|run_i) & ~(|:func_abr_prim_mubi_pkg::mubi4_test_true_loose_3:abr_prim_mubi_pkg::mubi4_test_true_loose))} -persistency {AAAAbHicHYs5CoBAEARLMBIEn+Ktm/kT8WAx1nQfb2lQ0zNNDZABC4Fadg4GIhOn22ludPaBltGrY3ZG3drs7T63sYdKd+dm5eH6/6CQUnIS6QWrCwyy} -type {expression} -top -comment {Added by GUI, apply waiver on ' 136 137 138 134 135'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3.sv} -start_line 241 -end_line 241 -start_column 23 -end_column 25 -expression {(|process_i & ~(|(!processing)))} -persistency {AAAAbnicJYxLDkBQEASLhbUjWFnj+e7cRPAi1tw/Ucikp2cqPQMkwMxEpTZ2Og4GolPUV4J8oqF3C4z2w2ylt7I3W8shN7txsXBzfnf/71RllFbxAMDtDBQ=} -type {expression} -top -comment {Added by GUI, apply waiver on ' 50'} -tag {*}





