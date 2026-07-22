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


check_cov -waiver -add -type {*} -instance {abr_sha3_pkg} -comment {Added by GUI, apply waiver on instance 'abr_sha3_pkg'} -tag {*}


check_cov -waiver -add -type {*} -instance {u_state_regs} -comment {Added by GUI, apply waiver on instance 'u_state_regs'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 80 -end_line 80 -start_column 34 -end_column 67 -expression {u_wrmsg_count.gen_cnts[0].decr_en} -persistency {AAAAsnicVY27DoJAFEQPP0FNZwOJLoRHZ+FfGLMBZAMxMSJ2hH93uFZmMtm9s+fOAhFw5khLgZNaOiqpISdQaw56dZpLnZ05MCi/S7XlTh2xbb7xLIy657yM+f2w+8LKiYN1pCT0PPmIn7ny4MamLJP/qUXMoC7PtBNf87IYaA==} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 270'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 88 -end_line 88 -start_column 32 -end_column 34 -expression {u_wrmsg_count.gen_cnts[0].uflow} -persistency {AAAAdHicHYzBCoAwDEOfCOIXePbmVTbR7eafyIYWj6L/D4YSQps0KdAAOzOFhSAUKpuQiRhJ2nQN0qtmdRqX/FNI7gf9GLz5cvBxa488noFW7MWOSe3xBzxHDgU=} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 277'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 88 -end_line 88 -start_column 32 -end_column 34 -expression {u_wrmsg_count.gen_cnts[1].uflow} -persistency {AAAAdHicHYzBCoAwDEOfCOIXePbmVTbR7eafyIYWj6L/D4YSQps0KdAAOzOFhSAUKpuQiRhJ2nQN0qtmdRqX/FNI7gf9GLz5cvBxa488noFW7MWOSe3xBzxHDgU=} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 301'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 89 -end_line 89 -start_column 32 -end_column 45 -expression {(~u_wrmsg_count.gen_cnts[0].uflow & u_wrmsg_count.gen_cnts[0].oflow)} -persistency {AAAAinicHYy9DkBAEIQ/0apVCp3WHfHTeQul3IULnaAT725ymUx2Z3ZmgQSYqHG0WMHh6YWRhsAgHXS10p2mjwxs8ldhiL7Vjzw2LxZudu0NZ8xAKmZiwcvMIe9R4sVQqWH4hPIHsugSow==} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 279'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 89 -end_line 89 -start_column 32 -end_column 45 -expression {(~u_wrmsg_count.gen_cnts[1].uflow & u_wrmsg_count.gen_cnts[1].oflow)} -persistency {AAAAinicHYy9DkBAEIQ/0apVCp3WHfHTeQul3IULnaAT725ymUx2Z3ZmgQSYqHG0WMHh6YWRhsAgHXS10p2mjwxs8ldhiL7Vjzw2LxZudu0NZ8xAKmZiwcvMIe9R4sVQqWH4hPIHsugSow==} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 303'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 100 -end_line 100 -start_column 34 -end_column 41 -expression {(~u_wrmsg_count.clr_i & u_wrmsg_count.set_i)} -persistency {AAAAfnicLYxLCoAwDESf4AFcufYI0orWnTeRFltcuBAVz+8QZBiS+SRABSz0RAacEElMwoynEKSLUic9aiZjIcvfhGC+04/WLi9WbnbtntM6UP9slGQeNV4lB90H3YMQow==} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 285'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 125 -end_line 125 -start_column 3 -end_column 32 -expression {1'b1} -persistency {AAAAqHicTY1JDoJQEEQfl2DtEcjHKGpIuIcxBsSvbtCIC4/vs92YSg9V1QNQAB0VPUuS6BlYiw01mUaedZN8ZR0iMmf1UTShJ2+UsfnkyMzVvuYRM78P39jKZ3HjwsSCk/nl/OS1d3R31fbPGdn778DuA0X1GDc=} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 318'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 138 -end_line 138 -start_column 3 -end_column 39 -expression {1'b1} -persistency {AAAAtnicPY1BCsIwFESfl3DtESQVWxGhy95CWpuoGw2tuPLwvkaQYZLMn5kfYAW0bOnZEUTPQC0OVCQaddIN6r33UJiIzkfRlHlwx7o0J87M3HxX5JL5/bCwU8/izpUHG7dk3uajraWXPaN+1H3pn+Tnn0o89S+6xy/GxRuu} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 319'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 153 -end_line 153 -start_column 13 -end_column 61 -expression {(strength_i == 3'b1)} -persistency {AAAAznicJY5LD8FQEIU/f8LaDkstSkQiscTGxkKEtrceUY9Q/99XMpmZM+ecO3eABjAjZUxGsPdJGBBRWI+yBUNiY+QUxJFcT1cqrlGtJe5oymS82PPmLI55WgP/H+o8qJc8yLnqqrXw85dcuJkVLabmyg0n5jo/3GU3tOmw8JLcSH29tlbOW5beE3nNji6TLzjVHgk=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 3 7 9 11'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 155 -end_line 155 -start_column 13 -end_column 61 -expression {(strength_i == 3'b11)} -persistency {AAAAznicJY7LDsFgEIU/L2Fth6W2lIhEYomNjYUIvblEXUK9v6+VycycOef88w/QAuYkTEjJ7RExQwIK60m2YERojJ1ycSA30JWIa1RrsTvaMilvDny4iENe1pz/D3Ue1UueZNx01Vre+Euu3M2KDjNz7YYzC51fHrJbuvRYeklmJL7eWCvnHavmsog9faY/ORYeEA==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 3 7 9 11'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 156 -end_line 156 -start_column 13 -end_column 61 -expression {(strength_i == 3'b100)} -persistency {AAAAznicJY5LD8FQEIU/f8LaDsu2KBGJxBIbGwsRqq1H1CPU//ddMpmZM+ecO3eABjAlY8SBwt4jpU9MaT3KlgxIjKFTIY7lIl2ZOKCgpe5oyhx4sePNWZzwtBb8fwi5V694kHPVFbTi56+4cDNrWkzMpRtOzHR+uMuuadNh7iW5kfl6Za2dNyy8MvKmLV3GXzjfHgk=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 3 7 9 11'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 158 -end_line 158 -start_column 16 -end_column 38 -expression {~|{(strength_i == 3'b0), (strength_i == 3'b1), (strength_i == 3'b10), (strength_i == 3'b11), (strength_i == 3'b100)}} -persistency {AAAAmnicJY3LDoJQDEQPP+HaHRsWykM0xsQ/McDFQMRAkP+P52qaaaczkxZIgDsNF1qCs6SmIqe3P1V7ThTW2S3Ic7WjqUYeWfRqb+xUWlYefBjkBYs98P8QkelPzHS8TEUv/PITI2+xsecmUg5cv+HPFMM=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 3 7 9 11'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 343 -end_line 349 -start_column 29 -end_column 12 -expression {((st == 7'b111100) & sent_blocksize)} -persistency {AAABnHicbZA5DsIwEEU/LQdAlHS0JGEVi6iokSgooyQ2IYIAImzH5xloAGvk2ez/ZmRJNUlzJRoplSF2NVBPoSx+Q9eqrwgbUhnykF7Aq4TcZe5uAKNBJ9VZsSptySOd8EbvCe7UubfKVehANVHLY5UuEAzZlLOiWsK0zC700BpiQW+MfubV73ibYQlZjPLKrFjHDy9Qmx1cdISFl7BhhxLNN+lG3DPb/JA6L9LQS8pQuP+440uouXeL5p/OsjNznobPMxk=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 349 -end_line 353 -start_column 18 -end_column 12 -expression {((st == 7'b111100) & ~sent_blocksize)} -persistency {AAABFHicbY7NDsFQEIU/Ww9gbWfdFiWNxMpa4gGk3FvETwQRj++7xEaaycyc+TlnBugAc2qmbAjmISUjcqKxsRsZU2gTqyDO7WVu1eKE0qxUo2dnw401d/bigqsx8L2QvOs8suPAxWpIv8XuPFQIopm+slqqGb194EUlb9HKa2SeZR7d3Wq1aM3TfJL508sY+EPK1efjf5XoZ+ENUfYiKw==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 356 -end_line 364 -start_column 21 -end_column 10 -expression {(st == 7'b1001100)} -persistency {AAAB2nicjZA7TwJBFIU/W0sKakpJaFyQR9DEkobExIJyszgDbAAl7pr48/12sEDXwtzM3HMf59w7A1wBjxTMWBP0IybckRG9N2YjY4ba1CiIM3O3dhXiBjW1iRpdM2veyanYiYecvAPnCc25th7ZUvJqNKX3yyqrB/lHPvg0fvAsE35SNzq/FM/lLlrc0mqPG/b2vWiFKNe/qXZSNVJ7cvv69l3uMW5pnXep7Q7fWzwbLeVUWiEzpi0GLVZUMSR/SK/5Oen+n5MuX7tyXmlunn7473nQaWe/AIfZPes=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 359 -end_line 361 -start_column 32 -end_column 12 -expression {((st == 7'b1001100) & keccak_complete_i)} -persistency {AAAAznicbYxJCsJAEEWf4soDiEuvYGIGEcELuPIA0qHLYSNi5/74slaKX/2H/gXMgBOJPQPZd0dHQ0W4b7pBS+30qiyv9Lb+SvKJTVnnjZXOwIcrhYe85u3OJnOxEEvz4M6Tl6pl82cKoxey7CguqrOd4iSbwcHm+qcVXrTzBQ9eGOs=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 361 -end_line 363 -start_column 18 -end_column 12 -expression {((st == 7'b1001100) & ~keccak_complete_i)} -persistency {AAAA0nicbY3BDgFBEESfqw9w9gt2scRKfILEwVF2M425iFgHn+8NN5FO91RV91QBI2BHx5qe5DunYUFFOM+qwZLaWsmSuFKbedWJCyq7Ro+JSs+DEwNXcc3dmfgmlB67Dy5kbrKW6Z8aeOqQRFv7INvrGWZnXhx1zGqbT97v39A3vQGJ6BoJ} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 340 -end_line 354 -start_column 17 -end_column 10 -expression {(st == 7'b111100)} -persistency {AAAC5HicrZG9TwJBEMWfraUFNZ2QUMiHghGNsbAzMbGwvNzdHrjhDoiIGv96f7NnAezZGDPZna99b97NSTqSdKtUl8rk8CONda6BCu4Z1UIXGmITMkc8oNbnVUpskfXGcLSoZHpVoo1eiIdaczvVE+wc0y80l9eSbKL2gW3oluArbfVJfs15CPEjvAXzPfEV2LsI6+m21QkcS73BksG1Uq4FNa8v6l1e7CqYRiy1CkO7n/lPZLvTn/kmT81U3DTiF7zNsZQoAbllVoKSmq+vUzSYN4b7RoYZGiow+0zv+JLZ7oDpLDDF2zTLQdgf+eCuYJ03quhFONuhC74MG93f2+gPe/uvr60Vt35RLJ3E1W/mjl82} -type {branch} -top -comment {Added by GUI, apply waiver on ' 68 69 70 74 75 60'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 412 -end_line 414 -start_column 41 -end_column 12 -expression {((st == 7'b1111) & ~sent_blocksize & ~process_i & keccak_complete_i)} -persistency {AAAAznicbYxLCsJAEESf4MoDiEuvYKL5IIIXcOUBZMK0n00Qx/vjC7hTiu6p6poqYAYcSfQMZN8tLTsqwn31GjTUolNleeVt468kn9jktXYsvQy8uFC4y2ue7qwz/85CP7jxYFQ1rP+g8LYhyw7OWXUyU0QyGexNrn5SYaOZDxAwGO0=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 104 105 106 107 95'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 414 -end_line 416 -start_column 18 -end_column 12 -expression {((st == 7'b1111) & ~sent_blocksize & ~process_i & ~keccak_complete_i)} -persistency {AAAA1HicbY3BDgFRDEWPrQ+w9gtmMESIH7CysJQ36cNsRDz/H+exE2na3nvb2wIjYE9iTU/Y53QsaMjWi2pmSWusZCFu1GZuJXFFddZ5Y6LS8+RM4SZueViD74eaY+eZKwN32Y7pnyi8vBCirXmUHfQUI+nMnOyD6ubz8dedvRxvwtsaYg==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 104 105 106 107 95'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 407 -end_line 412 -start_column 33 -end_column 12 -expression {((st == 7'b1111) & ~sent_blocksize & process_i)} -persistency {AAABAHicbY5LCsJQDEWPDl2AOHTmTGirrSKCSxBcQGl5tRX8Yd0/nifOLCHJTW5uEmAEHKjYUhPMKwrWpDTGs92GnEzbWAVxai9xqhJHFLnCHVM7NS9KejpxxtMYZMY/n8g3tFy4Wy2ZD1jP2w1BtNdPVsfvlp2KfFDR8eDqRMlNdftTJiy8FnNUzv5UjT945QNAJR23} -type {branch} -top -comment {Added by GUI, apply waiver on ' 104 105 106 107 95'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 403 -end_line 407 -start_column 29 -end_column 12 -expression {((st == 7'b1111) & sent_blocksize)} -persistency {AAABEHicbY47DsJADEQfLQdAlHTUSSABIRAXoKKgjBJlCZH4iXB/8VbQEVm2x+Od8QIjYE/FmprGvqBgSUqwnmUDOZmxcmrEqVziq0ocUdwVekxkal6U9FzEGU9rw/dCzLH7QEvH3WnHbCB63jo0oq15dDqo6Y1KZeBk72Q3OuSDDhceXHUoualqf04Jc6/HHpXTP1XwT179AMsOIQo=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 104 105 106 107 95'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 399 -end_line 417 -start_column 22 -end_column 10 -expression {(st == 7'b1111)} -persistency {AAADyHicrZHNS8NAEMWfV48eevbkB4jQD1tFFPHgQSgIHgoeDEmzsaGxDY2K+Nf7m91CpYlYUYbNfOy8mfeykrYkXSnWmRKl+J4GOlFHjm9G1amvLnZKlhJ3qLXpioktsrsBM1pUEi0UqdKEuKuSb6qwwc42905PyjUj62l3zSpuC/DPetU7+QVn6OMbMJnmOgf3WMM55hmqYnZCf7bEhkqkN3gUTEiJc+p72OrWWC70wo112Ybr2obczzzwDGf0Ruwp4DPWlFquD+qHdHzVd1mbEjQaOl0yvCcbgqmwGKTTCJ9TNR79xgkT9hZeS1AQJrW1z3bzhrxt/Eep94VXsdJUot6UBBb2h9aVHG+o5M6/99+YP/yC+ZRsjMVEEX7O3JIuBxfXqKSZ109vYryONuD1v6/f+majtFOvfgJ0hIHG} -type {branch} -top -comment {Added by GUI, apply waiver on ' 104 105 106 107 95'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 495 -end_line 499 -start_column 24 -end_column 10 -expression {(st == 7'b110011)} -persistency {AAABAHicbY6xCsJAEESfraWFtYVgnUSNIoKVvyEJd1ELjST+P77TNIostzO7Oze7wAg4ULGlJohLSlbkRHNjN7KmMDZWQZ7by1RV8sTSrNRjaqem40TPRV7wMAc+G9IbO4+cuXK3mjP7iZ6nv4NsP1Q7dcc/uuTciVF9I97EaKejfV/QDh4ZC3cmTE6TL5foFeEFxaUgHQ==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 157 160'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 501 -end_line 505 -start_column 16 -end_column 10 -expression {~|{(st == 7'b1000010), (st == 7'b111100), (st == 7'b1001100), (st == 7'b100101), (st == 7'b1111), (st == 7'b1111010), (st == 7'b11001), (st == 7'b1101001), (st == 7'b1010111), (st == 7'b110011)}} -persistency {AAABGnicbY65CgJBEESfqaGBsZnxeq0iion+gOayy8yq4MXq/+MbFwRFhu6q6qN6gBawomBGSRBH5IwZEM2V1ciEoW+qCvKBtcypQp5Y6uV6dK2U1Ox5cJQPuZsDzYUUbfuRAyeuqiW9n/fg6XaQLYytaud8zeW9UXBmraq5GXMdNn8c0s1ajDpV4kWMn629uXHP6PubhMmp8+USvRZeA1YlXQ==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 157 160'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 630 -end_line 630 -start_column 19 -end_column 39 -expression {(sel_mux == 3'b10)} -persistency {AAAAlnicJY1JCoNAEEVfwDNk7S4uHRIHQsCbiNIOG0kwq9ze14Smql7/XwNwAXpGOiaC9U7Dg5LZvKjO1FS+1l+QS7XCrlGOFL3GHVeViYOBL5tc8TEH/hcSI2PXW+043Bq9n/wm5WUU3JxPyXmehIETew==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 843 -end_line 845 -start_column 27 -end_column 8 -expression {(rst_b & zeroize)} -persistency {AAAAxnicTYyxCsJAEESf2llZWdtZJzGJYgT/JCTcaQSRkIjf77tGZNnZ2ZnZBRbAlY4TPcF5oKYkJ4o31UhFYR3dgjxXy0x18sSSV/tjq9Iz0TIzyAtGMegs7ZW91o/cefByq9j91czb9CS2fGRPU0G94SJm7L1N8+zl5ncV/WTqC398GJA=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 858 -end_line 860 -start_column 29 -end_column 8 -expression {(rst_b & ~zeroize & ~start_i & process_i)} -persistency {AAAAyHicTYxNC4JQFERPtGvRsrU7t6mV9gX9E9HeK4MoSej3d4SIGN68uTN3LjABTjRsaQn+K0rW5ET5ohvZUIjKKahzvcytRj2qMSu9sdBpeVEz0KkLejmYTL9vZh65cuPhtCP5Q2/zydl8EDVvu3c3g9mBo5yR2k9Ysrc9/zWj18IHwvcZQw==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 618 -end_line 618 -start_column 19 -end_column 59 -expression {(sel_mux == 3'b10)} -persistency {AAAAvnicJY1tCsIwEESfeIf+9gq21SoieARvUBKTYFFB/Dq/L8qyuzOzwywwAw4EtkSSu2dgRUt2FtXMms7ayJK4VVvqCuKK6m0wo1GJPBh5chZ33J2J/4e5feStVn+8TK2+rH+SX2XRa7GqtmBvFx03Lxe1kxVEI5+ffzJn9wWDlBzA} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 858 -end_line 858 -start_column 14 -end_column 27 -expression {(rst_b & ~zeroize & ~start_i & ~process_i)} -persistency {AAAAinicLYxNDkRgEESfxBmsLCxZYsbPzk0EH5lZEe6feBKpdHV1VaeACBiY6JkJ7g8tXypWedNdaahF5xXUlV7p16R+1JO1diQ6MycjFz91zSEHk/idlL8dGbnJyc5i9yVG/eIGmA0SLg==} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 856 -end_line 858 -start_column 27 -end_column 8 -expression {(rst_b & ~zeroize & start_i)} -persistency {AAAAynicTY3JCsJAEESfV0+ePOfmOYkmxgX8k5A44wJiggG/3zcIIsV0V1d19QAz4ERHQ0+wr6nZUBCtF9VIRSm2TkFeqOVudfLEkld7Y6nS86Jl4iYvGa2B7w/pzfUjV+48nXZkfxhNDpz1J9HyNvtwM+gdOFpzVuZT35te/JLRa259APRKGWI=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 854 -end_line 856 -start_column 27 -end_column 8 -expression {(rst_b & zeroize)} -persistency {AAAAynicTYy7DoJQEESP0llZWdPRCqj4TPwTAt4rmhglkvj9HhpjNjs7O7OzwAQ407CjJThXVKwpiOJVNbKhtLZuQV6o5V418pGNXuWPhUrLm5qBm7ykF4PO1E7smX6k487TbU/6V73JFxf9war5mH14GfSOnMSczHzKkoPp+S8Z/ebVF/VaGWQ=} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 606 -end_line 606 -start_column 19 -end_column 54 -expression {(sel_mux == 3'b10)} -persistency {AAAAtHicNY3RCoJAFERPP+Fzv6CWFiL41G+Iy64k9CBl1Od3tohl5s7ODPcCO2Bg4kwgOg+0HKlI8qybaKh9J39RXemVtiZ1Vjlr3VHoBO6MPLiqa1Y58ruQcTFJNhb9m73A053z1xt5yfn+Jvb0YtVJ5gtv83/WfQBqBBrF} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 847 -end_line 849 -start_column 29 -end_column 8 -expression {(rst_b & ~zeroize & ~start_i & process_i)} -persistency {AAAAxHicTYzLCsJQDESPuHPh0rU71221VVTwT0pLrg8QkVb8fs8FEQmZTGYmASbAiY4dPeFc07ChJIln1URNZW3dQl6qFaY6eWbZa/yxUOkZaBm5yiueYuhMvz3TT1y48XCrWf7VyMv0ILa8ZXdToX7gKBasvM1z7+X8d5X8FB9OvRhv} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 847 -end_line 847 -start_column 14 -end_column 27 -expression {(rst_b & ~zeroize & ~start_i & ~process_i)} -persistency {AAAAinicFYyxDoJAEEQfwW+woqCU0kM87fgTwnkQqTDw/4nvspnZ2ZnNABUwMvMmkd0PIgOBRV51F570zssrq4Pe3a9ZXVTJoh1XncTBxMlX3fOTs0ktLqJhs6PlZnKw87H7dCb97g+X6BIt} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 764 -end_line 764 -start_column 18 -end_column 47 -expression {~|{(msg_strb == 7'b0), (msg_strb == 7'b1), (msg_strb == 7'b11), (msg_strb == 7'b111), (msg_strb == 7'b1111), (msg_strb == 7'b11111), (msg_strb == 7'b111111), (msg_strb == 7'b1111111)}} -persistency {AAAAqHicLY1BDoIwFESf4Q6u3blFUBGMCTchxda4MMaArox390FIM7/TN5NfYAW0BGp6oveeigMFyXmTJo6UnpOvqC9kO1tBP7kpq9yxlvQMdIzc9SUvZzTJFjVu+PDkuiTd/N9bbbioLV9JshXsPUwaWc6P8x8ZYBdq} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 845 -end_line 847 -start_column 27 -end_column 8 -expression {(rst_b & ~zeroize & start_i)} -persistency {AAAAxnicTY09C8JAEESfrZWVdTpbk2iiqOA/CQl3foCEkIi/P+8QRJabnZ2d2QMWwJWWIx3BvqNmT0EUb6qRitI6OAV5oZbrauWJpV3tjbVKx0jDxENeMoiB7w/pLd1H7jzpnSqyv5p46x7Fho/spSuon7mIORuzGVtOJle/VPSSrhl+ShiM} -type {branch} -top -comment {Added by GUI, apply waiver on ' 204 255 261 194 262 263 264 184 252 253 237 254'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 153 -end_line 153 -start_column 13 -end_column 61 -expression {(strength_i == 3'b1)} -persistency {AAAAznicJY5LD8FQEIU/f8LaDkstSkQiscTGxkKEtrceUY9Q/99XMpmZM+ecO3eABjAjZUxGsPdJGBBRWI+yBUNiY+QUxJFcT1cqrlGtJe5oymS82PPmLI55WgP/H+o8qJc8yLnqqrXw85dcuJkVLabmyg0n5jo/3GU3tOmw8JLcSH29tlbOW5beE3nNji6TLzjVHgk=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 294 -end_line 294 -start_column 5 -end_column 15 -expression {1'b1} -persistency {AAAAgnicJY1bCsJADEWPXYP47RbaUWsphe5EZsiUfoq6fzxDCTe5j5AAJ2AlM1EI542ROwPVvulWHiTrqQr5oNe7leWNtWz0xkWn8OHFl12eeNuD40MnziY/8+DKIpqa/wtgEGM=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 155 -end_line 155 -start_column 13 -end_column 61 -expression {(strength_i == 3'b11)} -persistency {AAAAznicJY7LDsFgEIU/L2Fth6W2lIhEYomNjYUIvblEXUK9v6+VycycOef88w/QAuYkTEjJ7RExQwIK60m2YERojJ1ycSA30JWIa1RrsTvaMilvDny4iENe1pz/D3Ue1UueZNx01Vre+Euu3M2KDjNz7YYzC51fHrJbuvRYeklmJL7eWCvnHavmsog9faY/ORYeEA==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 156 -end_line 156 -start_column 13 -end_column 61 -expression {(strength_i == 3'b100)} -persistency {AAAAznicJY5LD8FQEIU/f8LaDsu2KBGJxBIbGwsRqq1H1CPU//ddMpmZM+ecO3eABjAlY8SBwt4jpU9MaT3KlgxIjKFTIY7lIl2ZOKCgpe5oyhx4sePNWZzwtBb8fwi5V694kHPVFbTi56+4cDNrWkzMpRtOzHR+uMuuadNh7iW5kfl6Za2dNyy8MvKmLV3GXzjfHgk=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 158 -end_line 158 -start_column 16 -end_column 38 -expression {~|{(strength_i == 3'b0), (strength_i == 3'b1), (strength_i == 3'b10), (strength_i == 3'b11), (strength_i == 3'b100)}} -persistency {AAAAmnicJY3LDoJQDEQPP+HaHRsWykM0xsQ/McDFQMRAkP+P52qaaaczkxZIgDsNF1qCs6SmIqe3P1V7ThTW2S3Ic7WjqUYeWfRqb+xUWlYefBjkBYs98P8QkelPzHS8TEUv/PITI2+xsecmUg5cv+HPFMM=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 400 -end_line 400 -start_column 9 -end_column 27 -expression {(st == 7'b1111)} -persistency {AAAAknicLYzBCoJQEEVPfkTrFv1AvtJChFbt+oZQ3pMCo1CEPt9jyHBnztw7DLABrjRcaInOIyUncpK9000UBOvsFuVc7+BVIy+0ZKU/tjotAw9GnnLga48m2aq9SaL34s3Ejx21uv/5xsv/H6oZNHYTng==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 401 -end_line 401 -start_column 9 -end_column 48 -expression {(st == 7'b1111)} -persistency {AAAAvHicRYzRCoJAFERPfUTPPvWeWhYR9AX+wqKsVlARmn2/ZymIy52dnZk7wAI403CgJfqWVGzJ6cRetWNH4ez9RXmutjHVyBNLXmXHSqVlIDBylRe8xKiz/G1t11P/YeJidrIx4+R+lcDHizs3r4KYsXb+buobeOuk1HEGG4gbYA==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 341 -end_line 341 -start_column 9 -end_column 29 -expression {(st == 7'b111100)} -persistency {AAAAlnicJY1dCoJQEEZPLcLnHn1VK5UI2oDgDkK5NxQUpAhavkdjmJkz3/wBB+BBR01PMJ8puZATjS/VyJVCq6yCnKtlTnXyRluv9Eai0vPmyYdBLliMgf+Ho57aiUxOzHz5ceKuNzu3bkY/jPJtBYaHFIs=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 404 -end_line 404 -start_column 11 -end_column 32 -expression {((st == 7'b1111) & sent_blocksize)} -persistency {AAAAmHicJY05DoNQDAUnOURqarpA2IQi5QKpKCijjz5bhwL3VwZFlu3xe5YNXIAXgYaBaH9QUZAxWifVkZLcqJ2inKnd3QrySadXeeOmMvDlw84i52zWyP/D1Ux1Dv1IwtPsnN7e343ALPX2VbX9AabxFLM=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 344 -end_line 344 -start_column 11 -end_column 31 -expression {((st == 7'b111100) & sent_blocksize)} -persistency {AAAAlnicJY3BDoJADEQffIRnj14BdSHExE8w4cDRQHaN3Ah48PN9G9O0nc5MW6AA7kx0zET7mcCFmmR9ySauNEbrFMW1XKVrEmeUteCNg8zMxpOdt7hhtUb+H0rzpPJRjxy5mYPTw43k5YUvo/5Frv8BffQUWg==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 406 -end_line 406 -start_column 11 -end_column 28 -expression {((st == 7'b1111) & sent_blocksize)} -persistency {AAAAkHicFYxLCoNAEAVLiFdwHbLJejRRgwjeRJQxcWFI0PuDNTSv+3X1B8iAgYkXM9H6oOFJyWJ+SxdqKqO1i/pSFtya9MmlWeOPQjKzM3Kw6iv+5ujkonJ1k//YZCNftz5c6VXg7mWq3QkHThI+} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 346 -end_line 346 -start_column 11 -end_column 32 -expression {((st == 7'b111100) & sent_blocksize)} -persistency {AAAAmHicJY3RCoJAEEVP4Df43Fvgm1ppROCfyOoqQaBi9P+dRYaZe/bOcBc4AR2BBwNRvdJwo2JyzroTd2qr9RXlSq/0KsiJ0q4xI9cZ2On58pZrNmfk+CGzCz6mjVaQem9/LOrKmZddcjEh6fMPrXsT2Q==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 408 -end_line 408 -start_column 11 -end_column 24 -expression {((st == 7'b1111) & ~sent_blocksize & process_i)} -persistency {AAAAiHicHYxJCsJAEEVfzB2yyCpXyGA6IoEcQfAAIU23uBT1/vhail/1JwqogI2DC5HknQicGcjuh25mZnQWVZIPer2tQ15YyYI/Gp3Im50PT/nIy51MTqIWrcnXPNGxirvq9u9cf3EVEWA=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 347 -end_line 347 -start_column 11 -end_column 36 -expression {((st == 7'b111100) & sent_blocksize)} -persistency {AAAAoHicFYzRCoJQEERPQb/Qs2+96lVTiaA/kWvXUCqQBL+/I8vszs4MAxyAB5GOgeStaKgJjO6X6siV0mn9kjyoFaaifGe719hxVhn40bMyyUsWd9I5ipMINqx8TbxtfTpR1rN5P8xmM+6i4GJTRs7tD2MtFXQ=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 411 -end_line 411 -start_column 11 -end_column 28 -expression {((st == 7'b1111) & ~sent_blocksize & process_i)} -persistency {AAAAkHicLYxBCoNADEWfC6/gWty4drRVKYI3EWVsu2hpqfeHvgEJSX7eTwJkwMzKyEa0d/RcCOzWu3TnSmsMTlEdZI1bqzqp5PX+KCQbPxYOnuqWrzXq5GdW8g8v2cLbrQclk9lQe5n67Q8HeRI/} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 413 -end_line 413 -start_column 11 -end_column 28 -expression {((st == 7'b1111) & ~sent_blocksize & ~process_i & keccak_complete_i)} -persistency {AAAAkHicLYxLCsJQDEVPJ12C4+IO7MenFMENOOoCyiupOhTr/vE8KJckJ/eGABVwJ3NlIZw9iYGW1f7UXTnTqYtbyK3eyassFypZ8sdBZ+HLzMZb7vjYw6Te62jyMw8abtbk9vD/pjIvafwDBxUTHw==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 348 -end_line 348 -start_column 11 -end_column 29 -expression {((st == 7'b111100) & sent_blocksize)} -persistency {AAAAknicJY1BDoJQDEQfC6/AmoWJa/gqEELCTQj4UReaGF14fd6HNJ1Op9MWyICBiZaZaD1Tc6FiEe+qC1eC0dhFeaVW6prkiaVZ7Y1cZebLyI+nPPARI/uHg3nkxmtz/MW3vgcFvVlycjfVbgUyOhLA} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 350 -end_line 350 -start_column 11 -end_column 27 -expression {((st == 7'b111100) & ~sent_blocksize)} -persistency {AAAAjnicLYxBDoJADEUfHoI1VxCQ0RATj0DCAQyTDtGdURYe30dimrav/7cFKuDGwoVM2HsSJ1qKdVUtDHTG2SnkVu3o1iLvtHvJH7VK5s2dDw+542UNncM/G51NP6SrOTtNXhQ/P/ky/gDflxK+} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 415 -end_line 415 -start_column 11 -end_column 32 -expression {((st == 7'b1111) & ~sent_blocksize & ~process_i & ~keccak_complete_i)} -persistency {AAAAmHicLYy7CoNQEAUn+YjU1nbR+EIC+YFUFpbhyvXVSfT/yQhhObuz5ywLXIAXgYaB6HxQUZAx2ifdkZLcqt2inOndvQrySWdW+eOmM/Dlw84i52z2aHL9KzU5zCMJT9W5vf2/W4FZ6p2rbvsDpyQUtA==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 352 -end_line 352 -start_column 11 -end_column 36 -expression {((st == 7'b111100) & ~sent_blocksize)} -persistency {AAAAoHicJY3RCoJQEERP9A8+99azV8tCBP9Erl0jqSAS/H7PRZbdmZ0dZoED0BO5M5LEmoYLgcn5VJ24Ulk3tyQPaqWuKM8s3xozCpWRPwMLL3nFz5nYPxztYMLCV8fb1IcVZQOr+GHWe6KzS84mZWw3YocVcg==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 357 -end_line 357 -start_column 9 -end_column 29 -expression {(st == 7'b1001100)} -persistency {AAAAlnicLY3RCoJAEEVPfYTPPfqqVioR9AOCfxDKbigoSBH0+R4llpk5e++dXeAAPOio6QnOMyUXcqL9pRq5Ungqb0HO1TJTnbzR5pW+kaj0vHnyYZALFnvQOf4r1YlMJma+/Dhxt5qdWzejP4zybQWGuBSM} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 360 -end_line 360 -start_column 11 -end_column 28 -expression {((st == 7'b1001100) & keccak_complete_i)} -persistency {AAAAkHicFYxLCsJQDEVPHXQJHYs7sB+fRQQ30JELkFdS7VB83T+eEm5ycm8IUAEPMiMz4exJDLQs9rfuwoXOurqF3OqdvcryTnuW/NHozPx4UVjljq89TA6qVieTzTw4cldPt8n/xcp8pNsfBmkTGw==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 362 -end_line 362 -start_column 11 -end_column 31 -expression {((st == 7'b1001100) & ~keccak_complete_i)} -persistency {AAAAlnicLYyxDoJAEEQffIS1pS2gHoSY+AkmFJQGcmekI2Dh5/suMZvZnZ3ZHaAA7kx0zETnmcCFmmR/qSauNFbrFuW1WuXVJM8se8GMg8rMxpOdt7xhtUed8o+Tzkc/cuQmBreHH8nkhS+j94ta/wN+JRRb} -type {statement} -top -comment {Added by GUI, apply waiver on ' 4 42 8 10 12 96 97 61 98 62 99 63 100 64 101 65 102 66 103 67 71 72 73'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 630 -end_line 630 -start_column 19 -end_column 39 -expression {(sel_mux == 3'b10)} -persistency {AAAAlnicJY1JCoNAEEVfwDNk7S4uHRIHQsCbiNIOG0kwq9ze14Smql7/XwNwAXpGOiaC9U7Dg5LZvKjO1FS+1l+QS7XCrlGOFL3GHVeViYOBL5tc8TEH/hcSI2PXW+043Bq9n/wm5WUU3JxPyXmehIETew==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 497 -end_line 497 -start_column 9 -end_column 19 -expression {(st == 7'b110011)} -persistency {AAAAgnicLYxLCsJAEESfOYO49grJqDGEQG4iM/SELEW9P76B0FR1fZoGTsBKZqIQ7hsjdwaqvJlWHiTnqQv1YNZ7ldVNtW70x8Wk8OHFl12deMth0x042/zsgyuLaG7+Awt9EGQ=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 498 -end_line 498 -start_column 9 -end_column 36 -expression {(st == 7'b110011)} -persistency {AAAApHicJY3LCoNADEVP/QjX3XWttj4ohf6JKDPiRizj/4NnLCE5NzeZDHADvkwMzAT5pONFTbQuupGWxujtgrrWq9ya1FnlWeeNUmcmMXKwqht+1sD/h8JsnWQvyejeIjcZdRL79XbnzseseHgt830Cy6YWiQ==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 503 -end_line 503 -start_column 9 -end_column 32 -expression {~|{(st == 7'b1000010), (st == 7'b111100), (st == 7'b1001100), (st == 7'b100101), (st == 7'b1111), (st == 7'b1111010), (st == 7'b11001), (st == 7'b1101001), (st == 7'b1010111), (st == 7'b110011)}} -persistency {AAAAnHicJY1dCoJQEEZPm+jZFQipZRGCL65A30W5RkFlXNs/nUsM38z3M8wAO6Bl4sJMcFbUHClY7DfdhROldVYFeaF3cGuSJ5ay2ht7nZnIyMZdXvKxB/4fEnKTr3kgoxG9avB+5MWDt9tPOlVkFdcf/fYVog==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 618 -end_line 618 -start_column 19 -end_column 59 -expression {(sel_mux == 3'b10)} -persistency {AAAAvnicJY1tCsIwEESfeIf+9gq21SoieARvUBKTYFFB/Dq/L8qyuzOzwywwAw4EtkSSu2dgRUt2FtXMms7ayJK4VVvqCuKK6m0wo1GJPBh5chZ33J2J/4e5feStVn+8TK2+rH+SX2XRa7GqtmBvFx03Lxe1kxVEI5+ffzJn9wWDlBzA} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 504 -end_line 504 -start_column 9 -end_column 36 -expression {~|{(st == 7'b1000010), (st == 7'b111100), (st == 7'b1001100), (st == 7'b100101), (st == 7'b1111), (st == 7'b1111010), (st == 7'b11001), (st == 7'b1101001), (st == 7'b1010111), (st == 7'b110011)}} -persistency {AAAApHicLYxLCoNAEAUrHsJ1dlmriR9CIDcRZUbciGG8P1gjYeiuN+91N3ADvkwMzAT5pONFTbQvupGWxtf7C+par3JqUmeVs84bpc5MYuRgVTf87MGk+Fdrkr0ko3OL3GTUSezX7s6dj1Xx8Frm+wTL5RaK} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 606 -end_line 606 -start_column 19 -end_column 54 -expression {(sel_mux == 3'b10)} -persistency {AAAAtHicNY3RCoJAFERPP+Fzv6CWFiL41G+Iy64k9CBl1Od3tohl5s7ODPcCO2Bg4kwgOg+0HKlI8qybaKh9J39RXemVtiZ1Vjlr3VHoBO6MPLiqa1Y58ruQcTFJNhb9m73A053z1xt5yfn+Jvb0YtVJ5gtv83/WfQBqBBrF} -type {statement} -top -comment {Added by GUI, apply waiver on ' 205 158 159 161 195 162 185'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 764 -end_line 764 -start_column 18 -end_column 47 -expression {~|{(msg_strb == 7'b0), (msg_strb == 7'b1), (msg_strb == 7'b11), (msg_strb == 7'b111), (msg_strb == 7'b1111), (msg_strb == 7'b11111), (msg_strb == 7'b111111), (msg_strb == 7'b1111111)}} -persistency {AAAAqHicLY1BDoIwFESf4Q6u3blFUBGMCTchxda4MMaArox390FIM7/TN5NfYAW0BGp6oveeigMFyXmTJo6UnpOvqC9kO1tBP7kpq9yxlvQMdIzc9SUvZzTJFjVu+PDkuiTd/N9bbbioLV9JshXsPUwaWc6P8x8ZYBdq} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 855 -end_line 855 -start_column 7 -end_column 30 -expression {(rst_b & zeroize)} -persistency {AAAAnHicFYzdCoJgEERP+g5de+ed+JOpWNCbiPYZBYGh4PN3ZNnZ2ZlhgBPwYKRjIngvNNSUzOJLdeZK5bR+QV6qFaZG+cEOr7HjrDKxMrDxllf8xKATubGbqawsPO3cnIHdxJePqYQbd7EgtSUhp/8DCXcUog==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 857 -end_line 857 -start_column 7 -end_column 30 -expression {(rst_b & ~zeroize & start_i)} -persistency {AAAAnHicJY3LCoNQDERPf6Jrd90VfFWLCv0TUa/FgtCi4Pd7LiVkMpkME+ACvBh4MhKcBRUlGbP4Vp15kFu1W5BnaqmuQR5ZvFVmXFVGNnp2FnnOTwz8P8S+q2x8mczcrZ5Dx8pHV0JLJ6bcTImzOQEI3RSg} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 859 -end_line 859 -start_column 7 -end_column 30 -expression {(rst_b & ~zeroize & ~start_i & process_i)} -persistency {AAAAnHicLYzRCoJQEERP9A8++9ZbpJYaKvQnol3FIDAU+n6PIMvOzs4MA5yAFx1PeoL3TsGDlEEcVQdyMqf0C/JULTHVyXe2e4UdkUrPQsvKJM/4iUHnfOxVZWHmbefqtPxNfPmYiqlpxISLLTE3qg0JrhSj} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 787 -end_line 787 -start_column 5 -end_column 37 -expression {1'b1} -persistency {AAAArnicdY1LCoNAEAXLS2TtFeI/hIA3EYdRIrgIDt4/pa6lmZ7X1Y/XQAb0jLwIRP+KlpqCyT5LJxpKq3OK6kL21DWqD3XsWjMeksDGQOKrLvnZI9eF60oybWORr/oCu5nzyQadOR/fvef9B8AKGXI=} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 844 -end_line 844 -start_column 7 -end_column 28 -expression {(rst_b & zeroize)} -persistency {AAAAmHicFYxLCoNQEATLeIesswtk59+gQm4iylMiZBFM8PzWY5iemu5hgAR4MfFkJjhLGipyFnXVXagprNYtyLle5tUkR4pZ44+rzszOyI+3XPBVg8nFTu2HyV9vV0cO6cPmxY2eQc24+yHO7gSvthPO} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 846 -end_line 846 -start_column 7 -end_column 28 -expression {(rst_b & ~zeroize & start_i)} -persistency {AAAAmHicJY3LCoNQDAWnP+HaXaErX60tKvgnolylgotipd/fuUjIyeQkJMAF6Bl5MRGsFTV3CmZ10Z15UBpPuyAXerlboxwpzmpvJDoTOwNf3nLJRw2cH2LenBx6uzrwkzZWN1JaOjXn6oWUjOYPryITyg==} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 848 -end_line 848 -start_column 7 -end_column 28 -expression {(rst_b & ~zeroize & ~start_i & process_i)} -persistency {AAAAmHicLYxBCoNQDAVHeoeu3RW6U2tV2kJvIspXFFyIiufvfCghL5P3QoAE+NLR0BOcDypKcgZ11B14Uli1W5BzvcyrTo4Us8ofV52ejZadSS5Y1WBy+ffd5NDb1JZTWpi9SHnzUTNufojz9QOv6RPP} -type {statement} -top -comment {Added by GUI, apply waiver on ' 238 258 259 260 247 249 250 251'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 470 -end_line 470 -start_column 37 -end_column 39 -expression {(|sent_blocksize & ~(|(~keccak_ack)))} -persistency {AAAAdHicHYw7CoBAEEOfjQewsLay1/XbeRNxWcVS9P7gU8IkmWQYIAMWNmYiSe0Y6WnZ5cN0ZyCIyS3pW7PGq03/ua8b/VGaRG5WHk594JKTTe4Uv9aiegEysQ2N} -type {expression} -top -comment {Added by GUI, apply waiver on ' 140'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_sha3/rtl/abr_sha3pad.sv} -start_line 436 -end_line 436 -start_column 35 -end_column 37 -expression {(|end_of_block & ~(|(~keccak_ack)))} -persistency {AAAAdHicFYw7CoBAEEOfIB7AwtrKXtdv501EWcVS9P7gW0IymWQYIANWdhYOorNnYqDjVC/Tk5EgZreo78xar3Z9cqmb/FGZHLxsfNz6wKNGm1yWsqAR9Q8ykw2L} -type {expression} -top -comment {Added by GUI, apply waiver on ' 117'} -tag {*}


check_cov -waiver -add -source_file {/home/osama-ayoub/Projects/Google/mulan_us_adams_bridge/verification_scripts/keccak/fv_abr_sha3pad/jasper/../../../../rtl/abr_prim/rtl/abr_prim_count.sv} -start_line 81 -end_line 81 -start_column 34 -end_column 67 -expression {(~u_wrmsg_count.gen_cnts[1].decr_en & u_wrmsg_count.gen_cnts[1].incr_en)} -persistency {AAAAsnicVY27DoJAFEQPP0FNZwGFLoRHZ+FfGLMBZAMxMSJ2hH93uFZmMtm9s+fOAhFw5khLgZNaOiqpISdQaw56dZpLnZ05MCi/S7XlTh2xbb7xLIy657yM+f2w+8LKiYN1ZCT0PPmIn7ny4MamLJX/qUXMoC7PtBNf83AYZg==} -type {branch} -instance {u_wrmsg_count} -comment {Added by GUI, apply waiver on ' 296'} -tag {*}





