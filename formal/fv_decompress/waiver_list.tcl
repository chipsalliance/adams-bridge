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

# Source paths are relative to $design_path, the RTL src directory set by the load script.

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
# Copyright (C) 2000-2025 Cadence Design Systems, Inc. All Rights
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


check_cov -waiver -add -source_file $design_path/abr_libs/rtl/abr_piso_multi.sv -start_line 83 -end_line 83 -start_column 17 -end_column 49 -expression 1'b0 -persistency AAABSHicrY/RDcIwDEQPsQZDkDQJ6R+boCSt/xAVsL94tRATUMvx2TnfNZKOkq6qCjoryzSDMueiVYUwugv9rKShSK4wgprXqg4KaJx8Y+ihuzY9wS/ipjeTzT2KexgbExHJAL+D9lpwMDwCtTFdmO3OGaXq3H9p7C9K3A/OiFqj7/73nUygyV9s8COTCCP5vnFnaBy++fs+JzEqKg== -type branch -instance abr_piso_inst -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[3].decompress_inst.mode} == 32'b11) & ~|{(genblk1[3].decompress_inst.mode == 2'b0), (genblk1[3].decompress_inst.mode == 2'b1), (genblk1[3].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type branch -instance {genblk1[3].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[2].decompress_inst.mode} == 32'b11) & ~|{(genblk1[2].decompress_inst.mode == 2'b0), (genblk1[2].decompress_inst.mode == 2'b1), (genblk1[2].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type branch -instance {genblk1[2].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[1].decompress_inst.mode} == 32'b11) & ~|{(genblk1[1].decompress_inst.mode == 2'b0), (genblk1[1].decompress_inst.mode == 2'b1), (genblk1[1].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type branch -instance {genblk1[1].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress_top.sv -start_line 116 -end_line 118 -start_column 26 -end_column 20 -expression 1'b0 -persistency AAABSHicLY/dDcIwDIQPsQADIGZI+pMmb2yCkqa8ISpgf/HZUMv15XI+x5KOkq6KKpq1ElGjqu6cNrKS0U+Ru6wAY9oBFLV4zWp4nNXpWPXUQ7te4Ddx0wdm9xnmklEV+uq/To4aMwt4xDPg0WEXIoLsVdW15rHgEpga/R0TOdOdleAH1MHf38AJlGGbu1bfZnSPjotNbzjPeHTUFX2Db77z6jtuuAWqoURvIgJYOpAX/b6T/b4flCnD -type branch -top -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[0].decompress_inst.mode} == 32'b11) & ~|{(genblk1[0].decompress_inst.mode == 2'b0), (genblk1[0].decompress_inst.mode == 2'b1), (genblk1[0].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type branch -instance {genblk1[0].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress_top.sv -start_line 173 -end_line 173 -start_column 22 -end_column 29 -expression 1'b0 -persistency AAABSHicrZBRDsIgEETHeA0PwRZry583aQqFv8ZGvX98bIwnkM0uu8PMFCrpLOkuU9KoQpiiVjWmSq6k+WSczQognTvQmSbfZ2U8LtpQFD2069CT/kUseoMc/o3gugY7ufuAvhEVzw2ssRdqAa+wb9wkUxvMzvmXx5XZQPtbErcvKLO7BdgTk9FlNL1G8Oj/IaNMnEqnb/7WB3VALD4= -type branch -top -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/abr_libs/rtl/abr_piso_multi.sv -start_line 106 -end_line 106 -start_column 17 -end_column 35 -expression 1'b0 -persistency AAABSHicrZBRDoIwEETHeA0PQQuU8udNTCndPyNR7x9fN8YTyGTLdrr7FirpLOmqrKBBs0wr2cy6qykhY7ewXzWpKhKNiqDi76yNLMC4eEfVQ3cdepK/0E1vnMNnGLQCoZMKzEp3ZOrIhM21kDc4ibORuoYMuvn3/Iuxo0x9hNH/uDovUdM7ujdAKXiR3ohXcQLsyW9DOn3j93wA4xEqtg== -type branch -instance abr_piso_inst -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/abr_libs/rtl/abr_piso_multi.sv -start_line 106 -end_line 106 -start_column 17 -end_column 35 -expression 1'b0 -persistency AAABSHicrZBRDoIwEETHeA0PQQuU8udNTCndPyNR7x9fN8YTyGTLdrr7FirpLOmqrKBBs0wr2cy6qykhY7ewXzWpKhKNiqDi76yNLMC4eEfVQ3cdepK/0E1vnMNnGLQCoZMKzEp3ZOrIhM21kDc4ibORuoYMuvn3/Iuxo0x9hNH/uDovUdM7ujdAKXiR3ohXcQLsyW9DOn3j93wA4xEqtg== -type statement -instance abr_piso_inst -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/abr_libs/rtl/abr_piso_multi.sv -start_line 83 -end_line 83 -start_column 17 -end_column 49 -expression 1'b0 -persistency AAABSHicrY/RDcIwDEQPsQZDkDQJ6R+boCSt/xAVsL94tRATUMvx2TnfNZKOkq6qCjoryzSDMueiVYUwugv9rKShSK4wgprXqg4KaJx8Y+ihuzY9wS/ipjeTzT2KexgbExHJAL+D9lpwMDwCtTFdmO3OGaXq3H9p7C9K3A/OiFqj7/73nUygyV9s8COTCCP5vnFnaBy++fs+JzEqKg== -type statement -instance abr_piso_inst -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[3].decompress_inst.mode} == 32'b11) & ~|{(genblk1[3].decompress_inst.mode == 2'b0), (genblk1[3].decompress_inst.mode == 2'b1), (genblk1[3].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type statement -instance {genblk1[3].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[2].decompress_inst.mode} == 32'b11) & ~|{(genblk1[2].decompress_inst.mode == 2'b0), (genblk1[2].decompress_inst.mode == 2'b1), (genblk1[2].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type statement -instance {genblk1[2].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[1].decompress_inst.mode} == 32'b11) & ~|{(genblk1[1].decompress_inst.mode == 2'b0), (genblk1[1].decompress_inst.mode == 2'b1), (genblk1[1].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type statement -instance {genblk1[1].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress_top.sv -start_line 117 -end_line 117 -start_column 21 -end_column 73 -expression 1'b0 -persistency AAABSHicrY9RDsIgEESfeg0PIaVa+PMmpi3tn7FR7x8fpEcwm4HZ3ZkhACfgTiBzZbYCkZHVbhGjCK0L7hIXJ1XbyQJDuxOTGWeKjpkXTzbe8o/14Otka29UZ+JGb2VZbOlZ9yLvTItuakY2dWjKoqdXm5z+K2PWkZwVz5o3qbuoXPR3+qp7bTnRbf19UVH1U2Nw3HHYwQ8/Yihu -type statement -top -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress.sv -start_line 40 -end_line 40 -start_column 26 -end_column 32 -expression {(~({30'b0, genblk1[0].decompress_inst.mode} == 32'b11) & ~|{(genblk1[0].decompress_inst.mode == 2'b0), (genblk1[0].decompress_inst.mode == 2'b1), (genblk1[0].decompress_inst.mode == 2'b10)})} -persistency AAABSHicrY9dDsIgEITHeA0PAYXy8+ZNGqDtm7FR7x8/N8YT2Ak7y7B8pJLOkq4aKCqroYIPeTxSJ7SqymmjBs46vpOtnBebrDAu7Dd2d9106EH/RIteJIe90YzY0YDW8Abtw87sPcxMX4wX7OVKDXjkRvgbwzE/SBJzCU0kDm9G6EwmVrW/mS2Z6XbkyRyM03f9vjcyZCkN -type statement -instance {genblk1[0].decompress_inst} -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/decompress/rtl/decompress_top.sv -start_line 173 -end_line 173 -start_column 22 -end_column 29 -expression 1'b0 -persistency AAABSHicrZBRDsIgEETHeA0PwRZry583aQqFv8ZGvX98bIwnkM0uu8PMFCrpLOkuU9KoQpiiVjWmSq6k+WSczQognTvQmSbfZ2U8LtpQFD2069CT/kUseoMc/o3gugY7ufuAvhEVzw2ssRdqAa+wb9wkUxvMzvmXx5XZQPtbErcvKLO7BdgTk9FlNL1G8Oj/IaNMnEqnb/7WB3VALD4= -type statement -top -comment {default cases} -tag *
check_cov -waiver -add -source_file $design_path/abr_libs/rtl/abr_piso_multi.sv -start_line 92 -end_line 92 -start_column 5 -end_column 23 -expression 1'b1 -persistency AAABSHicrY/ZDcIwEAUH0QZFxM79Ryco5x8iAvoX4xWiArLay36ZJwNn4MpAoqJlZ3RqrSsbnbG79e4jDQvZ3FQkpugDs1OScYk/Fh7cOXg6v4wbb0+O8MhyZrNW1YfXJjOHc6Hm8Epxl6TV9ia8s4rmb4zynqS27KtRXjCpKHsVjNpeedPLXIPbWSvraIfTN3/fB4r8KLA= -type statement -instance abr_piso_inst -comment {overwritten later in the same comb block} -tag *



