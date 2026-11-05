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

####################################################
# Copyright(c) LUBIS EDA GmbH, All rights reserved #
# Contact: contact@lubis-eda.com                   #
####################################################

# Coverage for the abr_sha3 bench is signed off for the top module only.
# The pad and keccak round sub-blocks have their own FV benches
# (fv_abr_sha3pad, fv_abr_keccak_round), so their logic is waived here.
# Proofs still run on the full design; waivers only affect check_cov.
#
# Sourced by the ScriptBuilder post_elaboration hook
# (jasper_gold_config.hooks.post_elaboration in script_builder.json).

check_cov -waiver -add -type {*} -instance {u_pad} -comment {sub-block verified in fv_abr_sha3pad} -tag {*}
check_cov -waiver -add -type {*} -instance {u_keccak} -comment {sub-block verified in fv_abr_keccak_round} -tag {*}
