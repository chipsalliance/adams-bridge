<!--
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# MLDSA Control inner FSM

You can use [this](https://marketplace.visualstudio.com/items?itemName=bierner.markdown-mermaid) extension to render the following graph in Visuel Studio Code.

Transition diagram for the different states of the inner FSM in the control module handling a single instruction:

```mermaid
flowchart

init-state(["init"])
idle-state(["MLDSA_CTRL_IDLE"])
sha3-start-state(["MLDSA_CTRL_SHA3_START"])
msg-start-state(["MLDSA_CTRL_MSG_START"])
msg-load-state(["MLDSA_CTRL_MSG_LOAD"])
msg-wait-state(["MLDSA_CTRL_MSG_WAIT"])
func-start-state(["MLDSA_CTRL_FUNC_START"])
done-state(["MLDSA_CTRL_DONE"])

init-state-to-idle-state["reset"]
init-state --- init-state-to-idle-state --> idle-state

idle-state-to-idle-state["else"]
idle-state --- idle-state-to-idle-state --> idle-state

idle-state-to-sha3-start-state["keccak_en"]
idle-state --- idle-state-to-sha3-start-state --> sha3-start-state

idle-state-to-func-start-state["sampler_en || ntt_en || aux_en"]
idle-state --- idle-state-to-func-start-state --> func-start-state

sha3-start-state-to-msg-start-state["[unconditionally]"]
sha3-start-state --- sha3-start-state-to-msg-start-state --> msg-start-state

msg-start-state-to-msg-load-state["[unconditionally]"]
msg-start-state --- msg-start-state-to-msg-load-state --> msg-load-state

msg-load-state-to-func-start-state["msg_done && sampler_en"]
msg-load-state --- msg-load-state-to-func-start-state --> func-start-state

msg-load-state-to-msg-wait-state["msg_done && !sampler_en"]
msg-load-state --- msg-load-state-to-msg-wait-state --> msg-wait-state

    msg-load-state-to-msg-load-state["!msg_done"]
    msg-load-state --- msg-load-state-to-msg-load-state --> msg-load-state

msg-wait-state-to-func-start-state["sampler_en || aux_en || ntt_en"]
msg-wait-state --- msg-wait-state-to-func-start-state --> func-start-state

msg-wait-state-to-msg-load-state["else"]
msg-wait-state --- msg-wait-state-to-msg-load-state --> msg-load-state

func-start-state-to-done-state["[unconditionally]"]
func-start-state --- func-start-state-to-done-state --> done-state

done-state-to-idle-state["[operation done]"]
done-state --- done-state-to-idle-state --> idle-state

done-state-to-done-state["else"]
done-state --- done-state-to-done-state --> done-state
```
