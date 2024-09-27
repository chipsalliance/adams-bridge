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
//
class mem_agent_config extends uvm_object;
    `uvm_object_utils(mem_agent_config)

    string mem_path;

    function new(string name = "mem_agent_config");
        super.new(name);
    endfunction

    function void set_mem_path(string path);
        mem_path = path;
    endfunction

    function string get_mem_path();
        return mem_path;
    endfunction
endclass: mem_agent_config