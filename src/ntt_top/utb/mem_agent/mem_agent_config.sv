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