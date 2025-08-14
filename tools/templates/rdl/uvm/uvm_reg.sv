{% import 'utils.sv' as utils with context %}

//------------------------------------------------------------------------------
// uvm_reg definition
//------------------------------------------------------------------------------
{% macro class_definition(node) -%}
{%- if class_needs_definition(node) %}
// {{get_class_friendly_name(node)}}
class {{get_class_name(node)}} extends uvm_reg;
{%- if use_uvm_factory %}
    `uvm_object_utils({{get_class_name(node)}})
{%- endif %}
    {{child_insts(node)|indent}}
    {{function_new(node)|indent}}

    {{function_build(node)|indent}}
endclass : {{get_class_name(node)}}
{% endif -%}
{%- endmacro %}


//------------------------------------------------------------------------------
// Child instances
//------------------------------------------------------------------------------
{% macro child_insts(node) -%}
{%- for field in node.fields() -%}
rand uvm_reg_field {{get_inst_name(field)}};
{% endfor -%}
{%- endmacro %}


//------------------------------------------------------------------------------
// new() function
//------------------------------------------------------------------------------
{% macro function_new(node) -%}
function new(string name = "{{get_class_name(node)}}");
    super.new(name, {{node.get_property('regwidth')}}, UVM_NO_COVERAGE);
endfunction : new
{%- endmacro %}


//------------------------------------------------------------------------------
// build() function
//------------------------------------------------------------------------------
{% macro function_build(node) -%}
virtual function void build();
    {%- for field in node.fields() %}
    {%- if use_uvm_factory %}
    this.{{get_inst_name(field)}} = uvm_reg_field::type_id::create("{{get_inst_name(field)}}");
    {%- else %}
    this.{{get_inst_name(field)}} = new("{{get_inst_name(field)}}");
    {%- endif %}
    this.{{get_inst_name(field)}}.configure(this, {{field.width}}, {{field.lsb}}, "{{get_field_access(field)}}", {{field.is_volatile|int}}, {{"'h%x" % field.get_property('reset', default=0)}}, {{field.get_property('reset') is not none|int}}, 1, 0);
    {%- endfor %}
endfunction : build
{%- endmacro %}


//------------------------------------------------------------------------------
// build() actions for uvm_reg instance (called by parent)
//------------------------------------------------------------------------------
{% macro build_instance(node) -%}
{%- if node.is_array %}
foreach(this.{{get_inst_name(node)}}[{{utils.array_iterator_list(node)}}]) begin
    {%- if use_uvm_factory %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}} = {{get_class_name(node)}}::type_id::create($sformatf("{{get_inst_name(node)}}{{utils.array_suffix_format(node)}}", {{utils.array_iterator_list(node)}}));
    {%- else %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}} = new($sformatf("{{get_inst_name(node)}}{{utils.array_suffix_format(node)}}", {{utils.array_iterator_list(node)}}));
    {%- endif %}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}.configure(this);
    {{add_hdl_path_slices(node, get_inst_name(node) + utils.array_iterator_suffix(node))|trim|indent}}
    this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}.build();
    this.default_map.add_reg(this.{{get_inst_name(node)}}{{utils.array_iterator_suffix(node)}}, {{get_array_address_offset_expr(node)}});
end
{%- else %}
{%- if use_uvm_factory %}
this.{{get_inst_name(node)}} = {{get_class_name(node)}}::type_id::create("{{get_inst_name(node)}}");
{%- else %}
this.{{get_inst_name(node)}} = new("{{get_inst_name(node)}}");
{%- endif %}
this.{{get_inst_name(node)}}.configure(this);
{{add_hdl_path_slices(node, get_inst_name(node))|trim}}
this.{{get_inst_name(node)}}.build();
this.default_map.add_reg(this.{{get_inst_name(node)}}, {{"'h%x" % node.raw_address_offset}});
{%- endif %}
{%- endmacro %}

//------------------------------------------------------------------------------
// Load HDL path slices for this reg instance
//------------------------------------------------------------------------------
{% macro add_hdl_path_slices(node, inst_ref) -%}
{%- if node.get_property('hdl_path') %}
{{inst_ref}}.add_hdl_path_slice("{{node.get_property('hdl_path')}}", -1, -1);
{%- endif -%}

{%- if node.get_property('hdl_path_gate') %}
{{inst_ref}}.add_hdl_path_slice("{{node.get_property('hdl_path_gate')}}", -1, -1, 0, "GATE");
{%- endif -%}

{%- for field in node.fields() %}
{%- if field.get_property('hdl_path_slice') is none -%}
{%- elif field.get_property('hdl_path_slice')|length == 1 %}
{{inst_ref}}.add_hdl_path_slice("{{field.get_property('hdl_path_slice')[0]}}", {{field.lsb}}, {{field.width}});
{%- elif field.get_property('hdl_path_slice')|length == field.width %}
{%- for slice in field.get_property('hdl_path_slice') %}
{%- if field.msb > field.lsb %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb - loop.index0}}, 1);
{%- else %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb + loop.index0}}, 1);
{%- endif %}
{%- endfor %}
{%- endif %}
{%- endfor -%}

{%- for field in node.fields() %}
{%- if field.get_property('hdl_path_gate_slice') is none -%}
{%- elif field.get_property('hdl_path_gate_slice')|length == 1 %}
{{inst_ref}}.add_hdl_path_slice("{{field.get_property('hdl_path_gate_slice')[0]}}", {{field.lsb}}, {{field.width}}, 0, "GATE");
{%- elif field.get_property('hdl_path_gate_slice')|length == field.width %}
{%- for slice in field.get_property('hdl_path_gate_slice') %}
{%- if field.msb > field.lsb %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb - loop.index0}}, 1, 0, "GATE");
{%- else %}
{{inst_ref}}.add_hdl_path_slice("{{slice}}", {{field.msb + loop.index0}}, 1, 0, "GATE");
{%- endif %}
{%- endfor %}
{%- endif %}
{%- endfor %}
{%- endmacro %}