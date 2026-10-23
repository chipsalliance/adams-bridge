//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
// DESCRIPTION:
//   Wraps ML_DSA_randomized_zeroize_mid_op_sequence into a UVM test.
//   Targets the zeroizeXmasking / zeroizeXntt1 / zeroizeXrecombine cross
//   holes reported in ABR SCA nightly coverage.
//
//----------------------------------------------------------------------

class ML_DSA_randomized_zeroize_mid_op_test extends test_top;

  `uvm_component_utils(ML_DSA_randomized_zeroize_mid_op_test);

  function new(string name = "", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    mldsa_bench_sequence_base::type_id::set_type_override(
        ML_DSA_randomized_zeroize_mid_op_sequence::get_type());
    super.build_phase(phase);
  endfunction

  virtual task main_phase(uvm_phase phase);
    ML_DSA_randomized_zeroize_mid_op_sequence seq;
    seq = ML_DSA_randomized_zeroize_mid_op_sequence::type_id::create(
              "ML_DSA_randomized_zeroize_mid_op_sequence");
    seq.start(null);
  endtask

endclass

// pragma uvmf custom external begin
// pragma uvmf custom external end
