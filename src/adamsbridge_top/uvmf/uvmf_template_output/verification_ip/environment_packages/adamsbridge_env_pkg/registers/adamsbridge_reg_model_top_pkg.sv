//----------------------------------------------------------------------
// Created with uvmf_gen version 2022.3
//----------------------------------------------------------------------
// pragma uvmf custom header begin
// pragma uvmf custom header end
//----------------------------------------------------------------------
//
//----------------------------------------------------------------------
// Placeholder for complete register model.  This placeholder allows
//  compilation of generated environment without modification.
//----------------------------------------------------------------------
//----------------------------------------------------------------------
//

package adamsbridge_reg_model_top_pkg;

   import uvm_pkg::*;
// pragma uvmf custom additional_imports begin
   import adamsbridge_reg_uvm::*;
// pragma uvmf custom additional_imports end

   `include "uvm_macros.svh"

   /* DEFINE REGISTER CLASSES */
// pragma uvmf custom define_register_classes begin
   //--------------------------------------------------------------------
   // Class: adamsbridge_example_reg0
   // 
   //--------------------------------------------------------------------
   class adamsbridge_example_reg0 extends uvm_reg;
      `uvm_object_utils(adamsbridge_example_reg0)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "adamsbridge_example_reg0");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass

   //--------------------------------------------------------------------
   // Class: adamsbridge_example_reg1
   // 
   //--------------------------------------------------------------------
   class adamsbridge_example_reg1 extends uvm_reg;
      `uvm_object_utils(adamsbridge_example_reg1)

      rand uvm_reg_field example_field; 

      // Function: new
      // 
      function new(string name = "adamsbridge_example_reg1");
         super.new(name, 8, UVM_NO_COVERAGE);
      endfunction


      // Function: build
      // 
      virtual function void build();
         example_field = uvm_reg_field::type_id::create("example_field");
         example_field.configure(this, 8, 0, "RW", 0, 8'h00, 1, 1, 1);
      endfunction
   endclass
// pragma uvmf custom define_register_classes end

// pragma uvmf custom define_block_map_coverage_class begin
   //--------------------------------------------------------------------
   // Class: adamsbridge_fixme_map_coverage
   // 
   // Coverage for the 'fixme_map' in 'adamsbridge_reg_model'
   //--------------------------------------------------------------------
   class adamsbridge_fixme_map_coverage extends uvm_object;
      `uvm_object_utils(adamsbridge_fixme_map_coverage)

      covergroup ra_cov(string name) with function sample(uvm_reg_addr_t addr, bit is_read);

         option.per_instance = 1;
         option.name = name; 

         ADDR: coverpoint addr {
            bins example_reg0 = {'h0};
            bins example_reg1 = {'h1};
         }

         RW: coverpoint is_read {
            bins RD = {1};
            bins WR = {0};
         }

         ACCESS: cross ADDR, RW;

      endgroup: ra_cov

      function new(string name = "adamsbridge_fixme_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: adamsbridge_fixme_map_coverage

   class adamsbridge_AHB_map_coverage extends uvm_object;
      `uvm_object_utils(adamsbridge_AHB_map_coverage)

      covergroup ra_cov(string name) with function sample(uvm_reg_addr_t addr, bit is_read);

         option.per_instance = 1;
         option.name = name; 

         // FIXME
         ADDR: coverpoint addr {
            bins example_reg0 = {'h0};
            bins example_reg1 = {'h1};
         }

         RW: coverpoint is_read {
            bins RD = {1};
            bins WR = {0};
         }

         ACCESS: cross ADDR, RW;

      endgroup: ra_cov

      function new(string name = "adamsbridge_AHB_map_coverage");
         ra_cov = new(name);
      endfunction: new

      function void sample(uvm_reg_addr_t offset, bit is_read);
         ra_cov.sample(offset, is_read);
      endfunction: sample

   endclass: adamsbridge_AHB_map_coverage
// pragma uvmf custom define_block_map_coverage_class end

   //--------------------------------------------------------------------
   // Class: adamsbridge_reg_model_top
   // 
   //--------------------------------------------------------------------

   class adamsbridge_reg_model_top extends adamsbridge_reg;
      `uvm_object_utils(adamsbridge_reg_model_top)
    
      adamsbridge_AHB_map_coverage AHB_map_cg;
    
      function new(string name = "adamsbridge_reg_model_top");
         super.new(name);
      endfunction
    
      
     

      virtual function void build();
         super.build();
        // Build coverage for address map
        if (has_coverage(UVM_CVR_ADDR_MAP)) begin
          AHB_map_cg = adamsbridge_AHB_map_coverage::type_id::create("AHB_map_cg");
          AHB_map_cg.ra_cov.set_inst_name({this.get_full_name(), "_AHB_cg"});
          void'(set_coverage(UVM_CVR_ADDR_MAP));
        end
   
      endfunction
    
      function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map map);
        if (get_coverage(UVM_CVR_ADDR_MAP)) begin
          if (map.get_name() == "adamsbridge_AHB_map") begin
            AHB_map_cg.sample(offset, is_read);
          end
        end
      endfunction: sample
    
    endclass
    
    
//    class adamsbridge_reg_model_top extends uvm_reg_block;
//       `uvm_object_utils(adamsbridge_reg_model_top)
// // pragma uvmf custom instantiate_registers_within_block begin
//       rand adamsbridge_reg adamsbridge_rm;
// // pragma uvmf custom instantiate_registers_within_block end

      
//       uvm_reg_map adamsbridge_AHB_map; // Block map
//       adamsbridge_AHB_map_coverage AHB_map_cg;
//       //adamsbridge_fixme_map_coverage fixme_map_cg;

//       // Function: new
//       // 
//       function new(string name = "");
//          super.new(name, build_coverage(UVM_CVR_ALL));
//       endfunction

//       // Function: build
//       // 
//       virtual function void build();
//          if(has_coverage(UVM_CVR_ADDR_MAP)) begin
//             AHB_map_cg = adamsbridge_AHB_map_coverage::type_id::create("AHB_map_cg");
//             AHB_map_cg.ra_cov.set_inst_name({this.get_full_name(),"_AHB_cg"});
//             void'(set_coverage(UVM_CVR_ADDR_MAP));
//          end
//          this.adamsbridge_AHB_map = create_map("adamsbridge_AHB_map", 0, 4, UVM_LITTLE_ENDIAN);

//          this.adamsbridge_rm = new("adamsbridge_rm");
//          this.adamsbridge_rm.configure(this);
//          // Build the internal registers of adamsbridge_rm
//          this.adamsbridge_rm.build();
//          // Add registers to the AHB map
//          this.build_ext_maps();

//          // Lock the register model
//          this.lock_model();

//       endfunction

//       virtual function void build_ext_maps();
//          uvm_reg        regs[$];
     
//          // Get registers from the default map of adamsbridge_rm
//          this.adamsbridge_rm.default_map.get_registers(regs, UVM_NO_HIER);
     
//          // Add registers to the AHB map
//          foreach (regs[c_reg]) begin
//            this.adamsbridge_AHB_map.add_reg(regs[c_reg], regs[c_reg].get_offset(this.adamsbridge_rm.default_map));
//          end

//        endfunction
 

//       // Function: sample
//       //
//       function void sample(uvm_reg_addr_t offset, bit is_read, uvm_reg_map  map);
//          if(get_coverage(UVM_CVR_ADDR_MAP)) begin
//             if(map.get_name() == "adamsbridge_AHB_map") begin
//                AHB_map_cg.sample(offset, is_read);
//             end
//          end
//       endfunction: sample

//    endclass

endpackage

// pragma uvmf custom external begin
// pragma uvmf custom external end

