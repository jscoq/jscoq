// Provides: vm_ll
function vm_ll(s, args) { 
  if (vm_ll.log) joo_global_object.console.warn(s, args); 
  if (vm_ll.trap) throw new Error("vm trap: '"+ s + "' not implemented");
}

vm_ll.log = false;     // whether to log calls
vm_ll.trap = false;    // whether to halt on calls

// Provides: init_coq_vm
// Requires: vm_ll
function init_coq_vm() {
  vm_ll('init_coq_vm', arguments);
  return;
}

// EG: Coq VM's code is evil and performs static initialization... the
// best option would be to disable the VM code entirely as before.

// Provides: coq_vm_trap
// Requires: vm_ll
function coq_vm_trap() {    // will cause future calls to vm code to fault
  vm_ll.log = vm_ll.trap = true;  // (called after initialization)
}

// Provides: accumulate_code
// Requires: vm_ll
function accumulate_code() {
  // EG: Where the hell is that called from
  vm_ll('accumulate_code', arguments);
  return [];
}

// Provides: coq_pushpop
// Requires: vm_ll
function coq_pushpop() {
  vm_ll('coq_pushpop', arguments);
  return [];
}

// Provides: coq_closure_arity
// Requires: vm_ll
function coq_closure_arity() {
  vm_ll('coq_closure_arity', arguments);
  return [];
}

// Provides: coq_eval_tcode
// Requires: vm_ll
function coq_eval_tcode() {
  vm_ll('coq_eval_tcode', arguments);
  return [];
}

// Provides: coq_int_tcode
// Requires: vm_ll
function coq_int_tcode() {
  vm_ll('coq_int_tcode', arguments);
  return [];
}

// Provides: coq_interprete_ml
// Requires: vm_ll
function coq_interprete_ml() {
  vm_ll('coq_interprete_ml', arguments);
  return [];
}

// Provides: coq_is_accumulate_code
// Requires: vm_ll
function coq_is_accumulate_code() {
  vm_ll('coq_is_accumulate_code', arguments);
  return [];
}

// Provides: coq_kind_of_closure
// Requires: vm_ll
function coq_kind_of_closure() {
  vm_ll('coq_kind_of_closure', arguments);
  return [];
}

// Provides: coq_makeaccu
// Requires: vm_ll
function coq_makeaccu() {
  vm_ll('coq_makeaccu', arguments);
  return [];
}

// Provides: coq_offset
// Requires: vm_ll
function coq_offset() {
  vm_ll('coq_offset', arguments);
  return [];
}

// Provides: coq_offset_closure
// Requires: vm_ll
function coq_offset_closure() {
  vm_ll('coq_offset_closure', arguments);
  return [];
}

// Provides: coq_offset_tcode
// Requires: vm_ll
function coq_offset_tcode() {
  vm_ll('coq_offset_tcode', arguments);
  return [];
}

// Provides: coq_push_arguments
// Requires: vm_ll
function coq_push_arguments() {
  vm_ll('coq_push_arguments', arguments);
  return [];
}

// Provides: coq_push_ra
// Requires: vm_ll
function coq_push_ra() {
  vm_ll('coq_push_ra', arguments);
  return [];
}

// Provides: coq_push_val
// Requires: vm_ll
function coq_push_val() {
  vm_ll('coq_push_val', arguments);
  return [];
}

// Provides: coq_push_vstack
// Requires: vm_ll
function coq_push_vstack() {
  vm_ll('coq_push_vstack', arguments);
  return [];
}

// Provides: coq_set_transp_value
// Requires: vm_ll
function coq_set_transp_value() {
  vm_ll('coq_set_transp_value', arguments);
  return [];
}

// Provides: coq_set_bytecode_field
// Requires: vm_ll
function coq_set_bytecode_field() {
  vm_ll('coq_set_bytecode_field', arguments);
  return [0];
}

// Provides: coq_tcode_of_code
// Requires: vm_ll
function coq_tcode_of_code() {
  vm_ll('coq_tcode_of_code', arguments);
  return [];
}

// Provides: get_coq_atom_tbl
// Requires: vm_ll
function get_coq_atom_tbl() {
  // First element of the array is the length!
  vm_ll('get_coq_atom_tbl', arguments);
  return [0];
}

// Provides: get_coq_global_data
// Requires: vm_ll
function get_coq_global_data() {
  vm_ll('get_coq_global_data', arguments);
  return [];
}

// Provides: get_coq_transp_value
// Requires: vm_ll
function get_coq_transp_value() {
  vm_ll('get_coq_transp_value', arguments);
  return [];
}

// Provides: realloc_coq_atom_tbl
// Requires: vm_ll
function realloc_coq_atom_tbl() {
  vm_ll('realloc_coq_atom_tbl', arguments);
  return;
}

// Provides: realloc_coq_global_data
// Requires: vm_ll
function realloc_coq_global_data() {
  vm_ll('realloc_coq_global_data', arguments);
  return;
}

// Provides: coq_interprete_byte
// Requires: vm_ll
function coq_interprete_byte()    { vm_ll('coq_interprete_byte', arguments); }
// Provides: coq_set_drawinstr
// Requires: vm_ll
function coq_set_drawinstr()      { vm_ll('coq_set_drawinstr', arguments); }
// Provides: coq_tcode_array
// Requires: vm_ll
function coq_tcode_array()        { vm_ll('coq_tcode_array', arguments); }

// Provides: coq_fadd_byte
function coq_fadd_byte(r1, r2) {
  return r1 + r2;
}

// Provides: coq_fsub_byte
function coq_fsub_byte(r1, r2) {
  return r1 - r2;
}

// Provides: coq_fmul_byte
function coq_fmul_byte(r1, r2) {
  return r1 * r2;
}

// Provides: coq_fdiv_byte
function coq_fdiv_byte(r1, r2) {
  return r1 / r2;
}

// Provides: coq_fsqrt_byte
// Requires: vm_ll
function coq_fsqrt_byte() {
  vm_ll('coq_fsqrt_byte', arguments);
  return;
}

// Provides: coq_is_double
// Requires: vm_ll
  function coq_is_double() {
    vm_ll('coq_is_double', arguments);
  return;
}

// Provides: coq_next_down_byte
// Requires: vm_ll
  function coq_next_down_byte() {
    vm_ll('coq_next_down_byte', arguments);
  return;
}

// Provides: coq_next_up_byte
// Requires: vm_ll
  function coq_next_up_byte() {
    vm_ll('coq_next_up_byte', arguments);
  return;
}

// Provides: coq_current_fix
// Requires: vm_ll
function coq_current_fix() {
  vm_ll('coq_current_fix', arguments);
  return [];
}

// Provides: coq_last_fix
// Requires: vm_ll
function coq_last_fix() {
  vm_ll('coq_last_fix', arguments);
  return [];
}

// Provides: coq_shift_fix
// Requires: vm_ll
function coq_shift_fix() {
  vm_ll('coq_shift_fix', arguments);
  return [];
}
