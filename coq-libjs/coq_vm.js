var v_log = true;   // Whether to log
function ll(s, args) { if (v_log) console.warn(s, args); }

//Provides: ll
var ll;

//Provides: init_coq_vm
//Requires: ll
function init_coq_vm() {
  ll('init_coq_vm', arguments);
  return;
}

// EG: Coq VM's code is evil and performs static initialization... the
// best option would be to disable the VM code entirely as before.

//Provides: accumulate_code
//Requires: ll
function accumulate_code() {
  // EG: Where the hell is that called from
  ll('accumulate_code', arguments);
  return [];
}

//Provides: coq_pushpop
//Requires: ll
function coq_pushpop() {
  ll('coq_pushpop', arguments);
  return [];
}

// Provides: coq_closure_arity
//Requires: ll
function coq_closure_arity() {
  ll('coq_closure_arity', arguments);
  return [];
}

// Provides: coq_eval_tcode
// Requires: ll
function coq_eval_tcode() {
  ll('coq_eval_tcode', arguments);
  return [];
}

// Provides: coq_int_tcode
// Requires: ll
function coq_int_tcode() {
  ll('coq_int_tcode', arguments);
  return [];
}

// Provides: coq_interprete_ml
// Requires: ll
function coq_interprete_ml() {
  ll('coq_interprete_ml', arguments);
  return [];
}

// Provides: coq_is_accumulate_code
// Requires: ll
function coq_is_accumulate_code() {
  ll('coq_is_accumulate_code', arguments);
  return [];
}

// Provides: coq_kind_of_closure
// Requires: ll
function coq_kind_of_closure() {
  ll('coq_kind_of_closure', arguments);
  return [];
}

// Provides: coq_makeaccu
// Requires: ll
function coq_makeaccu() {
  ll('coq_makeaccu', arguments);
  return [];
}

// Provides: coq_offset
// Requires: ll
function coq_offset() {
  ll('coq_offset', arguments);
  return [];
}

// Provides: coq_offset_closure
// Requires: ll
function coq_offset_closure() {
  ll('coq_offset_closure', arguments);
  return [];
}

// Provides: coq_offset_tcode
// Requires: ll
function coq_offset_tcode() {
  ll('coq_offset_tcode', arguments);
  return [];
}

// Provides: coq_push_arguments
// Requires: ll
function coq_push_arguments() {
  ll('coq_push_arguments', arguments);
  return [];
}

// Provides: coq_push_ra
// Requires: ll
function coq_push_ra() {
  ll('coq_push_ra', arguments);
  return [];
}

// Provides: coq_push_val
// Requires: ll
function coq_push_val() {
  ll('coq_push_val', arguments);
  return [];
}

// Provides: coq_push_vstack
// Requires: ll
function coq_push_vstack() {
  ll('coq_push_vstack', arguments);
  return [];
}

// Provides: coq_set_transp_value
// Requires: ll
function coq_set_transp_value() {
  ll('coq_set_transp_value', arguments);
  return [];
}

// Provides: coq_set_bytecode_field
// Requires: ll
function coq_set_bytecode_field() {
  ll('coq_set_bytecode_field', arguments);
  return [0];
}

// Provides: coq_tcode_of_code
// Requires: ll
function coq_tcode_of_code() {
  ll('coq_tcode_of_code', arguments);
  return [];
}

// Provides: get_coq_atom_tbl
// Requires: ll
function get_coq_atom_tbl() {
  // First element of the array is the length!
  ll('get_coq_atom_tbl', arguments);
  return [0];
}

// Provides: get_coq_global_data
// Requires: ll
function get_coq_global_data() {
  ll('get_coq_global_data', arguments);
  return [];
}

// Provides: get_coq_transp_value
// Requires: ll
function get_coq_transp_value() {
  ll('get_coq_transp_value', arguments);
  return [];
}

// Provides: realloc_coq_atom_tbl
// Requires: ll
function realloc_coq_atom_tbl() {
  ll('realloc_coq_atom_tbl', arguments);
  return;
}

// Provides: realloc_coq_global_data
// Requires: ll
function realloc_coq_global_data() {
  ll('realloc_coq_global_data', arguments);
  return;
}
