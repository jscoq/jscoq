#include <caml/mlvalues.h>
#include <caml/alloc.h>

#ifdef CAMLprim
#undef CAMLprim
#endif

#define CAMLprim __attribute__((used))
#define STUB { /* __wasi_trace("coq:byterun stub"); */ return Atom(0); }

/* coq_float64.c */

CAMLprim value coq_is_double(value x)               STUB

CAMLprim value coq_feq_byte(value a, value b)       STUB
CAMLprim value coq_flt_byte(value a, value b)       STUB
CAMLprim value coq_fgt_byte(value a, value b)       STUB

CAMLprim value coq_fmul_byte(value a, value b)      STUB
CAMLprim value coq_fadd_byte(value a, value b)     { return caml_copy_double(Double_val(a) + Double_val(b)); }
CAMLprim value coq_fsub_byte(value a, value b)      STUB
CAMLprim value coq_fdiv_byte(value a, value b)      STUB

CAMLprim value coq_fsqrt_byte(value a)              STUB
CAMLprim value coq_next_up_byte(value a)            STUB
CAMLprim value coq_next_down_byte(value a)          STUB

/* coq_fix_code.h */

CAMLprim value coq_tcode_of_code(value code)        STUB
CAMLprim value coq_makeaccu (value i)               STUB
CAMLprim value coq_pushpop (value i)                STUB
CAMLprim value coq_accucond (value i)               STUB
CAMLprim value coq_is_accumulate_code(value code)   STUB

/* coq_interp.h */

CAMLprim value coq_push_ra(value tcode)                                   STUB
CAMLprim value coq_push_val(value v)                                      STUB
CAMLprim value coq_push_arguments(value args)                             STUB
CAMLprim value coq_push_vstack(value stk)                                 STUB
CAMLprim value coq_interprete_ml(value tcode, value a, value t,
                                 value g, value e, value ea)              STUB
CAMLprim value coq_interprete_byte(value* argv, int argn)                 STUB
CAMLprim value coq_interprete(code_t coq_pc, value coq_accu,
            value coq_atom_tbl, value coq_global_data,
            value coq_env, long coq_extra_args)                           STUB
CAMLprim value coq_eval_tcode (value tcode, value t, value g, value e)    STUB

/* coq_memory.h */

CAMLprim value coq_static_alloc(value size)         STUB
CAMLprim value init_coq_vm(value unit)              STUB
CAMLprim value re_init_coq_vm(value unit)           STUB
CAMLprim value coq_set_transp_value(value transp)   STUB
CAMLprim value get_coq_transp_value(value unit)     STUB

CAMLprim value coq_set_drawinstr(value unit)        STUB

/* coq_memory.c */

CAMLprim value accumulate_code(value unit)          STUB

/* coq_values.c */

CAMLprim value coq_kind_of_closure(value v)                            STUB
CAMLprim value coq_closure_arity(value clos)                           STUB
CAMLprim value coq_current_fix(value v)                                STUB
CAMLprim value coq_shift_fix(value v, value offset)                    STUB
CAMLprim value coq_last_fix(value v)                                   STUB
CAMLprim value coq_set_bytecode_field(value v, value i, value code)    STUB
CAMLprim value coq_offset_tcode(value code, value offset)              STUB
CAMLprim value coq_int_tcode(value pc, value offset)                   STUB
CAMLprim value coq_tcode_array(value tcodes)                           STUB
CAMLprim value coq_obj_set_tag (value arg, value new_tag)              STUB
