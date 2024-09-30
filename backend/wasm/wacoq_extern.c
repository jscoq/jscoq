#include <caml/mlvalues.h>


// Implemented in core.ts
value interrupt_pending() { return Val_false; }
value interrupt_setup(value opaque) { return Val_false; }
value read_file(value name) { return Val_false; }
value write_file(value name, value content) { return Val_false; }

// For subproc mode
value wacoq_emit(value str) { printf("%s\n", (const char *)str); fflush(stdout); return Val_unit; }
