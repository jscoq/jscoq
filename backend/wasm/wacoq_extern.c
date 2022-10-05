#include <caml/mlvalues.h>


// Implemented in core.ts
value interrupt_pending() { return Val_false; }

// For subproc mode
value wacoq_emit(value str) { printf("%s\n", (const char *)str); fflush(stdout); return Val_unit; }
