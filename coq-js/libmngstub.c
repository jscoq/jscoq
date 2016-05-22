#include <stdlib.h>
#include <stdio.h>

#define D(f) void f () { fprintf(stderr, "Unimplemented Javascript primitive %s!\\\\n", #f); exit(1); }

D(string_of_uint8Array)
D(caml_string_of_array)
