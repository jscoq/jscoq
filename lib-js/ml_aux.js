//Provides: caml_marshal_data_size mutable
//Requires: caml_failwith, caml_string_unsafe_get
function caml_marshal_data_size (s, ofs) {
  function get32(s,i) {
    return (caml_string_unsafe_get(s, i) << 24) |
           (caml_string_unsafe_get(s, i + 1) << 16) |
           (caml_string_unsafe_get(s, i + 2) << 8) |
            caml_string_unsafe_get(s, i + 3);
  }
  debugger;
  var tmp     = get32(s, ofs);
  var magic_n = (0x8495A6BE|0);

  console.log(tmp.toString(16) + "\n");
  console.log(magic_n.toString(16) + "\n");

  if (tmp != magic_n)
    caml_failwith("Marshal.data_size: bad object");
  return (get32(s, ofs + 4));
}
