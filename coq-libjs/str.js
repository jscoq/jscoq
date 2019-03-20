function str_ll(s, args) { if (str_ll.log) console.warn(s, args); }
str_ll.log = true;

//Provides: str_ll
var str_ll;

//Provides: re_string_match
//Requires: str_ll
function re_string_match() {
  // external re_string_match : regexp -> string -> int -> bool
  if (!re_string_match.warned) {
    str_ll("(from Str) re_string_match", arguments);
    re_string_match.warned = true;
  }
  return false;
}

//Provides: re_search_forward
//Requires: str_ll
function re_search_forward() {
  // external re_search_forward: regexp -> string -> int -> int array
  if (!re_search_forward.warned) {
    str_ll("(from Str) re_search_forward", arguments);
    re_search_forward.warned = true;
  }
  return [0]; /* [||] : int array */
}

//Provides: re_partial_match
//Requires: str_ll
// external re_partial_match: regexp -> string -> int -> int array
function re_partial_match()          { str_ll('re_partial_match', arguments);     return [0]; }
//Provides: re_replacement_text
//Requires: str_ll
// external re_replacement_text: string -> int array -> string -> string
function re_replacement_text(_,_,s)  { str_ll('re_replacement_text', arguments);  return s; }
//Provides: re_search_backward
//Requires: str_ll
// external re_search_backward: regexp -> string -> int -> int array
function re_search_backward()        { str_ll('re_search_backward', arguments);   return [0]; }