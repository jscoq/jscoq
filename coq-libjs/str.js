function str_ll(s) { if (v_log) console.warn(s); }
str_ll.log = true;

//Provides: str_ll
var str_ll;

//Provides: re_string_match
//Requires: str_ll
function re_string_match() {
  // external re_string_match : regexp -> string -> int -> bool
  if (!re_string_match.warned) {
    str_ll("Danger: missing primitive re_string_match called from Str");
    re_string_match.warned = true;
  }
  return false;
}

//Provides: re_search_forward
//Requires: str_ll
function re_search_forward() {
  // external re_search_forward: regexp -> string -> int -> int array
  if (!re_search_forward.warned) {
    str_ll("Danger: missing primitive re_search_forward called from Str");
    re_search_forward.warned = true;
  }
  return [];
}

//Provides: re_partial_match
//Requires: str_ll
function re_partial_match()          { str_ll('re_partial_match', arguments); }
//Provides: re_replacement_text
//Requires: str_ll
function re_replacement_text()       { str_ll('re_replacement_text', arguments); }
//Provides: re_search_backward
//Requires: str_ll
function re_search_backward()        { str_ll('re_search_backward', arguments); }