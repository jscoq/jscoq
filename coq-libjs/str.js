var v_log = true;   // Whether to log
function log(s) { if (v_log) console.warn(s); }

//Provides: re_string_match
var log;

function re_string_match() {
  // external re_string_match : regexp -> string -> int -> bool
  if (!re_string_match.warned) {
    log("Danger: missing primitive re_string_match called from Str");
    re_string_match.warned = true;
  }
  return false;
}

//Provides: re_search_forward
var log;

function re_search_forward() {
  // external re_search_forward: regexp -> string -> int -> int array
  if (!re_search_forward.warned) {
    log("Danger: missing primitive re_search_forward called from Str");
    re_search_forward.warned = true;
  }
  return [];
}
