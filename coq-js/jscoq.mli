(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * By Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq. Our object listens to the following messages:
 *
 * And emits:
 *
 * - CoqLogEvent(level, msg): Log [msg] of priority [level].
 *
 *)

open Js
open Dom

(* Packages to load first *)
class type initInfo = object
  method init_pkgs_ : js_string t js_array t readonly_prop
  method all_pkgs_  : js_string t js_array t readonly_prop
  method base_path_ : js_string t            readonly_prop
end

class type jsCoq = object

  (* When the libraries are loaded and JsCoq is ready, onInit is called *)
  method init        : ('self t, initInfo t -> Stateid.t) meth_callback writeonly_prop
  method onInit      : ('self t, unit)                    event_listener prop

  method version     : ('self t, js_string t)           meth_callback writeonly_prop
  method goals       : ('self t, js_string t)           meth_callback writeonly_prop

  method goal_sexp_  : ('self t, js_string t)           meth_callback writeonly_prop
  method goal_json_  : ('self t, 'a t)                  meth_callback writeonly_prop

  method add         : ('self t, Stateid.t -> int -> js_string t -> Stateid.t) meth_callback writeonly_prop
  method edit        : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop
  method commit      : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop
  method query       : ('self t, Stateid.t -> js_string t -> unit) meth_callback writeonly_prop

  (* Options. XXX must improve. *)
  method set_printing_width_ : ('self t, int -> unit) meth_callback writeonly_prop

  (* Package management *)
  method add_pkg_    : ('self t, js_string t -> unit) meth_callback writeonly_prop

  (* When a new package is known we push the information to the GUI *)
  method onBundleInfo  : ('self t, Jslibmng.bundleInfo t ) event_listener prop
  method onBundleStart : ('self t, Jslibmng.bundleInfo t ) event_listener prop
  method onBundleLoad  : ('self t, Jslibmng.bundleInfo t ) event_listener prop

  (* When package loading starts/progresses/completes  *)
  method onPkgLoadStart : ('self t, Jslibmng.progressInfo t) event_listener prop
  method onPkgProgress  : ('self t, Jslibmng.progressInfo t) event_listener prop
  method onPkgLoad      : ('self t, Jslibmng.progressInfo t) event_listener prop

  (* Request to log from Coq *)
  method onLog       : ('self t, js_string t)           event_listener prop
  (* Error from Coq *)
  method onError     : ('self t, Stateid.t)             event_listener writeonly_prop

end

(*
class type coqLogEvent = object
  inherit [jsCoq] event

  method msg : js_string t readonly_prop
end

and addCodeEvent = object
  inherit [jsCoq] event

  method code : js_string t readonly_prop
  method eid  : int         readonly_prop
end

and assignStateEvent = object
  inherit [jsCoq] event

  method eid  : int   readonly_prop
  method sid  : int   readonly_prop
end

and coqErrorEvent = object
  inherit [jsCoq] event

  method eid  : int         readonly_prop
  method msg  : js_string t readonly_prop

end

and jsCoq = object
  method addCode     : ('self t, addCodeEvent     t) event_listener writeonly_prop
  method assignState : ('self t, assignStateEvent t) event_listener writeonly_prop
  method coqError    : ('self t, coqErrorEvent    t) event_listener writeonly_prop
end


*)
