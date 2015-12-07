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

class type jsCoq = object

  (* When init is finished, we call on init  *)
  method init        : ('self t, Stateid.t)             meth_callback writeonly_prop
  method onInit      : ('self t, unit)                  event_listener writeonly_prop

  method version     : ('self t, js_string t)           meth_callback writeonly_prop
  method goals       : ('self t, js_string t)           meth_callback writeonly_prop

  method add         : ('self t, Stateid.t -> int -> js_string t -> Stateid.t) meth_callback writeonly_prop
  method edit        : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop
  method commit      : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop
  method query       : ('self t, Stateid.t -> js_string t -> unit) meth_callback writeonly_prop

  (* Add a package *)
  method add_pkg_    : ('self t, js_string t -> unit)   meth_callback writeonly_prop

  (* Request to log from Coq *)
  method onLog       : ('self t, js_string t)           event_listener writeonly_prop
  (* Error from Coq *)
  method onError     : ('self t, Stateid.t)             event_listener writeonly_prop
  (* method onLog       : ('self t, js_string t -> unit)      meth_callback opt writeonly_prop *)
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
