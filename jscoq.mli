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

class type addCodeEvent = object
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

  method addCode     : ('self t, addCodeEvent)     event_listener writeonly_prop
  method assignState : ('self t, assignStateEvent) event_listener writeonly_prop
  method coqError    : ('self t, coqErrorEvent)    event_listener writeonly_prop

end

