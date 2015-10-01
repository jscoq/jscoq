(* JsCoq
 * Copyright (C) 2015 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq.
 *
 * Due to the large size of Coq libraries, we perform caching and lazy
 * loading in the browser.
*)

(** [init callback] gather package list and start preloading, call [callback] when done *)
val init : (unit -> unit) -> unit

(** [coq_resource_req url] query the manager's cache. *)
val coq_vo_req  : Js.js_string Js.t -> Js.js_string Js.t option

(** [coq_cma_req cma] load the [cma] file or else do nothing *)
val coq_cma_req : string -> unit
