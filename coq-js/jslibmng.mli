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

open Js

(** [init callback] gather package list and start preloading, call
    [callback] when done *)
val init : (unit -> unit) -> (string * int -> unit) -> (string -> unit) -> (string * int -> unit) -> unit

(** [load_pkg pkg_file] load package [file] *)
val load_pkg : string -> unit

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : js_string t -> js_string t option

(** [coq_cma_req cma] load the [cma] file or else do nothing *)
val coq_cma_req : string -> unit

(** [request_byte_cache md5] return [Some js] if bytecode with with
    digest [md5] is in the cache, None otherwise *)
val request_byte_cache : Digest.t -> js_string t option
