(* JsCoq
 * Copyright (C) 2015 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq

   Due to the large size of Coq libraries, we wnat to perform caching
   and lazy loading in the browser.
*)

(* We likely want these to be Hashtbls of just js arrays. *)
type cache_entry = {
  (* url        : Js.js_string; *)
  content    : Js.js_string Js.t;
  md5        : Digest.t;
  }

type byte_cache_entry = {
  md5     : Digest.t; (* Or other signature *)
  js_code : Js.js_string;
}

val init : unit -> unit

val coq_resource_req : Js.js_string Js.t -> Js.js_string Js.t option

val preload_file : string -> (string * int) -> unit Lwt.t
