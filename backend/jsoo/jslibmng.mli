(* JsCoq
 * Copyright (C) 2016-2019 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq.
 *
 * Due to the large size of Coq libraries, we perform caching and lazy
 * loading in the browser.
*)

open Jscoq_core.Jslib.LibManager

type out_fn = lib_event -> unit

(** [info_pkg out_fn lib_path pkgs] gathers package list [pkgs] from
    directory [lib_path], emits events using [out_fn].  *)
val info_pkg : out_fn -> string -> string list -> unit Lwt.t

(** [load_pkg base_path pkg_file] loads package [pkg_file] *)
val load_pkg : verb:bool -> out_fn -> string -> string -> unit Lwt.t

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : string -> string option

val register_cma : file_path:string -> unit

(** [coq_cma_link cma] dynlinks the bytecode plugin [cma] *)
val coq_cma_link : file_path:string -> unit
