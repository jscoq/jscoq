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

type progress_info =
  { bundle : string
  ; pkg    : string
  ; loaded : int
  ; total  : int
  }

type lib_event =
  | LibInfo     of string * Jslib.coq_bundle (* Information about the bundle, we could well put the json here *)
  | LibProgress of progress_info             (* Information about loading progress *)
  | LibLoaded   of string * Jslib.coq_bundle (* Bundle [pkg] is loaded *)

type out_fn = lib_event -> unit

(** [info_pkg out_fn base_path lib_path pkgs] gathers package list [pkgs] from
    directory [lib_path], emits events using [out_fn].  *)
val info_pkg : out_fn -> string -> string list -> unit Lwt.t

(** [load_pkg base_path pkg_file] loads package [pkg_file] *)
val load_pkg : out_fn -> string -> string -> unit Lwt.t
(** [info_pkg lib_path available_pkg ] gather package list
    [available_pkg] from directory [lib_path] *)

(** [coq_resource_req url] query the manager's cache for object [url] *)
val coq_vo_req  : string -> string option

(** [coq_cma_link cma] dynlinks the bytecode plugin [cma] *)
val coq_cma_link : string -> unit

val is_bytecode : string -> bool
val register_cma : file_path:string -> unit

(* auxiliary functions to create and process paths *)
val path_to_coqpath : ?implicit:bool -> ?unix_prefix:string list -> string list -> Loadpath.coq_path
val coqpath_of_bundle : ?implicit:bool -> Jslib.coq_bundle -> Loadpath.coq_path list

val path_of_dirpath : Names.DirPath.t -> string list
val module_name_of_qualid : Libnames.qualid -> string list
(* val module_name_of_reference : Libnames.reference_r -> string list *)
