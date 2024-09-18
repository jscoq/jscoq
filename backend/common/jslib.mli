(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * By Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 * This file contains the basic coq library definitions used in jscoq.
 *)

(* Information about a Coq library.
 *
 * We could have accessed Loadpath.t, etc..., but we've opted to keep
 * this module separated from Coq
 *)

module Coq_pkg : sig
  type t =
    { pkg_id    : string list
    ; vo_files  : (string * Digest.t option) list
    ; cma_files : (string * Digest.t option) list
    } [@@deriving yojson]

  val dir  : t -> string
  (*val dp : t -> string*)
  val num_files : t -> int
end

module Coq_bundle : sig
  type t =
    { name      : string
    ; chunks    : t list option
    ; deps      : string list
    ; pkgs      : Coq_pkg.t list
    ; archive   : string option
    ; modDeps   : Yojson.Safe.t option
    } [@@deriving yojson]

  val coqpath : ?implicit:bool -> t -> Loadpath.vo_path list

end

module DownloadProgress : sig
  type t = { total : int; downloaded : int }
  [@@deriving yojson]
end

module LibManager : sig
  type progress_info =
    { uri : string
    ; download : DownloadProgress.t
    } [@@deriving yojson]

  (* old progress info *)
  type _progress_info =
    { bundle : string
    ; pkg    : string
    ; loaded : int
    ; total  : int
    } [@@deriving yojson]

  type lib_event =
    | LibInfo     of string * Coq_bundle.t
    (** Information about the bundle, we could well put the json here *)
    | LibProgress of progress_info
    (** Information about loading progress *)
    | LibLoaded   of string * Coq_bundle.t option
    (** [LibLoaded url] Library designed by [url] was succesfully loaded *)
    | LibError    of string * string
    (** Bundle failed to load *)
  [@@deriving yojson]
end

val is_bytecode : string -> bool

(** This shouldn't be needed...  *)
val paths_to_coqpath : ?implicit:bool -> (string list * string list) list -> Loadpath.vo_path list
val require_libs : string list -> (string * string option * Lib.export_flag option) list
val module_name_of_qualid : Libnames.qualid -> string list
