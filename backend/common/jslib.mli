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
  val dp : t -> string
  val num_files : t -> int
end

module Coq_bundle : sig
  type t =
    { name      : string
    ; chunks    : t list option
    ; deps      : string list
    ; pkgs      : Coq_pkg.t list
    ; archive   : string option
    ; modDeps   : Yojson.Basic.t option
    } [@@deriving yojson]

  val coqpath : ?implicit:bool -> t -> Loadpath.vo_path list

end

(** This shouldn't be needed...  *)
val paths_to_coqpath : ?implicit:bool -> (string list * string list) list -> Loadpath.vo_path list
val require_libs : string list -> (string * string option * Lib.export_flag option) list
val module_name_of_qualid : Libnames.qualid -> string list
