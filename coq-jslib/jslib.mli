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

(* JSON handling *)
module J = Yojson.Safe

type coq_pkg = {
  pkg_id    : string list;
  vo_files  : (string * Digest.t) list;
  cma_files : (string * Digest.t) list;
}

val coq_pkg_to_yojson : coq_pkg -> J.t
val coq_pkg_of_yojson : J.t -> (coq_pkg, string) Result.result

val to_dir  : coq_pkg -> string
val to_desc : coq_pkg -> string
val no_files : coq_pkg -> int

type coq_bundle = {
  desc      : string;
  deps      : string list;
  pkgs      : coq_pkg list;
  archive   : string option;
  modDeps   : J.t option;
}

val coq_bundle_to_yojson : coq_bundle -> J.t
val coq_bundle_of_yojson : J.t -> (coq_bundle, string) Result.result
