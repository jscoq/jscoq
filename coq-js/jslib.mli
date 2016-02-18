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

type coq_pkg = {
  pkg_id    : string list;
  vo_files  : (string * Digest.t) list;
  cma_files : (string * Digest.t) list;
}

type coq_bundle = {
  desc      : string;
  deps      : string list;
  pkgs      : coq_pkg list;
}

val to_dir  : coq_pkg -> string
val to_desc : coq_pkg -> string

val no_files : coq_pkg -> int

(* JSON handling *)
open Yojson.Basic

(* XXX Use PPX *)
val pkg_to_json : coq_pkg -> json
val json_to_pkg : json -> coq_pkg

val bundle_to_json : coq_bundle -> json
val json_to_bundle : json -> coq_bundle

