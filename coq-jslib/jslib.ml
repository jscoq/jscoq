(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * Copyright (C) 2016-2017 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 * This file contains the basic coq library definitions used in jscoq.
 *)

(* Information about a Coq library.
 *
 * We could have use Loadpath.t, etc..., but we've opted to keep
 * this module separated from Coq
 *)

module J = Yojson.Safe

type digest =
  [%import: Digest.t]
  [@@deriving yojson]

type coq_pkg =
  { pkg_id    : string list
  ; vo_files  : (string * digest) list
  ; cma_files : (string * digest) list
  } [@@deriving yojson]

let to_dir   pkg = String.concat "/" pkg.pkg_id
let to_desc  pkg = String.concat "." pkg.pkg_id
let no_files pkg = List.length pkg.vo_files + List.length pkg.cma_files

type coq_bundle =
  { desc      : string
  ; deps      : string list
  ; pkgs      : coq_pkg list
  ; archive   : string option [@default None]
  ; modDeps   : Yojson.Safe.t option [@default None]
  } [@@deriving yojson]

