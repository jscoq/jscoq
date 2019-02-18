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

type digest  = Digest.t
type _digest = string
[@@deriving yojson]

let digest_of_yojson j =
  let open Result in
  match _digest_of_yojson j with
  | Ok s    -> Ok (Digest.from_hex s)
  | Error e -> Error e

let digest_to_yojson s = _digest_to_yojson (Digest.to_hex s)

type coq_pkg = {
  pkg_id    : string list;
  vo_files  : (string * digest) list;
  cma_files : (string * digest) list;
}
[@@deriving yojson]

type coq_bundle = {
  desc      : string;
  deps      : string list;
  archive   : string option [@default None];
  pkgs      : coq_pkg list;
}
[@@deriving yojson]

let to_dir   pkg = String.concat "/" (pkg.pkg_id)
let to_desc  pkg = String.concat "." (pkg.pkg_id)
let no_files pkg = List.length pkg.vo_files + List.length pkg.cma_files
