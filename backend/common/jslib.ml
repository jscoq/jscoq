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
  ; vo_files  : (string * digest option) list
  ; cma_files : (string * digest option) list
  } [@@deriving yojson]

let to_dir   pkg = String.concat "/" pkg.pkg_id
let to_desc  pkg = String.concat "." pkg.pkg_id
let no_files pkg = List.length pkg.vo_files + List.length pkg.cma_files

type coq_bundle =
  { name      : string
  ; chunks    : coq_bundle list option [@default None]
  ; deps      : string list
  ; pkgs      : coq_pkg list
  ; archive   : string option [@default None]
  ; modDeps   : Yojson.Safe.t option [@default None]
  } [@@deriving yojson]

let path_to_coqpath ?(implicit=false) ?(unix_prefix=[]) lib_path =
  let phys_path =  (* HACK to allow manual override of dir path *)
    if last unix_prefix = Some "." then unix_prefix
                                   else unix_prefix @ lib_path
  in
  Loadpath.{
    unix_path = String.concat "/" phys_path
  ; coq_path = Names.(DirPath.make @@ List.rev_map Id.of_string lib_path)
  ; has_ml = true
  ; implicit = implicit && is_intrinsic lib_path
  ; recursive = false
  }

let paths_to_coqpath ?(implicit=false) lib_path =
  List.map (fun (path_el, phys) ->
    path_to_coqpath ~implicit ~unix_prefix:phys path_el
  ) lib_path
