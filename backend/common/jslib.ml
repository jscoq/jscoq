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

(*
let to_dir   pkg = String.concat "/" pkg.pkg_id
let to_desc  pkg = String.concat "." pkg.pkg_id
let no_files pkg = List.length pkg.vo_files + List.length pkg.cma_files
*)

module Coq_pkg = struct
  type t =
    { pkg_id    : string list
    ; vo_files  : (string * digest option) list
    ; cma_files : (string * digest option) list
    } [@@deriving yojson]

    
  let dir   pkg = String.concat "/" pkg.pkg_id
  (*val dp : t -> string *)
  let num_files pkg = List.length pkg.vo_files + List.length pkg.cma_files
end


let rec last = function
    | [] -> None
    | [x] -> Some x
    | _ :: t -> last t

let is_intrinsic = function
    | "Coq" :: _ -> true
    | _ -> false

let is_bytecode file =
  let chk sf = Filename.check_suffix file sf in
  chk "cma" || chk "cmo" || chk "cma.js" || chk "cmo.js"

let require_libs libs =
  List.map (fun lp -> lp, None, Some Lib.Export) libs
  (* Last coordinate: *)
  (*   None            : just require            *)
  (*   Some Lib.Import : import but don't export *)
  (*   Some Lib.Export : import and export       *)

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

let path_of_dirpath dirpath =
  Names.(List.rev_map Id.to_string (DirPath.repr dirpath))

let module_name_of_qualid qualid =
  let (dirpath, id) = Libnames.repr_qualid qualid in
  (path_of_dirpath dirpath) @ [Names.Id.to_string id]

module Coq_bundle = struct
  type t =
    { name      : string
    ; chunks    : t list option
    ; deps      : string list
    ; pkgs      : Coq_pkg.t list
    ; archive   : string option
    ; modDeps   : Yojson.Safe.t option
    } [@@deriving yojson]

  let coqpath ?(implicit=false) bundle =
    let open Coq_pkg in
    List.map (fun pkg ->
      path_to_coqpath ~implicit pkg.pkg_id
    ) bundle.pkgs

end

module LibManager = struct
  type progress_info =
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
    | LibLoaded   of string * Coq_bundle.t
    (** Bundle [pkg] is loaded *)
    | LibError    of string * string
    (** Bundle failed to load *)
  [@@deriving yojson]
end