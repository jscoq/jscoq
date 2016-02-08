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

let to_dir  pkg = String.concat "/" (pkg.pkg_id)
let to_desc pkg = String.concat "." (pkg.pkg_id)

let no_files pkg = List.length pkg.vo_files + List.length pkg.cma_files

(* JSON handling *)
open Yojson.Basic

let file_to_json (f : (string * Digest.t)) : json =
  `String (fst f)

let pkg_to_json (p : coq_pkg) : json =
  `Assoc ["pkg_id",    `List (List.map (fun s -> `String s) p.pkg_id);
          "vo_files",  `List (List.map file_to_json p.vo_files);
          "cma_files", `List (List.map file_to_json p.cma_files)]

let json_to_file (f : json) : (string * Digest.t) =
  match f with
  | `String name -> (name, Digest.string "")
  | _            -> raise (Failure "JSON")

let json_to_pkg (p : json) : coq_pkg =
  match p with
  | `Assoc ["pkg_id", `List pid; "vo_files", `List vo_files; "cma_files", `List cma_files] ->
     { pkg_id    = List.map (fun s ->
                        match s with `String s -> s | _ -> raise (Failure "JSON")) pid;
       vo_files  = List.map json_to_file vo_files;
       cma_files = List.map json_to_file cma_files;
     }
  | _ -> raise (Failure "JSON")

