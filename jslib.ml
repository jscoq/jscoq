(* This file contains the basic coq library definitions used in jscoq *)

(* Information about a Coq library. We could access Loadpath.t, etc...,
   but we've opted to keep this module separated from Coq *)
type coq_pkg = {
  pkg_id    : string list;
  (* Has ml files *)
  with_ml   : bool;
  pkg_files : (string * Digest.t) list;
}

let to_name = String.concat "_"

(* JSON handling *)
open Yojson.Basic

let file_to_json (f : (string * Digest.t)) : json =
  `String (fst f)

let pkg_to_json (p : coq_pkg) : json =
  `Assoc ["pkg_id",    `List (List.map (fun s -> `String s) p.pkg_id);
          "pkg_files", `List (List.map file_to_json p.pkg_files)]

let json_to_file (f : json) : (string * Digest.t) =
  match f with
  | `String name -> (name, Digest.string "")
  | _ -> raise (Failure "JSON")

let json_to_pkg (p : json) : coq_pkg =
  match p with
  | `Assoc ["pkg_id", `List pid; "pkg_files", `List pkg_files] ->
     { pkg_id    = List.map (fun s ->
                        match s with `String s -> s | _ -> raise (Failure "JSON")) pid;
       with_ml   = true;
       pkg_files = List.map json_to_file pkg_files
     }
  | _ -> raise (Failure "JSON")

