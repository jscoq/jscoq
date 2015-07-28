(* Output a JSON file for library loading
 *
 * (C) Mines ParisTech
 * Written by: Emilio J. Gallego Arias
 *)

open Format
open Yojson.Basic

(* Make the json file for the installed libraries *)
let to_name = String.concat "_"
let prefix = "filesys"

let is_vo s =
  Filename.check_suffix s ".vo"

let is_cma s =
  Filename.check_suffix s ".cma"

let build_pkg (pid : string list) : Jslib.coq_pkg =
  let dir       = prefix ^ "/" ^ to_name pid       in
  let files     = Array.to_list @@ Sys.readdir dir in
  let vo_files  = List.filter is_vo files          in
  let cma_files = List.filter is_cma files         in
  let dummy_d   = Digest.string ""                 in
  {
    Jslib.pkg_id    = pid;
    vo_files  = List.map (fun s -> (s, dummy_d)) vo_files;
    cma_files = List.map (fun s -> (s, dummy_d)) cma_files;
  }

let build_pkgs () =
  let coq_std_pkgs = List.map (fun s -> "Coq" :: s) @@ Jsdftlib.plugin_list @ Jsdftlib.coq_theory_list in
  List.map build_pkg @@ coq_std_pkgs @ Jsdftlib.addons_list

let _ =
  let pkgs = List.map Jslib.pkg_to_json (build_pkgs ()) in
  Printf.printf "%s\n" @@ pretty_to_string (`List pkgs)
