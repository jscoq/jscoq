(* Output a JSON file for library loading

   (C) Mines ParisTech
   Written by: Emilio J. Gallego Arias, 
*)

open Format
open Yojson.Basic

(* Make the json file for the installed libraries *)
let to_name = String.concat "_"
let prefix = "filesys"

let wanted_files s =
  Filename.check_suffix s ".cma" ||
  Filename.check_suffix s ".vo"

let build_pkg (pid : string list) : Jslib.coq_pkg =
  let dir       = prefix ^ "/" ^ to_name pid       in
  let files     = Array.to_list @@ Sys.readdir dir in
  let pkg_files = List.filter wanted_files files   in
  let dummy_d   = Digest.string "" in
  {
    Jslib.pkg_id    = pid;
    with_ml         = true;
    pkg_files = List.map (fun s -> (s, dummy_d)) pkg_files;
  }

let build_pkgs () =
  let coq_pkgs_list = List.map (fun s -> "Coq" :: s) Jsdftlib.coq_theory_list in
  List.map build_pkg @@ Jsdftlib.plugin_list @ coq_pkgs_list @ Jsdftlib.addons_list

let _ =
  let pkgs = List.map Jslib.pkg_to_json (build_pkgs ()) in
  Printf.printf "%s\n" @@ pretty_to_string (`List pkgs)
