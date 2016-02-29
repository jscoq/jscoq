(* Output a JSON file for library loading
 *
 * (C) Mines ParisTech
 * Written by: Emilio J. Gallego Arias
 *)

open Format
open Yojson.Basic

module Dl = Dftlibs

(* Make the json file for the installed libraries *)
let is_vo s =
  Filename.check_suffix s ".vo"

let is_cma s =
  Filename.check_suffix s ".cma"

let build_pkg (pid : string list) : Jslib.coq_pkg =
  let dummy_d   = Digest.string ""                 in
  let dir       = Dl.prefix ^ "/" ^ Dl.to_dir pid  in
  let vo_files, cma_files =
    try
      let open List                                    in
      let files     = Array.to_list @@ Sys.readdir dir in
      filter is_vo files, filter is_cma files
    with
    | Sys_error msg ->
      eprintf "Warning: %s@\n%!" msg;
      [], []
  in
  {
    Jslib.pkg_id    = pid;
    vo_files  = List.map (fun s -> (s, dummy_d)) vo_files;
    cma_files = List.map (fun s -> (s, dummy_d)) cma_files;
  }

let out_pref = "coq-pkgs/"

let build_pkg (pkg, deps, p_mod) =
  let open List                                    in
  let open Jslib                                   in
  let out    = open_out (out_pref ^ pkg ^ ".json") in
  let ofmt   = formatter_of_out_channel out        in
  let p_mod  = map build_pkg p_mod                 in
  let bundle = { desc = pkg;
                 deps = deps;
                 pkgs = p_mod;
               } in
  let json   = bundle_to_json bundle               in
  fprintf ofmt "%s\n" @@ pretty_to_string json;
  close_out out

let _ =
  List.iter build_pkg Dl.pkgs
