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
  let dir       = Dl.prefix ^ "/" ^ Dl.to_dir pid  in
  let files     = Array.to_list @@ Sys.readdir dir in
  let vo_files  = List.filter is_vo files          in
  let cma_files = List.filter is_cma files         in
  let dummy_d   = Digest.string ""                 in
  {
    Jslib.pkg_id    = pid;
    vo_files  = List.map (fun s -> (s, dummy_d)) vo_files;
    cma_files = List.map (fun s -> (s, dummy_d)) cma_files;
  }

let out_pref = "coq-pkgs/"

let build_pkg (pkg, p_mod) =
  let out   = open_out (out_pref ^ pkg ^ ".json")      in
  let p_mod = List.map build_pkg p_mod                 in
  let json  = List.map Jslib.pkg_to_json p_mod         in
  Printf.fprintf out "%s\n" @@ pretty_to_string (`List json);
  close_out out

let _ =
  List.iter build_pkg Dl.pkgs
