(* Output a JSON file for library loading
 *
 * (C) Mines ParisTech
 * Written by: Emilio J. Gallego Arias
 *)

open Format
open Yojson.Safe

module Dl = Dftlibs

let n_warn = ref 0

(* Make the json file for the installed libraries *)
let is_vo s =
  Filename.check_suffix s ".vo"

let is_cma s =
  Filename.check_suffix s ".cma" ||
  Filename.check_suffix s ".cmo"

let select (l : string list) (sel : Dl.selector) = 
  let open Dl in
  match sel with
  | All -> l
  | Only s -> List.filter (fun fn -> List.mem fn s) l
  | Except s -> List.filter (fun fn -> not @@ List.mem fn s) l

let build_pkg ((pid, sel) : string list * Dl.selector) : Jslib.coq_pkg =
  let dummy_d   = Digest.string ""                 in
  let dir       = Dl.prefix ^ "/" ^ Dl.to_dir pid  in
  let vo_files, cma_files =
    try
      let open List                                 in
      let files = Array.to_list @@ Sys.readdir dir  in
      let files = select files sel                  in
      (* eprintf "files for %s: %n@\n" dir (List.length files); *)
      filter is_vo files, filter is_cma files
    with
    | Sys_error _msg ->
      (* eprintf "Warning: %s@\n%!" _msg; *)
      incr n_warn;
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
                 archive = None;
                 pkgs = p_mod;
               } in
  let json   = coq_bundle_to_yojson bundle         in

  fprintf ofmt "%s\n" @@ pretty_to_string json;
  close_out out

let _ =
  List.iter build_pkg Dl.pkgs;
  if !n_warn > 0 then
    eprintf "Addons not found: %d@\n%!" !n_warn
