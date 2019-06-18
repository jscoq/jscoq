(* Output a JSON file for library loading
 *
 * (C) Mines ParisTech
 * Written by: Emilio J. Gallego Arias
 *)

open Format
open Yojson.Safe

module Dl = Dftlibs

(* Package statistics *)
type stats = {
  total_pkgs : int;
  found_pkgs: int
}

let stats : (string, stats) Hashtbl.t = 
  Hashtbl.create 15

let or_zeroed = function
  | None -> { total_pkgs = 0; found_pkgs = 0 }
  | Some x -> x

let incr_total_pkgs r = r := { !r with total_pkgs = !r.total_pkgs + 1 }
let incr_found_pkgs r = r := { !r with found_pkgs = !r.found_pkgs + 1 }

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

let build_pkg pkg ((pid, sel) : string list * Dl.selector) : Jslib.coq_pkg =
  let dir       = Dl.prefix ^ "/" ^ Dl.to_dir pid  in
  let pkg_stats = ref (Hashtbl.find_opt stats pkg
                       |> or_zeroed)               in
  let vo_files, cma_files =
    try
      incr_total_pkgs pkg_stats;
      let open List                                 in
      let files = Array.to_list @@ Sys.readdir dir  in
      let files = select files sel                  in
      (* eprintf "files for %s: %n@\n" dir (List.length files); *)
      incr_found_pkgs pkg_stats;
      filter is_vo files, filter is_cma files
    with
    | Sys_error _msg ->
      [], []
  in
  Hashtbl.replace stats pkg !pkg_stats;
  {
    Jslib.pkg_id    = pid;
    vo_files  = List.map (fun s -> (s, None)) vo_files;   (* digests are disabled, for now *)
    cma_files = List.map (fun s -> (s, None)) cma_files;
  }

let out_pref = "coq-pkgs/"

let build_bundle (pkg, deps, p_mod) =
  let open List                                    in
  let open Jslib                                   in
  let out    = open_out (out_pref ^ pkg ^ ".json") in
  let ofmt   = formatter_of_out_channel out        in
  let p_mod  = map (build_pkg pkg) p_mod           in
  let bundle = { desc = pkg;
                 deps = deps;
                 archive = None;
                 pkgs = p_mod;
                 modDeps = None;
               } in
  let json   = coq_bundle_to_yojson bundle         in

  fprintf ofmt "%s\n" @@ pretty_to_string json;
  close_out out

let seq_eprint s =
  Seq.iter (fun el -> eprintf "@ %s" el) s

let seq_join sep s =
  let l = Seq.fold_left (fun l el -> el :: l) [] s in
  String.concat sep l

let seq_is_empty seq = match seq () with
  | Seq.Nil -> true
  | Seq.Cons (_,_) -> false

let _ =
  List.iter build_bundle Dl.pkgs;
  let pkgs = (Hashtbl.to_seq stats) in
  let pkgs_complete = Seq.filter (fun (_pkg, stats) -> stats.total_pkgs > 0 && stats.found_pkgs = stats.total_pkgs) pkgs in
  let pkgs_partial = Seq.filter (fun (_pkg, stats) -> stats.total_pkgs > stats.found_pkgs && stats.found_pkgs > 0) pkgs in
  let pkgs_missing = Seq.filter (fun (_pkg, stats) -> stats.total_pkgs > 0 && stats.found_pkgs = 0) pkgs in
  eprintf "\n%!";
  eprintf "Complete packages:\n%!   [@[<b 1>"; seq_eprint (Seq.map fst pkgs_complete); eprintf "@] ]\n%!";
  if (not @@ seq_is_empty pkgs_missing) then begin
    eprintf "Missing packages:\n%!   [@[<b 1>"; seq_eprint (Seq.map fst pkgs_missing); eprintf "@] ]\n%!" end;
  if (not @@ seq_is_empty pkgs_partial) then begin
    eprintf "Partially available packages:\n   [@[<b 1>";
      (seq_eprint (Seq.map (fun (pkg, stats) -> sprintf "%s(%d/%d)" pkg stats.found_pkgs stats.total_pkgs) pkgs_partial));
    eprintf "@] ]\n%!" end;
  eprintf "\n%!"
