(*
   Build the std filesystem for jscoq

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Format
module Dl = Dftlibs


let (/) = Filename.concat
let cd cur ch = if Filename.is_relative ch then cur / ch else ch

let option_map_default f d = function | Some x -> f x | None -> d


(* use `fileutils`? *)
module Fileutils = struct
  open Unix

  let buffer_size = 8192
  let buffer = Bytes.create buffer_size

  let file_copy source_filename target_filename mode =
    let fd_in = openfile source_filename [O_RDONLY] 0 in
    let fd_out = openfile target_filename [O_WRONLY; O_CREAT; O_TRUNC] mode in
    let rec copy_loop () = match read fd_in buffer 0 buffer_size with
      |  0 -> ()
      | r -> ignore (write fd_out buffer 0 r); copy_loop ()
    in
    copy_loop ();  close fd_in;  close fd_out

  let file_update source_filename target_filename =
    let source_stats = lstat source_filename in
    let target_stats = try Some (lstat target_filename) 
                       with Unix.Unix_error _ -> None in
    let needs_update = option_map_default 
      (fun ts -> source_stats.st_mtime > ts.st_mtime) true target_stats in
    if needs_update then
      file_copy source_filename target_filename source_stats.st_perm

  let rec mkdir_p dirpath perm =
    match dirpath with
    | [] -> "."
    | el :: els -> if (not @@ Sys.file_exists el) then Unix.mkdir el perm;
      match els with | [] -> el | x :: xs -> mkdir_p ((el / x) :: xs) perm
end

(* Determines which files are copied over *)
let include_pat fn =
  Filename.(check_suffix fn ".vo" || check_suffix fn ".cma")


let copy_subdir coqdir basepath dirpath =
  let subdirpath = basepath :: List.tl dirpath                       in
  let desc       = Dl.to_dir subdirpath                              in
  let indir      = Dl.to_dir (coqdir :: subdirpath)                  in
  let outdir     = Fileutils.mkdir_p (Dl.prefix :: dirpath) 0o755    in

  let copy_single_file fn =
    try
      Fileutils.file_update (indir / fn) (outdir / fn)
    with Sys_error e ->
      eprintf " * @[failed to copy:@ %s/%s@]\n%!" desc fn
  in

  try
    Sys.readdir indir |> Array.to_seq 
      |> Seq.filter include_pat |> Seq.iter copy_single_file
  with Sys_error e ->
    eprintf " * @[missing subdirectory:@ %s@]\n%!" 
            (Dl.to_dir (basepath :: (List.tl dirpath)))

let make_libfs coqdir =
  List.iter (copy_subdir coqdir "plugins")  Dl.plugin_list;
  List.iter (copy_subdir coqdir "theories") Dl.coq_theory_list


let _ =
  let coqdir = ref @@ "." in
  Arg.parse [] (fun s -> coqdir := cd !coqdir s) "" ;
  make_libfs !coqdir
