(* JsCoq/SerAPI
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias
 * Copyright (C) 2016-2019 Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for Sertop_js/jsCoq

   Due to the large size of Coq libraries, we wnat to perform caching
   and lazy loading in the browser.
*)
open Jslib
open Lwt
open Js_of_ocaml
module JL = Js_of_ocaml_lwt

let verb = false

(* Main file_cache, indexed by url *)
type cache_entry =
  { file_content : string   (* file_content is backed by a TypedArray, thanks to @hhugo *)
  ; md5          : Digest.t
  }

(* Number of actual files in a full distribution ~ 2000 *)
let file_cache : (string, cache_entry) Hashtbl.t = Hashtbl.create 503

(* The cma resolver cache maps a cma module to its actual path. *)
let cma_cache : (string, string) Hashtbl.t = Hashtbl.create 103

type progress_info =
  { bundle : string
  ; pkg    : string
  ; loaded : int
  ; total  : int
  }

type lib_event =
  | LibInfo     of string * coq_bundle  (* Information about the bundle, we could well put the json here *)
  | LibProgress of progress_info        (* Information about loading progress *)
  | LibLoaded   of string * coq_bundle  (* Bundle [pkg] is loaded *)
  | LibError    of string * string      (* Bundle failed to load *)

type out_fn = lib_event -> unit

exception DynLinkFailed of string

let is_bytecode file = Filename.(check_suffix file "cma" || check_suffix file "cmo")

let preload_file ?(refresh=false) base_path base_url (file, _hash) : unit Lwt.t =
  let open JL.XmlHttpRequest                        in
  if verb then Format.eprintf "preload_request: %s / %s\n%!" base_path base_url;

  (* Cache the directory to workaround deficient Coq code *)
  if is_bytecode file then Hashtbl.add cma_cache file base_url;
  (* Load a js file for bytecode requests                           *)
  let req_file    = file ^ (if is_bytecode file then ".js" else "") in
  let full_url    = base_url  ^ "/" ^ file                          in
  let request_url = base_path ^ "/" ^ base_url ^ "/" ^ req_file     in
  let cached      = Hashtbl.mem file_cache full_url                 in

  (* Only reload if not cached or a refresh is requested *)
  if not cached || refresh then begin
  perform_raw ~response_type:ArrayBuffer request_url >>= fun frame ->
  (* frame.code contains the request status *)
  (* Is this redudant with the Opt check? I guess so *)
  if frame.code = 200 || frame.code = 0 then
    Js.Opt.case
      frame.content
      (fun ()        -> ())
      (fun raw_array ->
         let cache_entry = {
           file_content = Typed_array.String.of_arrayBuffer raw_array;
           md5          = Digest.string "";
         } in
         if verb then Format.eprintf "cache_add_entry: %s\n%!" full_url;
         Hashtbl.add file_cache full_url cache_entry;
         (* Warm the file cache to workaround a deficient jsoo is_directory implementation *)
         ignore(Sys.file_exists full_url);
      );
  Lwt.return_unit
  end
  else Lwt.return_unit

let preload_pkg ?(verb=false) out_fn base_path bundle pkg : unit Lwt.t =
  let pkg_dir = to_dir pkg                                           in
  let ncma    = List.length pkg.cma_files                            in
  let nfiles  = no_files pkg                                         in
  if verb then
    Format.eprintf "pre-loading package %s, [00/%02d] files\n%!" pkg_dir nfiles;
  (* XXX: pkg_start, we don't emit an event here *)
  let preload_and_log nc i f =
    preload_file base_path pkg_dir f >>= fun () ->
    if verb then
      Format.eprintf "pre-loading package %s, [%02d/%02d] files\n%!" pkg_dir (i+nc+1) nfiles;
    out_fn (LibProgress { bundle; pkg = pkg_dir; loaded = i+nc+1; total = nfiles });
    Lwt.return_unit
  in
  Lwt_list.iteri_s (preload_and_log 0   ) pkg.cma_files <&>
  Lwt_list.iteri_s (preload_and_log ncma) pkg.vo_files  >>= fun () ->
  (* We don't emit a package loaded event for now *)
  (* out_fn (LibLoadedPkg bundle pkg); *)
  Lwt.return_unit

let parse_bundle base_path file : coq_bundle Lwt.t =
  let open JL.XmlHttpRequest in
  let file_url = base_path ^ file ^ ".json" in
  get file_url >>= fun res ->
  if Int.equal res.code 200 then
    match Jslib.coq_bundle_of_yojson (Yojson.Safe.from_string res.content) with
    | Result.Ok bundle -> return bundle
    | Result.Error s   ->
      Format.eprintf "JSON parsing error in parse_bundle for file %s: %s\n%!" file s;
      Lwt.fail (Failure s)
    | exception Yojson.Json_error s ->
      Format.eprintf "JSON conversion error in parse_bundle for file %s: %s\n%!" file s;
      Lwt.fail (Failure s)
  else
    let s = Format.sprintf "%s: not found (%d)" file_url res.code in
    Lwt.fail (Failure s)

let load_under_way = ref ([])

let only_once lref s =
  if List.mem s !lref then false
  else begin
    lref := !lref @ [s]; true
  end

(* Load a bundle *)
let rec preload_from_file ?(verb=false) out_fn base_path bundle_name =
  if only_once load_under_way bundle_name then
    try%lwt
      parse_bundle base_path bundle_name >>= fun bundle ->
      (* Load sub-packages in parallel *)
      Lwt_list.iter_p (preload_pkg ~verb:verb out_fn base_path bundle_name) bundle.pkgs  >>= fun () ->
      return @@ out_fn (LibLoaded (bundle_name, bundle))
    with
    | Failure _ ->
    Lwt.return_unit
  else
    Lwt.return_unit

let info_from_file out_fn base_path file =
  try%lwt
    parse_bundle base_path file >>= fun bundle ->
    return @@ out_fn (LibInfo (file, bundle))
  with
  | Failure err -> return @@ out_fn (LibError(file, err))

let info_pkg out_fn base_path pkgs =
  Lwt_list.iter_p (info_from_file out_fn base_path) pkgs

(* Hack *)
let load_pkg out_fn base_path pkg_file =
  preload_from_file out_fn base_path pkg_file (*>>= fun () ->
  parse_bundle base_path pkg_file *)

(* let _is_bad_url _ = false *)

(* XXX: Wait until we have enough UI support for logging *)
let coq_vo_req url =
  (* if not @@ is_bad_url url then *)
  try
    let c_entry = Hashtbl.find file_cache url in
    Some c_entry.file_content
  with
  | Not_found -> None

(* coq_vo_reg is also invoked throught the Sys.file_exists call
 * in mltop:file_of_name function, a good example on how to be
 * too smart for your own good $:-)
 *
 * Sadly coq only uses this information to determine if it will
 * load a cmo/cma file, not to guess the path...
 *)

let coq_vo_req url =
  if verb then Format.eprintf "url %s requested\n%!" url; (* with category info *)
  match coq_vo_req url with
  | Some file -> Some file
  | None ->
    if verb then Format.eprintf "url request for %s FAILED\n%!" url; (* with category info *)
    None

let coq_cma_link cmo_file =
  let open Format in
  if verb then eprintf "bytecode file %s requested\n%!" cmo_file;
  let cmo_file =
    try Hashtbl.find cma_cache cmo_file ^ "/" ^ cmo_file
    with
    | Not_found ->
      eprintf "!! cache inconsistency for file %s\n%!" cmo_file;
      cmo_file
  in
  Feedback.feedback (Feedback.FileDependency(Some cmo_file, cmo_file));
  try
    (* let js_code = (Hashtbl.find file_cache cmo_file).file_content in *)
    let js_code =
      try (Hashtbl.find file_cache cmo_file).file_content
      with Not_found -> Sys_js.read_file ~name:(cmo_file ^ ".js") in
    (* When eval'ed, the js_code will return a closure waiting for the
       jsoo global object to link the plugin.
    *)
    Js.Unsafe.((eval_string ("(" ^ js_code ^ ")") : < .. > Js.t -> unit) global);
    Feedback.feedback (Feedback.FileLoaded(cmo_file, cmo_file));
  with
  | Sys_error _ ->
    eprintf "!! bytecode file %s not found in path. DYNLINK FAILED\n%!" cmo_file;
    raise @@ DynLinkFailed cmo_file

let register_cma ~file_path =
  let filename = Filename.basename file_path in
  let dir = Filename.dirname file_path in
  Hashtbl.add cma_cache filename dir

let rec last = function
    | [] -> None
    | [x] -> Some x
    | _ :: t -> last t

let is_intrinsic = function
    | "Coq" :: _ -> true
    | _ -> false

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

let require_libs libs =
  List.map (fun lp -> String.concat "." lp, None, Some true) libs
  (* Last coordinate: *)
  (*   None       : just require            *)
  (*   Some false : import but don't export *)
  (*   Some true  : import and export       *)

let coqpath_of_bundle ?(implicit=false) bundle =
  List.map (fun pkg ->
    path_to_coqpath ~implicit pkg.pkg_id
  ) bundle.pkgs

let path_of_dirpath dirpath =
  Names.(List.rev_map Id.to_string (DirPath.repr dirpath))

let module_name_of_qualid qualid =
  let (dirpath, id) = Libnames.repr_qualid qualid in
  (path_of_dirpath dirpath) @ [Names.Id.to_string id]

(* let module_name_of_reference ref =
 *   match ref with
 *   | Libnames.Ident id -> [Names.Id.to_string id]
 *   | Libnames.Qualid qid -> module_name_of_qualid qid *)
