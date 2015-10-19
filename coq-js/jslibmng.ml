(* JsCoq
 * Copyright (C) 2015 Emilio Gallego / Mines ParisTech
 *
 * LICENSE: GPLv3+
 *)

(* Library management for JsCoq

   Due to the large size of Coq libraries, we wnat to perform caching
   and lazy loading in the browser.
*)
open Jslib
open Lwt

let json_file = "coq_pkg.json"
let fs_prefix = "coq-fs/"

(* We likely want these to be Hashtbls of just js arrays. *)
type cache_entry = {
  vo_content : Js.js_string Js.t;
  md5        : Digest.t;
}

type byte_cache_entry = {
  js_content : Js.js_string Js.t;
  (* md5        : Digest.t; (\* Or other signature *\) *)
  (* Should this be a OCAML string given the signature of eval_string? *)
}

(* Main file_cache *)
let file_cache : (Js.js_string Js.t, cache_entry) Hashtbl.t =
  Hashtbl.create 100

let byte_cache : (Js.js_string Js.t, byte_cache_entry) Hashtbl.t =
  Hashtbl.create 50

let preload_vo_file base_url (file, hash) : unit Lwt.t =
  let open XmlHttpRequest                       in
  (* Jslog.printf Jslog.jscoq_log "Start preload file %s\n%!" name; *)
  let full_url    = base_url  ^ "/" ^ file in
  let request_url = fs_prefix ^ full_url   in
  perform_raw ~response_type:ArrayBuffer request_url >>= fun frame ->
  (* frame.code contains the request status *)
  (* Is this redudant with the Opt check? I guess so *)
  if frame.code = 200 || frame.code = 0 then
    Js.Opt.case
      frame.content
      (fun ()        -> ())
      (fun raw_array ->
       let bl    = raw_array##byteLength                              in
       let u8arr = jsnew Typed_array.uint8Array_fromBuffer(raw_array) in
       (* Add to file cache, pity of all the unneeded marshalling *)
       let s = Bytes.create bl in
       for i = 0 to bl - 1 do
         Bytes.set s i @@ Char.chr @@ Typed_array.unsafe_get u8arr i
       done;
       let cache_entry = {
         vo_content = Js.bytestring (Bytes.to_string s);
         md5        = Digest.bytes s;
       } in
       Hashtbl.add file_cache (Js.string full_url) cache_entry;
       ()
       (* Jslog.printf Jslog.jscoq_log "Cached %s [%d]\n%!" full_url bl *)
       (*
       Jslog.printf Jslog.jscoq_log
         "Cached %s [%d/%d/%d/%s]\n%!"
          full_url bl (u8arr##length)
          (cache_entry.vo_content##length)
          (Digest.to_hex cache_entry.md5)
        *)
      );
  Lwt.return_unit

(* Unfortunately this is a tad different than preload_vo_file *)
let preload_cma_file base_url (file, hash) : unit Lwt.t =
  (* Jslog.printf Jslog.jscoq_log "pre-loading cma file %s-%s\n%!" base_url file; *)
  Format.eprintf "pre-loading cma file %s-%s\n%!" base_url file;
  let cma_url   = fs_prefix ^ "cmas/" ^ file ^ ".js" in
  (* Jslog.printf Jslog.jscoq_log "cma url %s\n%!" cma_url; *)
  Format.eprintf "cma url %s\n%!" cma_url;
  (* Avoid costly string conversions *)
  let open XmlHttpRequest in
  perform_raw ~response_type:Text cma_url >>= fun frame ->
  (if frame.code = 200 || frame.code = 0 then
    let byte_entry = {
      js_content = frame.content;
    } in
    Format.eprintf "added cma %s with length %d\n%!" cma_url (frame.content)##length;
    (* Jslog.printf Jslog.jscoq_log "added cma %s with length %d\n%!" cma_url (frame.content)##length; *)

    (* XXXX: This  called without qualitification so
       filename conflicts are possible *)
    Hashtbl.add byte_cache (Js.string file) byte_entry)
  ;
  Lwt.return_unit

let preload_pkg pkg : unit Lwt.t =
  let pkg_dir = to_name pkg.pkg_id        in
  let ncma    = List.length pkg.cma_files in
  let nfiles  = List.length pkg.vo_files + List.length pkg.cma_files in
  (* Jslog.printf Jslog.jscoq_log "pre-loading package %s, [00/%02d] files\n%!" pkg_dir nfiles; *)
  Format.eprintf "pre-loading package %s, [00/%02d] files\n%!" pkg_dir nfiles;
  let preload_vo_and_log nc i f =
    preload_vo_file pkg_dir f >>= fun () ->
    (* Jslog.printf_rep Jslog.jscoq_log "pre-loading package %s, [%02d/%02d] files\n%!" pkg_dir (i+nc+1) nfiles; *)
    Format.eprintf "pre-loading package %s, [%02d/%02d] files\n%!" pkg_dir (i+nc+1) nfiles;
    Lwt.return_unit
  in
  (if Icoq.dyn_comp then
    Lwt_list.iteri_s (preload_vo_and_log 0) pkg.cma_files
  else
    Lwt_list.iter_s (preload_cma_file pkg_dir) pkg.cma_files) >>= fun () ->
  Lwt_list.iteri_s (preload_vo_and_log ncma) pkg.vo_files     >>= fun () ->
  Icoq.add_load_path pkg.pkg_id pkg_dir;
  Lwt.return_unit

let init callback = Lwt.async (fun () ->
  XmlHttpRequest.get json_file >>= fun res ->
  let jpkg = Yojson.Basic.from_string res.XmlHttpRequest.content in
  match jpkg with
  | `List coq_pkgs ->
    let open List in
    let pkgs = List.map Jslib.json_to_pkg coq_pkgs in
    (* Jslog.printf Jslog.jscoq_log "number of packages to preload %d [%d files]\n%!" *)
    Format.eprintf "number of packages to preload %d [%d files]\n%!"
      (length coq_pkgs)
      (fold_left (+) 0
         (map (fun pkg -> length pkg.vo_files + length pkg.cma_files) pkgs));
    Lwt_list.iter_s preload_pkg pkgs >>= fun _ ->
    (callback (); Lwt.return_unit)
  | _ -> raise (Failure "JSON");
)


(*
  let handler xml =
      let md5 = Digest.md5 xml##contents (casts, etc...)
      if md5 <> hash then
         notifyError(base_url + name);
      add_to_cache contents ...;
      let next () =
        if cma then
           preload_bytecode md5
	else cont ()
      do_next ()
 *)

let is_bad_url _ = false

let coq_vo_req url =
  (* Wait until we have enough UI support *)
  (* Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url); *)
  if not @@ is_bad_url url then
    try let c_entry = Hashtbl.find file_cache url in
        (* Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url); *)
        Js.Unsafe.global##lastCoqReq <- url;
        Some c_entry.vo_content
    with
      (* coq_vo_reg is also invoked throught the Sys.file_exists call
         in mltop:file_of_name function, a good example on how to be
         too smart for your own good $:-) *)
      Not_found ->
        (* Check for a hit in the cma cache, return the empty string *)
        if Filename.check_suffix (Js.to_string url) ".cma" && Hashtbl.mem byte_cache url then
          Some (Js.string "")
        else None
      (* Js.Unsafe.global##lastCoqReq <- Js.string "Not Found"; *)
  else
    begin
      Js.Unsafe.global##lastCoqReq <- Js.string "Bad URL";
      None
    end

let coq_cma_req cma =
  (* Jslog.printf Jslog.jscoq_log "cma file %s requested\n%!" cma; *)
  Format.eprintf "cma file %s requested\n%!" cma;
  let str = (Js.string (fs_prefix ^ "cmas/" ^ cma ^ ".js")) in
  Js.Unsafe.global##load_script_(str)
(*
  try let js_code = Hashtbl.find byte_cache (Js.string cma) in
      let js_code = Js.to_string js_code.js_content         in
      Jslog.printf Jslog.jscoq_log "executing js code %s\n%!" js_code;
      Js.Unsafe.eval_string js_code
      (* Js.Unsafe.global##eval js_code.js_content *)
  with Not_found -> ()
*)
