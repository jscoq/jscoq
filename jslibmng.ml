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

(* We likely want these to be Hashtbls of just js arrays. *)
type cache_entry = {
  (* url        : Js.js_string; *)
  content    : Js.js_string Js.t;
  md5        : Digest.t;
  }

type byte_cache_entry = {
  md5     : Digest.t; (* Or other signature *)
  (* should this be a OCAML string? *)
  js_code : Js.js_string;
}

(* Main file_cache *)
let file_cache : (Js.js_string Js.t, cache_entry) Hashtbl.t =
  Hashtbl.create 100

let preload_file base_url (file, hash) : unit Lwt.t =
  let open XmlHttpRequest                       in
  (* Jslog.printf Jslog.jscoq_log "Start preload file %s\n%!" name; *)
  let full_url    = base_url ^ "/" ^ file in
  let request_url = "filesys/" ^ full_url in
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
         content = Js.bytestring (Bytes.to_string s);
         md5     = Digest.bytes s;
       } in
       Hashtbl.add file_cache (Js.string full_url) cache_entry;
       Jslog.printf Jslog.jscoq_log
         "Cached %s [%d/%d/%d/%s]\n%!"
          full_url bl (u8arr##length)
          (cache_entry.content##length)
          (Digest.to_hex cache_entry.md5)
      );
  Lwt.return_unit

let preload_pkg pkg : unit Lwt.t =
  let pkg_dir = to_name pkg.pkg_id in
  Jslog.printf Jslog.jscoq_log "pre-loading package %s\n%!" pkg_dir;
  Lwt_list.iter_s (preload_file pkg_dir) pkg.pkg_files >>= fun () ->
  Jscoq.add_load_path pkg.pkg_id pkg.with_ml pkg_dir;
  Lwt.return_unit

let init () = Lwt.async (fun () ->
  XmlHttpRequest.get "coq_pkg.json" >>= fun res ->
  let jpkg = Yojson.Basic.from_string res.content in
  match jpkg with
  | `List coq_pkgs ->
     Jslog.printf Jslog.jscoq_log "number of packages to preload %d\n%!" (List.length coq_pkgs);
    let pkgs = List.map Jslib.json_to_pkg coq_pkgs in
    Lwt_list.iter_s preload_pkg pkgs
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

let coq_resource_req url =
  (* Wait until we have enough UI support *)
  (* Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url); *)
  if not @@ is_bad_url url then
    try let c_entry = Hashtbl.find file_cache url in
        Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url);
        Js.Unsafe.global##lastCoqReq <- url;
        Some c_entry.content
    with Not_found ->
      (* Js.Unsafe.global##lastCoqReq <- Js.string "Not Found"; *)
      None
  else
    begin
      Js.Unsafe.global##lastCoqReq <- Js.string "Bad URL";
      None
    end

