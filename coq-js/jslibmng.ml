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
open Js

let pkg_prefix    = ref ""
let bcache_prefix = "bcache/"
let bcache_file   = "bcache.list"

(* Main byte_cache *)
let byte_cache : (Digest.t, js_string t) Hashtbl.t = Hashtbl.create 200

(* Main file_cache, indexed by url*)
type cache_entry = {
  vo_content : js_string t;
  md5        : Digest.t;
}

(* We'll likely want these to be Hashtbls of js typed arrays. *)
let file_cache : (js_string t, cache_entry) Hashtbl.t = Hashtbl.create 100

(* The special cma cache has been disabled, for now we have a bytecode
   cache. *)
(* let cma_cache *)

(* XXX This should be the serialization of the jslib.ml:coq_pkg, but
   waiting for JSON support *)
class type pkgInfo = object
  method name        : js_string t writeonly_prop
  method desc        : js_string t writeonly_prop
  method no_files_   : int         writeonly_prop
end

class type bundleInfo = object
  method desc        : js_string t            writeonly_prop
  method deps        : js_string t js_array t writeonly_prop
  method pkgs        : pkgInfo   t js_array t writeonly_prop
end

class type progressInfo = object
  method bundle_name_ : js_string t writeonly_prop
  method pkg_name_    : js_string t writeonly_prop
  method loaded       : int         writeonly_prop
  method total        : int         writeonly_prop
end

let mk_pkgInfo pkg : pkgInfo t =
  let pi      = Js.Unsafe.obj [||]   in
  pi##name      <- string @@ to_dir  pkg;
  pi##desc      <- string @@ to_desc pkg;
  pi##no_files_ <- no_files pkg;
  pi

let build_bundle_info bundle : bundleInfo t =
  let bi      = Js.Unsafe.obj [||]   in
  let bi_deps = Js.array @@ Array.of_list @@ List.map Js.string  bundle.deps in
  let bi_pkgs = Js.array @@ Array.of_list @@ List.map mk_pkgInfo bundle.pkgs in
  bi##desc <- string bundle.desc;
  bi##deps <- bi_deps;
  bi##pkgs <- bi_pkgs;
  bi

let mk_progressInfo bundle pkg number =
  let pi           = Js.Unsafe.obj [||]   in
  pi##bundle_name_ <- string bundle;
  pi##pkg_name_    <- string @@ to_dir pkg;
  pi##total        <- no_files pkg;
  pi##loaded       <- number;
  pi

(* Global Callbacks *)
type pkg_callbacks = {
  pkg_info     : bundleInfo   t -> unit;
  pkg_start    : progressInfo t -> unit;
  pkg_progress : progressInfo t -> unit;
  pkg_load     : progressInfo t -> unit;
}

let cb : pkg_callbacks ref = ref {
  pkg_info     = (fun _ -> ());
  pkg_start    = (fun _ -> ());
  pkg_progress = (fun _ -> ());
  pkg_load     = (fun _ -> ());
  }

(* Preload some code based on its md5 *)
let preload_js_code msum =
  let open Lwt                           in
  let open XmlHttpRequest                in
  let js_url = bcache_prefix ^ msum      in
  perform_raw ~response_type:Text js_url >>= fun frame      ->
  Hashtbl.add byte_cache (Digest.from_hex msum) frame.content;
  return_unit

let preload_byte_cache () =
  let open Lwt            in
  let open XmlHttpRequest in
  (* Don't fail if bcache.list doesn't exist *)
  catch (fun () ->
      XmlHttpRequest.get bcache_file                 >>= fun res ->
      let m_list = Regexp.split (Regexp.regexp "\n") res.content in
      Firebug.console##log_2(string "Got binary js cache: ",
                             string (string_of_int (List.length m_list)));
      Lwt_list.iter_s preload_js_code m_list)
  (* try *)
    (fun _exn ->
       Firebug.console##log(string @@ "Downloading " ^ bcache_file ^ " failed");
       return_unit
    )
  (* Firebug.console##log_2(string "bcache file: ", string res.content); *)
  (* Firebug.console##log_2(string "number of files", List.length m_list); *)

(* Query the ocaml bytecode cache *)
let request_byte_cache (md5sum : Digest.t) =
  try Some (Hashtbl.find byte_cache md5sum)
  with | Not_found -> None

let preload_vo_file base_url (file, _hash) : unit Lwt.t =
  let open XmlHttpRequest                       in
  (* Jslog.printf Jslog.jscoq_log "Start preload file %s\n%!" name; *)
  let full_url    = base_url  ^ "/" ^ file in
  let request_url = !pkg_prefix ^ full_url  in
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
         (* XXX: We'd like to avoid the expensive md5 here but, misteries of javascript!
            if we don't do the md5, we'll eat memory too fast and the browser will crash!
         *)
         (* md5        = Digest.string ""; *)
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
let _preload_cma_file base_url (file, _hash) : unit Lwt.t =
  Format.eprintf "pre-loading cma file %s-%s\n%!" base_url file;
  let cma_url   = !pkg_prefix ^ "cmas/" ^ file ^ ".js" in
  Format.eprintf "cma url %s\n%!" cma_url;
  (* Avoid costly string conversions *)
  let open XmlHttpRequest in
  perform_raw ~response_type:Text cma_url >>= fun frame ->
  (if frame.code = 200 || frame.code = 0 then
    let _byte_entry = frame.content in
    Format.eprintf "added cma %s with length %d\n%!" cma_url (frame.content)##length;
    (* XXXX: This  called without qualitification so filename conflicts are possible *)
    (* Hashtbl.add byte_cache (Js.string file) byte_entry) *)
    ())
  ;
  Lwt.return_unit

let preload_pkg ?(verb=false) bundle pkg : unit Lwt.t =
  let pkg_dir = to_dir pkg                                           in
  let ncma    = List.length pkg.cma_files                            in
  let nfiles  = no_files pkg                                         in
  if verb then
    Format.eprintf "pre-loading package %s, [00/%02d] files\n%!" pkg_dir nfiles;
  !cb.pkg_start (mk_progressInfo bundle pkg 0);
  let preload_vo_and_log nc i f =
    preload_vo_file pkg_dir f >>= fun () ->
    if verb then
      Format.eprintf "pre-loading package %s, [%02d/%02d] files\n%!" pkg_dir (i+nc+1) nfiles;
    !cb.pkg_progress (mk_progressInfo bundle pkg (i+nc+1));
    Lwt.return_unit
  in
  (if Icoq.dyn_comp then
    Lwt_list.iteri_s (preload_vo_and_log 0) pkg.cma_files
  else
    return_unit
    (* For now, CMA files are no special *)
    (* Lwt_list.iter_s (preload_cma_file pkg_dir) pkg.cma_files *)
  ) >>= fun () ->
  Lwt_list.iteri_s (preload_vo_and_log ncma) pkg.vo_files     >>= fun () ->
  Icoq.add_load_path pkg.pkg_id pkg_dir (ncma > 0);
  !cb.pkg_load (mk_progressInfo bundle pkg nfiles);
  Lwt.return_unit

let rec preload_from_file ?(verb=false) file =
  let file_url = !pkg_prefix ^ file ^ ".json" in
  XmlHttpRequest.get file_url >>= (fun res ->
  (* XXX: Use _JSON.json??????? *)
  let bundle = try Jslib.json_to_bundle
                     (Yojson.Basic.from_string res.XmlHttpRequest.content)
               with | _ -> (Format.eprintf "JSON error in preload_from_file\n%!";
                            raise (Failure "JSON"))
  in
  (* !cb.pkg_info (build_bundle_info bundle); *)
  (* Load deps *)
  Lwt_list.iter_s (preload_from_file ~verb:verb) bundle.deps >>= fun () ->
  Lwt_list.iter_s (preload_pkg ~verb:verb file) bundle.pkgs)

let iter_arr (f : 'a -> unit Lwt.t) (l : 'a js_array t) : unit Lwt.t =
  let f_js = wrap_callback (fun p x _ _ -> f x >>= (fun () -> p)) in
  l##reduce_init(f_js, return_unit)

let info_from_file file =
  let file_url = !pkg_prefix ^ file ^ ".json" in
  XmlHttpRequest.get file_url >>= fun res ->
  let bundle = try Jslib.json_to_bundle
                     (Yojson.Basic.from_string res.XmlHttpRequest.content)
               with | _ -> (Format.eprintf "JSON error in preload_from_file\n%!";
                            raise (Failure "JSON"))
  in
  return @@ !cb.pkg_info (build_bundle_info bundle)

let init init_callback pkg_cb pkg_path all_pkgs init_pkgs =
  cb         := pkg_cb;
  pkg_prefix := to_string pkg_path ^ "/";
  Lwt.async (fun () ->
    preload_byte_cache ()                                                      >>= fun () ->
    iter_arr (fun x -> to_string x |> info_from_file)                all_pkgs  >>= fun () ->
    iter_arr (fun x -> to_string x |> preload_from_file ~verb:false) init_pkgs >>= fun () ->
    init_callback ();
    return_unit
  )

let load_pkg pkg_file = Lwt.async (fun () ->
    preload_from_file pkg_file >>= fun () ->
    (* XXX: No notification for bundle loading *)
    (* !cb.bundle_load pkg_file; *)
    return_unit
  )

let _is_bad_url _ = false

(* XXX: Wait until we have enough UI support for logging *)
let coq_vo_req url =
  (* Format.eprintf "file %s requested\n%!" (to_string url); (\* with category info *\) *)
  (* if not @@ is_bad_url url then *)
  try let c_entry = Hashtbl.find file_cache url in
    (* Jslog.printf Jslog.jscoq_log "coq_resource_req %s\n%!" (Js.to_string url); *)
    Some c_entry.vo_content
  with
      (* coq_vo_reg is also invoked throught the Sys.file_exists call
         in mltop:file_of_name function, a good example on how to be
         too smart for your own good $:-) *)
    Not_found -> None
(*
        (* Check for a hit in the cma cache, return the empty string *)
        if Filename.check_suffix (to_string url) ".cma" && Hashtbl.mem byte_cache url then
          Some (string "")
        else None
*)
(*
  else
    begin
      Js.Unsafe.global##lastCoqReq <- Js.string "Bad URL";
      None
    end
*)

let coq_cma_req cma =
  Format.eprintf "cma file %s requested\n%!" cma;
  let str = (Js.string (!pkg_prefix ^ "cmas/" ^ cma ^ ".js")) in
  Js.Unsafe.global##load_script_(str)
(*
  try let js_code = Hashtbl.find byte_cache (Js.string cma) in
      let js_code = Js.to_string js_code.js_content         in
      Jslog.printf Jslog.jscoq_log "executing js code %s\n%!" js_code;
      Js.Unsafe.eval_string js_code
      (* Js.Unsafe.global##eval js_code.js_content *)
  with Not_found -> ()
*)
