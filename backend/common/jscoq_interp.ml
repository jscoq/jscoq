(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * Interpreter for the Coq communication protocol
 *)

(* open Js_of_ocaml *)
open Jscoq_proto.Proto

open Jslib

module Callbacks = struct

  open LibManager

  type t =
    { pre_init : unit -> unit
    ; post_message : (Yojson.Safe.t -> unit)
    ; post_file : (string -> string -> string -> unit)
    ; interrupt_setup : (opaque -> unit)
    ; branding : string
    ; subsystem_version : string
    ; read_file : name:string -> string
    ; write_file : name:string -> content:string-> unit
    ; register_cma : file_path:string -> unit
    ; load_pkg : base_path:string -> pkg:string -> cb:(lib_event -> unit) -> unit
    ; info_pkg : base_path:string -> pkgs:string list -> cb:(lib_event -> unit) -> unit
    }

  let default =
    { pre_init = (fun () -> ())
    ; post_message = (fun _ -> ())
    ; post_file = (fun _ _ _ -> ())
    ; interrupt_setup = (fun _ -> ())
    ; branding = "xxCoq"
    ; subsystem_version = "??"
    ; read_file = (fun ~name:_ -> "")
    ; write_file = (fun ~name:_ ~content:_ -> ())
    ; register_cma = (fun ~file_path:_ -> ())
    ; load_pkg = (fun ~base_path:_ ~pkg:_ ~cb:_ -> ())
    ; info_pkg = (fun ~base_path:_ ~pkgs:_ ~cb:_ -> ())
    }

  let cb = ref default

  let set t = cb := t

end

let opts = ref
    { implicit_libs = true
    ; coq_options = []
    ; debug = {coq = false; stm = false}
    ; lib_path = []
    }

(** Message handlers **)
let post_lib_event le =
  LibManager.lib_event_to_yojson le |> !Callbacks.cb.post_message

let post_answer ans =
  jscoq_answer_to_yojson ans |> !Callbacks.cb.post_message

(* XXX: Fixme, version should use the one in the document *)
let post_notification fb version = Notification ([fb],version) |> post_answer

(** Coq stuff **)

let coq_info_string () =
  let coqv, ccv, cmag = Icoq.version                          in
  let subsys = !Callbacks.cb.subsystem_version                in
  let header1 = Printf.sprintf
      "jsCoq (%s), Coq %s/%4d\n"
      Jscoq_version.jscoq_version coqv (Int32.to_int cmag)    in
  let header2 = Printf.sprintf
      "OCaml %s, %s\n" ccv subsys                             in
  header1 ^ header2

(** When a new package is loaded, the library load path has to be updated *)
let update_loadpath (msg : LibManager.lib_event) : unit =
  match msg with
  | LibLoaded (_,bundle) ->
    List.iter Loadpath.add_vo_path
      (Jslib.Coq_bundle.coqpath ~implicit:!opts.implicit_libs bundle)
  | _ -> ()

let process_lib_event (msg : LibManager.lib_event) : unit =
  update_loadpath msg;
  post_lib_event msg

let mk_vo_path l = Jslib.paths_to_coqpath ~implicit:!opts.implicit_libs l

(* set_opts  : general Coq initialization options *)
let exec_init (set_opts : jscoq_options) =

  let opts = (opts := set_opts; set_opts) in

  (* Moved, but still need to improve *)
  (* !Callbacks.cb.pre_init (); *)

  Icoq.coq_init ({
      notification_cb = post_notification;
      (* opt_values   = opts.coq_options; *)
      debug        = opts.debug.stm;
    });

  (* This is technically wrong, as coq_init needs to enable the serlib
     instrumentation, but that requires a findlib-enabled loader. *)
  !Callbacks.cb.pre_init ()

(* opts  : document initialization options *)
let create_doc (doc_opts : doc_options) =
  let opts =
    { Icoq.uri = "file:///browser.v"
    ; opt_values = []
    ; vo_path = mk_vo_path !opts.lib_path
    ; require_libs  = Jslib.require_libs doc_opts.lib_init;
    }
  in
  Icoq.new_doc opts

let doc = ref (Obj.magic 0)

(** main interpreter *)
let jscoq_execute =
  let out_fn = post_answer in function

  | Init opts ->
    exec_init opts; out_fn @@ CoqInfo(coq_info_string ())

  | NewDoc (opts, text, markdown) ->
    let ndoc, _st, diags = create_doc opts markdown text in
    doc := ndoc;
    out_fn @@ Ready ();
    out_fn (Notification (diags,1))

  | Update (contents, version) ->
    let ndoc = { !doc with contents } in
    let ndoc, _state, diags = Icoq.check_doc ~doc:ndoc in
    doc := ndoc;
    out_fn (Notification (diags, version))

  | Request q ->
    let f = Request_interp.do_request ~doc:!doc in
    let res = Request.process ~f q in
    out_fn (Response res)

  | Register file_path  ->
    !Callbacks.cb.register_cma ~file_path

  | Put (filename, content) ->
    !Callbacks.cb.write_file ~name:filename ~content;
    if Jslib.is_bytecode filename
    then !Callbacks.cb.register_cma ~file_path:filename

  | LoadPkg(base, pkg)  ->
    !Callbacks.cb.load_pkg ~base_path:base ~pkg ~cb:process_lib_event
  | InfoPkg(base, pkgs) ->
    !Callbacks.cb.info_pkg ~base_path:base ~pkgs ~cb:process_lib_event

  | InterruptSetup shmem -> !Callbacks.cb.interrupt_setup shmem
