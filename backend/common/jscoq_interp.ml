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
    { load_module : string -> unit
    ; load_plugin : Mltop.PluginSpec.t -> unit
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
    { load_module = (fun _ -> ())
    ; load_plugin = (fun _ -> ())
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
    ; debug = false
    ; lib_path = []
    ; lib_init = []
    }

(** Message handlers **)
let post_lib_event le =
  LibManager.lib_event_to_yojson le |> !Callbacks.cb.post_message

let post_answer ans =
  jscoq_answer_to_yojson ans |> !Callbacks.cb.post_message

(** Coq stuff **)
let version =
  Coq_config.version, Coq_config.caml_version, Coq_config.vo_version

let coq_info_string () =
  let coqv, ccv, cmag = version                               in
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

(* State of the interpreter after init XXX, refactor *)
let cur_workspace = ref None
let root_state =
  let st = Vernacstate.freeze_full_state () in
  ref (Coq.State.of_coq st)

let lsp_cb =
  let perfData ~uri:_ ~version:_ { Fleche.Perf.summary = _; _ } = () in
    (* Format.(eprintf "[perfdata]@\n@[%s@]@\n%!" summary) in *)

  let serverVersion _ = () in
  let serverStatus _ = () in

  let out_fn = post_answer in
  Fleche.Io.CallBack.
    { trace = (fun cat ?extra:_ msg -> Format.eprintf "[%s] %s@\n%!" cat msg)
    ; message = (fun ~lvl:_ ~message:_ -> ())
    ; diagnostics = (fun ~uri:_ ~version diags ->
          out_fn (Notification (diags,version)))
    ; fileProgress = (fun ~uri:_ ~version:_ _progress -> ())
    ; perfData
    ; serverVersion
    ; serverStatus
    }

(* set_opts  : general Coq initialization options *)
let exec_init (set_opts : init_options) =

  let opts = (opts := set_opts; set_opts) in

  (* Moved, but still need to improve *)
  (* !Callbacks.cb.pre_init (); *)

  Fleche.Io.CallBack.set lsp_cb;

  (* jsCoq-specific flags *)
  Global.set_VM false;
  Global.set_native_compiler false;

  let st = Coq.Init.coq_init (
    { debug        = opts.debug
    ; load_plugin = !Callbacks.cb.load_plugin
    ; load_module = !Callbacks.cb.load_module
    })
  in
  root_state := st

(* opts  : workspace initialization options *)
let init_workspace ~token ~dir opts =
  let vo_load_path = mk_vo_path opts.lib_path in
  let cmdline = Coq.Workspace.CmdLine.
      { coqlib = "/lib"
      ; coqcorelib = "/lib"
      ; ocamlpath = Some "/lib"
      ; args = ["-boot"]
      ; require_libraries = []
      ; vo_load_path
      ; ml_include_path = []
      }
  in
  Coq.Workspace.guess ~token ~debug:opts.debug ~dir ~cmdline

(** XXX Error better when the workspace was not initialized *)
let get_ws () = Option.get !cur_workspace

let try_check ~token =
  let io = lsp_cb in
  match Fleche.Theory.Check.maybe_check ~token ~io with
  | None -> ()
  | Some (_wake_up, _doc) -> ()

(** main interpreter *)
let jscoq_execute =
  let out_fn = post_answer in fun ~token -> function
  | Init opts ->
    exec_init opts;
    out_fn @@ CoqInfo(coq_info_string ());
    let dir = "/src" in
    (match init_workspace ~token ~dir opts with
    | Ok workspace ->
      cur_workspace := Some workspace;
      out_fn @@ Ready ()
    | Error _ -> ())

  | NewDoc { uri; version; raw } ->
    let io = lsp_cb in
    let workspace = get_ws () in
    let init = !root_state in
    let files = Coq.Files.make () in
    let env = Fleche.Doc.Env.make ~init ~workspace ~files in
    Fleche.Theory.create ~io ~token ~env ~uri ~version ~raw;
    try_check ~token;
    ()

  | Update { uri; version; raw } ->
    let io = lsp_cb in
    let _stale_request : Int.Set.t = Fleche.Theory.change ~io ~token ~uri ~version ~raw in
    try_check ~token;
    ()

  | Request { uri; method_ } ->
    let { Request.id; loc = _; v = _ } = method_ in
    (* XXX Fix to use position *)
    let postpone = true in
    let r = Fleche.Theory.Request.{ id; uri; postpone; request = FullDoc } in
    (* XXX Fix to postpone requests *)
    let () = match Fleche.Theory.Request.add r with
      | Now doc ->
        let f = Request_interp.do_request ~token ~doc in
        let res = Request.process ~f method_ in
        out_fn (Response res)
      | Postpone -> ()
      | Cancel -> () in
    try_check ~token

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
