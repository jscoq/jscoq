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

let post_feedback fb =
  Feedback (Jscoq_util.fb_opt fb) |> post_answer

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

let mk_feedback ~span_id ?(route=0) contents =
  Feedback {doc_id = 0; span_id; route; contents}

let mk_vo_path l = Jslib.paths_to_coqpath ~implicit:!opts.implicit_libs l

(* set_opts  : general Coq initialization options *)
let exec_init (set_opts : jscoq_options) =

  let opts = (opts := set_opts; set_opts) in

  !Callbacks.cb.pre_init ();

  Icoq.coq_init ({
      fb_handler   = post_feedback;
      aopts        = { enable_async = None;
                       async_full   = false;
                       deep_edits   = false;
                     };
      opt_values   = opts.coq_options;
      debug        = opts.debug.stm;
      vo_path      = mk_vo_path opts.lib_path;
    })

(* opts  : document initialization options *)
let create_doc (opts : doc_options) =
  Icoq.new_doc ({
      top_name      = opts.top_name;
      mode          = opts.mode;
      require_libs  = Jslib.require_libs opts.lib_init;
    })

(* I refuse to comment on this part of Coq code... *)
let exec_getopt opt =
  let open Goptions in
  let tbl = get_tables () in
  (OptionMap.find opt tbl).opt_value

let coq_exn_info exn =
  let (e, info) = Exninfo.capture exn in
  let pp_exn    = Jscoq_util.pp_opt @@ CErrors.iprint (e, info) in
  let msg = Format.asprintf "@[%a@]" Pp.pp_with pp_exn in
  CoqExn { loc = Loc.get_loc info; sid = Stateid.get info; msg; pp = pp_exn }

(** Used by the Add command *)
let requires ast =
  match ast with
  | Vernacexpr.{ expr = VernacRequire (prefix, _export, module_refs); _ } ->
    let prefix_str = match prefix with
    | Some ref -> Jslib.module_name_of_qualid ref
    | _ -> [] in
    let module_refs_str =
      (* XXX *)
      let module_refs = List.map fst module_refs in
      List.map (fun modref -> Jslib.module_name_of_qualid modref) module_refs
    in
    Some ((prefix_str, module_refs_str))
  | _ -> None
  [@@warning "-4"]

(** Goal printing *)
let pp_of_goals =
  let ppx env sigma x = Jscoq_util.pp_opt (Printer.pr_ltype_env env sigma x) in
  Serapi.Serapi_goals.get_goals_gen ppx

(** main Query handler *)
let exec_query doc ~span_id ~route query =
  let span_id = if span_id = Stateid.dummy then Jscoq_doc.tip !doc else span_id in
  match query with
  | Goals ->
    let doc = fst !doc in
    let goal_pp = pp_of_goals ~doc span_id in
    [GoalInfo (span_id, goal_pp)]
  | Mode ->
    let doc = fst !doc in
    let in_mode = Icoq.mode_of_stm ~doc span_id in
    [ModeInfo (span_id, in_mode)]
  | Vernac command ->
    begin try
      Jscoq_doc.query ~doc:!doc ~at:span_id ~route command;
      [mk_feedback ~span_id ~route Complete]
    with exn ->
      let CoqExn { loc; pp; _ } = coq_exn_info exn [@@warning "-8"] in
      [ mk_feedback ~span_id ~route (Message(Error, loc, pp ))
      ; mk_feedback ~span_id ~route Incomplete
      ]
    end
  | Inspect q ->
    let _, env = Icoq.context_of_stm ~doc:(fst !doc) span_id in
    let results = Code_info.symbols_for env q in
    [SearchResults (route, results)]

(** main interpreter *)
let jscoq_execute =
  let out_fn = post_answer in fun doc -> function
  | Add(ontop,newid,stm,resolved) ->
    if ontop = Jscoq_doc.tip !doc then begin
      try
        let ast = Jscoq_doc.parse ~doc:!doc ~ontop stm in
        let requires = if resolved then None else requires ast.CAst.v in
        match requires with
        | Some ((prefix, module_names)) ->
          out_fn @@ Pending (newid, prefix, module_names)
        | _ ->
          let loc,_tip_info,ndoc = Jscoq_doc.add ~doc:!doc ~ontop ~newid stm in
          doc := ndoc; out_fn @@ Added (newid,loc)
      with exn ->
        let CoqExn { loc; pp; _ } as exn_info = coq_exn_info exn [@@warning "-8"] in
        out_fn @@ mk_feedback ~span_id:newid (Message(Error, loc, pp));
        out_fn @@ Cancelled [newid];
        out_fn @@ exn_info
    end
    else out_fn @@ Cancelled [newid]

  | Cancel sid        ->
    let can_st, ndoc = Jscoq_doc.cancel ~doc:!doc sid in
    doc := ndoc; out_fn @@ Cancelled can_st

  | Exec sid          ->
    let ndoc = Jscoq_doc.observe ~doc:!doc sid in
    doc := ndoc

  | Query (sid, rid, query) ->
    exec_query doc ~span_id:sid ~route:rid query |> List.iter out_fn

  | Register file_path  ->
    !Callbacks.cb.register_cma ~file_path

  | Put (filename, content) ->
    !Callbacks.cb.write_file ~name:filename ~content;
    if Jslib.is_bytecode filename
    then !Callbacks.cb.register_cma ~file_path:filename

  | GetOpt opt          -> out_fn @@ CoqOpt (opt, exec_getopt opt)

  | Ast sid ->
    let ast = Stm.get_ast ~doc:(fst !doc) sid in
    out_fn @@ Ast ast

  | Init opts -> exec_init opts; out_fn @@ CoqInfo(coq_info_string ())

  | NewDoc opts ->
    let ndoc, iid = create_doc opts in
    doc := Jscoq_doc.create ndoc;
    out_fn @@ Ready iid

  | LoadPkg(base, pkg)  ->
    !Callbacks.cb.load_pkg ~base_path:base ~pkg ~cb:process_lib_event
  | InfoPkg(base, pkgs) ->
    !Callbacks.cb.info_pkg ~base_path:base ~pkgs ~cb:process_lib_event

  | InterruptSetup shmem -> !Callbacks.cb.interrupt_setup shmem

  | ReassureLoadPath load_path ->
    doc := Jscoq_doc.observe ~doc:!doc (Jscoq_doc.tip !doc); (* force current tip *)
    List.iter Loadpath.add_vo_path (mk_vo_path load_path)
  | Load filename ->
    doc := Jscoq_doc.load ~doc:!doc filename ~echo:false;
    out_fn @@ Loaded (filename, Jscoq_doc.tip !doc)
  | Compile filename ->
    let vo_out_fn = Icoq.compile_vo ~doc:(fst !doc) filename in
    !Callbacks.cb.post_file "Compiled" filename (!Callbacks.cb.read_file vo_out_fn)
