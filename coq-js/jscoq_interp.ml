(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * Interpreter for the Coq communication protocol
 *)

open Js_of_ocaml
open Jscoq_proto.Proto
open Jslibmng

let opts = ref { implicit_libs = true; debug = {coq = false; stm = false} }

(* XXX *)
let post_message = ref (fun _ -> ())
let post_file = ref (fun _ _ _ -> ())
let interrupt_setup = ref (fun _ -> ())
(* End XXX *)

(** Message handlers **)
type progress_info =
  [%import: Jslibmng.progress_info]
  [@@deriving yojson]

type lib_event =
  [%import: Jslibmng.lib_event]
  [@@deriving yojson]

let post_lib_event le =
  lib_event_to_yojson le |> !post_message

let post_answer ans =
  jscoq_answer_to_yojson ans |> !post_message

let post_feedback fb =
  Feedback (Jscoq_util.fb_opt fb) |> post_answer

(** Coq stuff **)

(** When a new package is loaded, the library load path has to be updated *)
let update_loadpath (msg : lib_event) : unit =
  match msg with
  | LibLoaded (_,bundle) ->
    List.iter Loadpath.add_vo_path
      (Jslibmng.coqpath_of_bundle ~implicit:!opts.implicit_libs bundle)
  | _ -> ()

let process_lib_event (msg : lib_event) : unit =
  update_loadpath msg;
  post_lib_event msg

let mk_feedback ~span_id ?(route=0) contents =
  Feedback {doc_id = 0; span_id; route; contents}

let mk_vo_path l = Jslibmng.paths_to_coqpath ~implicit:!opts.implicit_libs l

(* set_opts  : general Coq initialization options *)
let exec_init (set_opts : jscoq_options) =

  let opts = (opts := set_opts; set_opts) in

  Icoq.coq_init ({
      ml_load      = Jslibmng.coq_cma_link;
      fb_handler   = post_feedback;
      aopts        = { enable_async = None;
                       async_full   = false;
                       deep_edits   = false;
                     };
      debug        = opts.debug.stm;
    })

(* opts  : document initialization options *)
let create_doc (opts : doc_options) =
  Icoq.new_doc ({
      top_name      = opts.top_name;
      mode          = opts.mode;
      require_libs  = Jslibmng.require_libs opts.lib_init;
      vo_path       = mk_vo_path opts.lib_path;
      opt_values    = opts.coq_options;
    })

(* I refuse to comment on this part of Coq code... *)
let exec_getopt opt =
  let open Goptions in
  let tbl = get_tables () in
  (OptionMap.find opt tbl).opt_value

let coq_exn_info exn =
    let (e, info) = Exninfo.capture exn in
    let pp_exn    = Jscoq_util.pp_opt @@ CErrors.iprint (e, info) in
    CoqExn (Loc.get_loc info, Stateid.get info, pp_exn)

(** Used by the Add command *)
let requires ast =
  match ast with
  | Vernacexpr.{ expr = VernacRequire (prefix, _export, module_refs); _ } ->
    let prefix_str = match prefix with
    | Some ref -> Jslibmng.module_name_of_qualid ref
    | _ -> [] in
    let module_refs_str = List.map (fun modref -> Jslibmng.module_name_of_qualid modref) module_refs in
    Some ((prefix_str, module_refs_str))
  | _ -> None
  [@@warning "-4"]

(* -- Used by Query command --*)

(* (Goals) *)

let pp_of_goals =
  let ppx env sigma x = Jscoq_util.pp_opt (Printer.pr_ltype_env env sigma x) in
  Serapi.Serapi_goals.get_goals_gen ppx

(* (Inspect) *)

let string_contains s1 s2 =  (* from Rosetta Code *)
  let len1 = String.length s1
  and len2 = String.length s2 in
  if len1 < len2 then false else
    let rec aux i =
      (i >= 0) && ((String.sub s1 i len2 = s2) || aux (pred i))
    in
    aux (len1 - len2)

let rec seq_append s1 s2 =  (* use batteries?? *)
  match s1 () with
  | Seq.Nil -> s2
  | Seq.Cons (x, xs) -> fun () -> Seq.Cons (x, seq_append xs s2)

let is_within qn prefix =
  let {Icoq.prefix = {dp}} = qn in
  Libnames.is_dirpath_prefix_of prefix dp

let symbols_for (q : search_query) env =
    match q with
    | Locals       -> Icoq.inspect_locals  ~env ()
    | CurrentFile  -> seq_append (Icoq.inspect_library ~env ())
                                 (Icoq.inspect_locals  ~env ())
    | _            -> Icoq.inspect_globals ~env ()
    [@@warning "-4"]

let filter_by (q : search_query) =
  match q with
  | All | CurrentFile | Locals -> (fun _ -> true)
  | ModulePrefix prefix -> (fun nm -> is_within nm prefix)
  | Keyword s -> (fun nm -> string_contains (Icoq.string_of_qualified_name nm) s)

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
      let CoqExn(loc,_,msg) = coq_exn_info exn [@@warning "-8"] in
      [mk_feedback ~span_id ~route (Message(Error, loc, msg ));
       mk_feedback ~span_id ~route Incomplete]
    end
  | Inspect q ->
    let _, env = Icoq.context_of_stm ~doc:(fst !doc) span_id in
    let symbols = symbols_for q env in
    let results = Seq.filter (filter_by q) symbols in
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
          let CoqExn(loc,_,msg) as exn_info = coq_exn_info exn [@@warning "-8"] in
          out_fn @@ mk_feedback ~span_id:newid (Message(Error, loc, msg));
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
    Jslibmng.register_cma ~file_path

  | Put (filename, content) -> begin
      try         Sys_js.create_file ~name:filename ~content
      with _e ->  Sys_js.update_file ~name:filename ~content
    end;
    if Jslibmng.is_bytecode filename then
      Jslibmng.register_cma ~file_path:filename

  | GetOpt opt          -> out_fn @@ CoqOpt (opt, exec_getopt opt)

  | Ast sid ->
    let ast = Stm.get_ast ~doc:(fst !doc) sid in
    out_fn @@ Ast ast

  | Init opts -> exec_init opts

  | NewDoc opts ->
    let ndoc, iid = create_doc opts in
    doc := Jscoq_doc.create ndoc;
    out_fn @@ Ready iid

  | LoadPkg(base, pkg)  ->
    Lwt.async (fun () -> Jslibmng.load_pkg process_lib_event base pkg)

  | InfoPkg(base, pkgs) ->
    Lwt.(async (fun () ->
        let coqv, coqd, ccd, ccv, cmag = Icoq.version               in
        let jsoov = Sys_js.js_of_ocaml_version                      in
        let header1 = Printf.sprintf
            "jsCoq (%s), Coq %s/%4d (%s),\n  compiled on %s\n"
            Jscoq_version.jscoq_version coqv (Int32.to_int cmag) coqd ccd in
        let header2 = Printf.sprintf
            "OCaml %s, Js_of_ocaml %s\n" ccv jsoov                  in
        Jslibmng.info_pkg post_lib_event base pkgs                  >>= fun () ->
        return @@ out_fn @@ CoqInfo (header1 ^ header2)
      ))

  | InterruptSetup shmem -> !interrupt_setup (Js.Unsafe.coerce shmem)

  | ReassureLoadPath load_path ->
    doc := Jscoq_doc.observe ~doc:!doc (Jscoq_doc.tip !doc); (* force current tip *)
    List.iter Loadpath.add_vo_path (mk_vo_path load_path)
  | Load filename ->
    doc := Jscoq_doc.load ~doc:!doc filename ~echo:false;
    out_fn @@ Loaded (filename, Jscoq_doc.tip !doc)
  | Compile filename ->
    !post_file "Compiled" filename (Icoq.compile_vo ~doc:(fst !doc) filename)
