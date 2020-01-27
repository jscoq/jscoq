(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2020 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2020 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq.
 *)

open Js_of_ocaml
open Jscoqlib
open Jscoq_proto.Proto

let opts = ref { top_name = "JsCoq"; implicit_libs = true; stm_debug = false; coq_options = [] }

let jsCoq = Js.Unsafe.obj [||]

let rec json_to_obj (cobj : < .. > Js.t) (json : Yojson.Safe.t) : < .. > Js.t =
  let open Js.Unsafe in
  let ofresh j = json_to_obj (obj [||]) j in
  match json with
  | `Bool b   -> coerce @@ Js.bool b
  | `Null     -> pure_js_expr "undefined"
  | `Assoc l  -> List.iter (fun (p, js) -> set cobj p (ofresh js)) l; cobj
  | `List  l  -> Array.(Js.array @@ map ofresh (of_list l))
  | `Float f  -> coerce @@ Js.number_of_float f
  | `String s -> coerce @@ Js.string s
  | `Int m    -> coerce @@ Js.number_of_float (Obj.magic m)
  | `Intlit s -> coerce @@ Js.number_of_float (float_of_string s)
  | `Tuple t  -> Array.(Js.array @@ map ofresh (of_list t))
  | `Variant(_,_) -> pure_js_expr "undefined"

let rec obj_to_json (cobj : < .. > Js.t) : Yojson.Safe.t =
  let open Js in
  let open Js.Unsafe in
  let typeof_cobj = to_string (typeof cobj) in
  match typeof_cobj with
  | "string"  -> `String (to_string @@ coerce cobj)
  | "boolean" -> `Bool (to_bool @@ coerce cobj)
  | "number"  -> `Int (int_of_float @@ float_of_number @@ coerce cobj)
  | _ ->
    if instanceof cobj array_empty then
      `List Array.(to_list @@ map obj_to_json @@ to_array @@ coerce cobj)
    else if instanceof cobj Typed_array.arrayBuffer then
      `String (Typed_array.String.of_arrayBuffer @@ coerce cobj)
    else
      let json_string = Js.to_string (Json.output cobj) in
      Yojson.Safe.from_string json_string

(* This is an internal js_of_ocaml primitive... *)
external string_bytes : string -> Typed_array.uint8Array Js.t = "caml_array_of_string"

(* (following is a reference implementation)
let string_bytes s : Typed_array.uint8Array Js.t =
  let ta = new%js Typed_array.uint8Array (String.length s) in
  String.iteri (fun i c -> Typed_array.set ta i (Char.code c)) s;
  ta *)

let buffer_of_uint8array array =    (* pretty much copied from CoqWorker.put  :| *)
  let open Js.Unsafe in
  let buffer = array##.buffer in
  if Int.equal array##.byteOffset 0 && Int.equal array##.byteLength buffer##.byteLength then
    array, buffer
  else
    let buffer = (coerce buffer)##slice array##.byteOffset array##.byteLength in
    new%js Typed_array.uint8Array_fromBuffer buffer, buffer

external interrupt_setup : Typed_array.int32Array Js.t -> unit = "interrupt_setup"

let _answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg                            in
  let json_str = Yojson.Safe.to_string json_msg                        in
  (* Workaround to avoid ml_string conversion of Json.unsafe_input     *)
  Js._JSON##(parse (Js.string json_str))

let answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg       in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

type progress_info =
  [%import: Jscoqlib.Jslibmng.progress_info]
  [@@deriving yojson]

type lib_event =
  [%import: Jscoqlib.Jslibmng.lib_event]
  [@@deriving yojson]

let lib_event_to_jsobj msg =
  let json_msg = lib_event_to_yojson msg          in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

let is_worker =
  let open Js.Unsafe in
  global##.WorkerGlobalScope != Js.undefined && global##.self != Js.undefined &&
    pure_js_expr "self instanceof WorkerGlobalScope"

let post_message : < .. > Js.t -> unit =
  if is_worker then Worker.post_message
  else
    fun msg -> Js.Unsafe.fun_call (jsCoq##.onmessage) [|Js.Unsafe.inject msg|]

(* Send messages to the main thread *)
let post_answer (msg : jscoq_answer) : unit =
  post_message (answer_to_jsobj msg)

let post_lib_event (msg : lib_event) : unit =
  Worker.post_message (lib_event_to_jsobj msg)

let post_file filename content : unit =
  let open Js.Unsafe in
  let array, buf = buffer_of_uint8array (string_bytes content) in
  let msg = Js.array [|inject @@ Js.string "Got";
                       inject @@ Js.string filename;
                       inject @@ array|] in
  if is_worker then
    Js.Unsafe.global##postMessage msg (Js.array [|buf|])  (* use `transfer` *)
  else
    post_message msg

(* When a new package is loaded, the library load path has to be updated *)
let update_loadpath (msg : lib_event) : unit =
  match msg with
  | LibLoaded (_,bundle) ->
    List.iter Loadpath.add_coq_path
      (Jslibmng.coqpath_of_bundle ~implicit:!opts.implicit_libs bundle)
  | _ -> ()
  [@@warning "-4"]

let process_lib_event (msg : lib_event) : unit =
  update_loadpath msg ; post_lib_event msg

(* set_opts  : general options *)
(* lib_init  : list of modules to load *)
(* lib_path  : list of load paths *)
let exec_init (set_opts : jscoq_options) (lib_init : string list list) (lib_path : (string list * string list) list) =

  opts := set_opts;
  let opts = set_opts in

  let lib_require  = List.map (fun lp ->
      String.concat "." lp, None, Some true) lib_init  in

  (* None       : just require            *)
  (* Some false : import but don't export *)
  (* Some true  : import and export       *)

  Icoq.(coq_init {
      ml_load      = Jslibmng.coq_cma_link;
      fb_handler   = (fun fb -> post_answer (Feedback (Jscoq_util.fb_opt fb)));
      require_libs = lib_require;
      iload_path   = List.map (fun (path_el, phys) ->
                         Jslibmng.path_to_coqpath ~implicit:opts.implicit_libs ~unix_prefix:phys path_el
                     ) lib_path;
      top_name     = set_opts.top_name;
      opt_values   = set_opts.coq_options;
      aopts        = { enable_async = None;
                       async_full   = false;
                       deep_edits   = false;
                     };
      debug    = opts.stm_debug;
    })

(* I refuse to comment on this part of Coq code... *)
let exec_getopt opt =
  let open Goptions in
  let tbl = get_tables () in
  (OptionMap.find opt tbl).opt_value

let coq_exn_info exn =
    let (e, info) = CErrors.push exn                   in
    let pp_exn    = Jscoq_util.pp_opt @@ CErrors.iprint (e, info) in
    CoqExn (Loc.get_loc info, Stateid.get info, pp_exn)

(* -- Used by Add command -- *)

let requires ast =
  match ast with
  | Vernacexpr.{ expr = VernacRequire (prefix, _export, module_refs)} ->
    let prefix_str = match prefix with
    | Some ref -> Jslibmng.module_name_of_qualid ref
    | _ -> [] in
    let module_refs_str = List.map (fun modref -> Jslibmng.module_name_of_qualid modref) module_refs in
    Some ((prefix_str, module_refs_str))
  | _ -> None
  [@@warning "-4"]

(* -- Used by Inspect command --*)

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

let is_within path prefix =
  let dp, _ = Libnames.repr_path path in
  Libnames.is_dirpath_prefix_of prefix dp

let symbols_for (q : search_query) env =
    match q with
    | Locals       -> Icoq.inspect_locals  ~env ()
    | CurrentFile  -> seq_append (Icoq.inspect_library ~env ())
                                 (Icoq.inspect_locals  ~env ())
    | _            -> Icoq.inspect_globals ~env ()
    [@@warning "-4"]

let pp_of_goals =
  let ppx env sigma x = Jscoq_util.pp_opt (Printer.pr_ltype_env env sigma x) in
  Serapi.Serapi_goals.get_goals_gen ppx

let filter_by (q : search_query) =
  match q with
  | All | CurrentFile | Locals -> (fun _ -> true)
  | ModulePrefix prefix -> (fun nm -> is_within nm prefix)
  | Keyword s -> (fun nm -> string_contains (Libnames.string_of_path nm) s)

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
          out_fn @@ Feedback { doc_id = 0; span_id = newid; route = 0; contents = Message(Error, loc, msg ) };
          out_fn @@ Cancelled [newid];
          out_fn @@ exn_info
      end
      else out_fn @@ Cancelled [newid]

  | Cancel sid        ->
    let can_st, ndoc = Jscoq_doc.cancel ~doc:!doc sid in
    doc := ndoc; out_fn @@ Cancelled can_st

  | Exec sid          ->
    let ndoc = Jscoq_doc.observe ~doc:!doc sid in
    doc := ndoc; out_fn @@ Log (Debug, Pp.str @@ "observe " ^ (Stateid.to_string sid))

  | Goals sid        ->
    let doc = fst !doc in
    let goal_pp = pp_of_goals ~doc sid in
    out_fn @@ GoalInfo (sid, goal_pp)

  | Query (sid, rid, query) ->
    let sid = if Int.equal (Stateid.to_int sid) 0 then Jscoq_doc.tip !doc else sid in
    begin try
      Jscoq_doc.query ~doc:!doc ~at:sid ~route:rid query;
      out_fn @@ Feedback { doc_id = 0; span_id = sid; route = rid; contents = Complete }
    with exn ->
      let CoqExn(loc,_,msg) = coq_exn_info exn [@@warning "-8"] in
      out_fn @@ Feedback { doc_id = 0; span_id = sid; route = rid; contents = Message(Error, loc, msg ) };
      out_fn @@ Feedback { doc_id = 0; span_id = sid; route = rid; contents = Incomplete }
    end

  | Inspect (sid, rid, q) ->
    let sid = if Int.equal (Stateid.to_int sid) 0 then Jscoq_doc.tip !doc else sid in
    let _, env = Icoq.context_of_stm ~doc:(fst !doc) sid in
    let symbols = symbols_for q env in
    let results = Seq.filter (filter_by q) symbols in
    out_fn @@ SearchResults (rid, results)

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

  | Init(set_opts, lib_init, lib_path) ->
    let ndoc, iid = exec_init set_opts lib_init lib_path in
    doc := Jscoq_doc.create ndoc;
    out_fn @@ Ready iid

  | LoadPkg(base, pkg)  ->
    Lwt.async (fun () -> Jslibmng.load_pkg process_lib_event base pkg)

  | InfoPkg(base, pkgs) ->
    Lwt.(async (fun () ->
        let coqv, coqd, ccd, ccv, cmag = Icoq.version               in
        let jsoov = Sys_js.js_of_ocaml_version                      in
        let header1 = Printf.sprintf
            "JsCoq (%s), Coq %s/%4d (%s),\n  compiled on %s\n"
            Jscoq_version.jscoq_version coqv cmag coqd ccd          in
        let header2 = Printf.sprintf
            "OCaml %s, Js_of_ocaml %s\n" ccv jsoov                  in
        Jslibmng.info_pkg post_lib_event base pkgs                  >>= fun () ->
        return @@ out_fn @@ CoqInfo (header1 ^ header2)
      ))

  | InterruptSetup shmem -> interrupt_setup (Js.Unsafe.coerce shmem)

  | ReassureLoadPath load_path ->
    doc := Jscoq_doc.observe ~doc:!doc (Jscoq_doc.tip !doc); (* force current tip *)
    List.iter (fun (path_el, phys) -> Loadpath.add_coq_path
      (Jslibmng.path_to_coqpath ~implicit:!opts.implicit_libs ~unix_prefix:phys path_el)
    ) load_path
  | Load filename ->
    doc := Jscoq_doc.load ~doc:!doc filename ~echo:false
  | Compile filename ->
    post_file filename (Icoq.compile_vo ~doc:(fst !doc))

let setup_pseudo_fs () =
  (* '/static' is the default working directory of jsoo *)
  Sys_js.unmount ~path:"/static";
  Sys_js.mount ~path:"/static/" (fun ~prefix:_ ~path -> Jslibmng.coq_vo_req path);
  (* '/lib' is the target for Put commands *)
  Sys_js.mount ~path:"/lib/" (fun ~prefix:_ ~path:_ -> None)

let put_pseudo_file ~name ~buf =
  let str = Typed_array.String.of_arrayBuffer buf in
  try
    Sys_js.create_file ~name ~content:str
  with _e ->
    Sys_js.update_file ~name ~content:str

let setup_std_printers () =
  Sys_js.set_channel_flusher stdout (fun msg -> post_answer (Log (Notice, Pp.str @@ "stdout: " ^ msg)));
  Sys_js.set_channel_flusher stderr (fun msg -> post_answer (Log (Notice, Pp.str @@ "stderr: " ^ msg)));
  ()

let jscoq_protect f =
  try f ()
  with | exn -> post_answer @@ coq_exn_info exn

let jscoq_cmd_of_obj (cobj : < .. > Js.t) =
  let open Js.Unsafe in
  (* check if the given cobj is a "special" command *)
  (* that cannot be serialized by Yojson            *)
  let cmd = Js.array_get (coerce cobj) 0 in
  let o = Js.Optdef.bind cmd (fun cmd -> 
    if Js.to_string cmd = "InterruptSetup" then
      let arg = Js.array_get (coerce cobj) 1 in
      Js.Optdef.return @@ Result.Ok (InterruptSetup (inject arg))
    else Js.undefined) in
  Js.Optdef.get o (fun () -> jscoq_cmd_of_yojson @@ obj_to_json cobj)

(* Message from the main thread *)
let on_msg doc msg =

  let log_cmd cmd =
    let str = match cmd with
      | Put (filename,_) -> "[\"Put\", \"" ^ filename ^ "\", ...]"  (* "Put" commands are too long *)
      | _ -> Js.to_string (Js._JSON##(stringify msg)) [@@warning "-4"] in
    post_answer (Log (Debug, Pp.str str))
  in

  match jscoq_cmd_of_obj msg with
  | Result.Ok cmd  -> jscoq_protect (fun () -> log_cmd cmd ;
                                               jscoq_execute doc cmd)
  | Result.Error s -> post_answer @@
    JsonExn ("Error in JSON conv: " ^ s ^ " | " ^ (Js.to_string (Json.output msg)))


(* This code is executed on Worker initialization *)
let _ =

  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  setup_pseudo_fs    ();
  setup_std_printers ();

  let doc = ref (Obj.magic 0) in

  let on_msg = on_msg doc  in

  if is_worker then
    Worker.set_onmessage on_msg
  else
    Js.export "jsCoq" jsCoq;
    jsCoq##.postMessage := Js.wrap_callback on_msg ;
    jsCoq##.onmessage := Js.wrap_callback (fun _ -> ())
