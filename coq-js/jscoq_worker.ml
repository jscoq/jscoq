(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2017 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq.
 *)

open Js_of_ocaml

(* XXX *)
let str = Pp.str
let rec pp_opt (d : Pp.t) = let open Pp in
  let rec flatten_glue l = match l with
    | []  -> []
    | (Ppcmd_glue g :: l) -> flatten_glue (List.map repr g @ flatten_glue l)
    | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> flatten_glue (Ppcmd_string (s1 ^ s2) :: flatten_glue l)
    | (x :: l) -> x :: flatten_glue l
  in
  (* let rec flatten_glue l = match l with *)
  (*   | (Ppcmd_string s1 :: Ppcmd_string s2 :: l) -> Ppcmd_string (s1 ^ s2) :: flatten_glue l *)
  unrepr (match repr d with
      | Ppcmd_glue []   -> Ppcmd_empty
      | Ppcmd_glue [x]  -> repr (pp_opt x)
      | Ppcmd_glue l    -> Ppcmd_glue List.(map pp_opt (map unrepr (flatten_glue (map repr l))))
      | Ppcmd_box(bt,d) -> Ppcmd_box(bt, pp_opt d)
      | Ppcmd_tag(t, d) -> Ppcmd_tag(t,  pp_opt d)
      | d -> d
    )
  [@@warning "-4"]

let fbc_opt (fbc : Feedback.feedback_content) =
  Feedback.(match fbc with
  | Message(id,loc,msg) -> Message(id,loc,pp_opt msg)
  | _ -> fbc)
  [@@warning "-4"]

let fb_opt (fb : Feedback.feedback) =
  Feedback.({ fb with contents = fbc_opt fb.contents })

open Jser_feedback
open Jser_feedback.Feedback

type gvalue =
  [%import: Goptions.option_value]
  [@@deriving yojson]

(* Main RPC calls *)
let jscoq_version = "0.9~beta0"

type jscoq_cmd =
  | GetInfo
  | InfoPkg of string * string list
  | LoadPkg of string * string

  (*           implicit initial_imports      load paths                      *)
  | Init    of bool   * string list list   * (string list * string list) list

  (*           ontop       new         sentence                *)
  | Add     of Stateid.t * Stateid.t * string * bool
  | Cancel  of Stateid.t
  | Exec    of Stateid.t

  | Goals   of Stateid.t
  | Query   of Stateid.t * Feedback.route_id * string

  | Register of string

  (* XXX: Not well founded... *)
  | GetOpt  of string list

  | ReassureLoadPath of (string list * string list) list
  [@@deriving yojson]

type jscoq_answer =
  | CoqInfo   of string

  | Ready     of Stateid.t

  (* Merely Informative now *)
  | Added     of Stateid.t * Loc.t option

  (* Requires pkg(s)         prefix        module names    *)
  | Pending   of Stateid.t * string list * string list list

  (* Main feedback *)
  | Cancelled of Stateid.t list

  (* Goals must be printed better *)
  | GoalInfo  of Stateid.t * Pp.t option

  | CoqOpt    of gvalue
  | Log       of level     * Pp.t
  | Feedback  of feedback

  (* Low-level *)
  | CoqExn    of Loc.t option * (Stateid.t * Stateid.t) option * Pp.t
  | JsonExn   of string
  [@@deriving to_yojson]

let jsCoq = Js.Unsafe.obj [||]

let rec json_to_obj (cobj : < .. > Js.t) (json : Yojson.Safe.json) : < .. > Js.t =
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

let _answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg                            in
  let json_str = Yojson.Safe.to_string json_msg                        in
  (* Workaround to avoid ml_string conversion of Json.unsafe_input     *)
  Js.Unsafe.global##.JSON##(parse (Js.string json_str))

let answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg                            in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

type progress_info =
  [%import: Jslibmng.progress_info]
  [@@deriving yojson]

type lib_event =
  [%import: Jslibmng.lib_event]
  [@@deriving yojson]

let _lib_event_to_jsobj msg =
  let json_msg = lib_event_to_yojson msg                               in
  let json_str = Yojson.Safe.to_string json_msg                        in
  (* Workaround to avoid ml_string conversion of Json.unsafe_input     *)
  Js.Unsafe.global##.JSON##(parse (Js.string json_str))

let lib_event_to_jsobj msg =
  let json_msg = lib_event_to_yojson msg                            in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

let is_worker = (Js.Unsafe.global##.onmessage != Js.undefined)

let post_message : < .. > Js.t -> unit = 
  if is_worker then Worker.post_message
  else 
    fun msg -> Js.Unsafe.fun_call (jsCoq##.onmessage) [|Js.Unsafe.inject msg|]

(* Send messages to the main thread *)
let post_answer (msg : jscoq_answer) : unit =
  post_message (answer_to_jsobj msg)

let post_lib_event (msg : lib_event) : unit =
  Worker.post_message (lib_event_to_jsobj msg)

(* When a new package is loaded, the library load path has to be updated *)
let update_loadpath (msg : lib_event) : unit =
  match msg with
  | LibLoaded (_,bundle) ->
    List.iter Mltop.add_coq_path
      (Jslibmng.coqpath_of_bundle ~implicit:true (* TODO get implicit_flag from opts *) bundle)
  | _ -> ()
  [@@warning "-4"]

let process_lib_event (msg : lib_event) : unit =
  update_loadpath msg ; post_lib_event msg

(* implicit_flag : whether to enable loading of modules by short name only *)
(* lib_init      : list of modules to load *)
(* lib_path      : list of load paths *)
let exec_init (implicit_flag : bool) (lib_init : string list list) (lib_path : (string list * string list) list) =

  let lib_require  = List.map (fun lp ->
      (* Format.eprintf "u: %s, %s@\n" (to_name md) (to_dir md); *)
      String.concat "." lp, None, Some true) lib_init  in

  (* None       : just require            *)
  (* Some false : import but don't export *)
  (* Some true  : import and export       *)

  Icoq.(coq_init {
      ml_load      = Jslibmng.coq_cma_link;
      fb_handler   = (fun fb -> post_answer (Feedback (fb_opt fb)));
      require_libs = lib_require;
      iload_path   = List.map (fun (path_el, phys) ->
                         Jslibmng.path_to_coqpath ~implicit:implicit_flag ~unix_prefix:phys path_el
                     ) lib_path;
      top_name     = "JsCoq";
      aopts        = { enable_async = None;
                       async_full   = false;
                       deep_edits   = false;
                     };
      debug    = true;
    })

(* I refuse to comment on this part of Coq code... *)
let exec_getopt on =
  let open Goptions in
  let tbl = get_tables () in
  (OptionMap.find on tbl).opt_value

let coq_exn_info exn =
    let (e, info) = CErrors.push exn                   in
    let pp_exn    = pp_opt @@ CErrors.iprint (e, info) in
    CoqExn (Loc.get_loc info, Stateid.get info, pp_exn)

let requires ast =
  match ast with
  | Vernacexpr.VernacExpr (_, Vernacexpr.VernacRequire (prefix, _export, module_refs)) ->
    let prefix_str = match prefix with
    | Some ref -> Jslibmng.module_name_of_qualid ref
    | _ -> [] in
    let module_refs_str = List.map (fun modref -> Jslibmng.module_name_of_qualid modref) module_refs in
    Some ((prefix_str, module_refs_str))
  | _ -> None
  [@@warning "-4"]

let jscoq_execute =
  let out_fn = post_answer in fun doc -> function
  | Add(ontop,newid,stm,resolved) ->
      begin try
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
  | Cancel sid        ->
    let can_st, ndoc = Jscoq_doc.cancel ~doc:!doc sid in
    doc := ndoc; out_fn @@ Cancelled can_st

  | Exec sid          ->
    let ndoc = Jscoq_doc.observe ~doc:!doc sid in
    doc := ndoc; out_fn @@ Log (Debug, str @@ "observe " ^ (Stateid.to_string sid))

  | Goals sid        ->
    let doc = fst !doc in
    let goal_pp = Option.map pp_opt @@ Icoq.pp_of_goals ~doc sid in
    out_fn @@ GoalInfo (sid, goal_pp)

  | Query (sid, rid, query) ->
    let sid = if Stateid.to_int sid == 0 then Jscoq_doc.tip !doc else sid in
    begin try
      Jscoq_doc.query ~doc:!doc ~at:sid ~route:rid query
    with exn ->
      let CoqExn(loc,_,msg) = coq_exn_info exn [@@warning "-8"] in
      out_fn @@ Feedback { doc_id = 0; span_id = sid; route = rid; contents = Message(Error, loc, msg ) };
    end

  | Register file_path  ->
    let filename = Filename.basename file_path in
    let dir = Filename.dirname file_path in
    Jslibmng.register_cma ~filename ~dir

  | GetOpt on           -> out_fn @@ CoqOpt (exec_getopt on)

  | Init(implicit_flag, lib_init, lib_path) ->
    let ndoc, iid = exec_init implicit_flag lib_init lib_path in
    doc := Jscoq_doc.create ndoc;
    out_fn @@ Ready iid

  | InfoPkg(base, pkgs) ->
    Lwt.async (fun () -> Jslibmng.info_pkg post_lib_event base pkgs)

  | LoadPkg(base, pkg)  ->
    Lwt.async (fun () -> Jslibmng.load_pkg process_lib_event base pkg)

  | GetInfo             ->
    let coqv, coqd, ccd, ccv, cmag = Icoq.version               in
    let header1 = Printf.sprintf
        " JsCoq (%s), Coq %s/%4d (%s),\n   compiled on %s\n Ocaml %s"
        jscoq_version coqv cmag coqd ccd ccv                    in
    let header2 = Printf.sprintf
        " Js_of_ocaml version %s\n" Sys_js.js_of_ocaml_version  in
    out_fn @@ CoqInfo (header1 ^ header2)

  | ReassureLoadPath load_path ->
    Mltop.add_coq_path @@ Jslibmng.path_to_coqpath ~implicit:true ~unix_prefix:["/lib"] [];
    List.iter (fun (path_el, phys) -> Mltop.add_coq_path
      (Jslibmng.path_to_coqpath ~implicit:true  (* TODO get implicit_flag from opts *) ~unix_prefix:phys path_el)
    ) load_path

let setup_pseudo_fs () =
  (* '/static' is the default working directory of jsoo *)
  Sys_js.unmount ~path:"/static";
  Sys_js.mount ~path:"/static/" (fun ~prefix:_ ~path -> Jslibmng.coq_vo_req path);
  (* '/lib' is the target for Put commands *)
  Sys_js.mount ~path:"/lib/" (fun ~prefix:_ ~path:_ -> None);
  Sys_js.create_file ~name:"/lib/.anchor" ~content:""

let put_pseudo_file ~name ~buf =
  let str = Typed_array.String.of_arrayBuffer buf in
  try
    Sys_js.create_file ~name ~content:str
  with _e ->
    Sys_js.update_file ~name ~content:str

let setup_std_printers () =
  Sys_js.set_channel_flusher stdout (fun msg -> post_answer (Log (Notice, str @@ "stdout: " ^ msg)));
  Sys_js.set_channel_flusher stderr (fun msg -> post_answer (Log (Notice, str @@ "stderr: " ^ msg)));
  ()

let jscoq_protect f =
  try f ()
  with | exn -> post_answer @@ coq_exn_info exn

(* Message from the main thread *)
let on_msg doc msg =

  (*-- "Regular" messages are pure POD --*)
  let on_json_msg doc obj =
    (* XXX: Call the GC, setTimeout to avoid stack overflows ?? *)
    let json_string = Js.to_string (Json.output obj) in
    let json_obj = Yojson.Safe.from_string json_string in

    match jscoq_cmd_of_yojson json_obj with
    | Result.Ok cmd  -> jscoq_protect (fun () -> post_answer (Log (Debug, str json_string)) ;
                                        jscoq_execute doc cmd)
    | Result.Error s -> post_answer @@
      JsonExn ("Error in JSON conv: " ^ s ^ " | " ^ (Js.to_string (Json.output obj)))
  in
  (*-- "Special" messages containing ArrayBuffers require special treatment --*)
  let get_cmd arr =
    Js.Optdef.case (Js.array_get arr 0)
      (fun () -> "")
      (fun s -> Js.to_string (Js.Unsafe.coerce s))
  in
  let array_unsafe_get arr idx =
    Js.Unsafe.coerce (Js.Optdef.get (Js.array_get arr idx) (fun _ -> assert false))
  in
  let on_buffer_msg msg =
    (* Assume msg is of the form ["Put", filename, <ArrayBuffer>] *)
    let filename = Js.to_string (array_unsafe_get msg 1) in 
    let content = array_unsafe_get msg 2 in
    put_pseudo_file ~name:filename ~buf:content
  
  in
  match get_cmd msg with
  | "Put" -> on_buffer_msg msg
  | _     -> on_json_msg doc msg

(* This code is executed on Worker initialization *)
let _ =

  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  setup_pseudo_fs    ();
  setup_std_printers ();

  let doc = ref (Obj.magic 0) in

  (* Heuristic to avoid StackOverflows when we have too many incoming
     messages. *)
  (*
  let on_msg obj = Lwt.(async (             fun () ->
                        Lwt_js.yield () >>= fun () ->
                        return @@ on_msg obj    )) in
   *)
  let on_msg = on_msg doc  in

  if is_worker then  
    Worker.set_onmessage on_msg
  else
    Js.export "jsCoq" jsCoq;
    jsCoq##.postMessage := Js.wrap_callback on_msg ;
    jsCoq##.onmessage := Js.wrap_callback (fun _ -> ())
      (* Js.Unsafe.fun_call Js.Unsafe.global##.console##.log [|x|]); *)
