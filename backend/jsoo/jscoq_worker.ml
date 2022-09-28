(* Coq JavaScript API.
 *
 * Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * Copyright (C) 2018-2021 Shachar Itzhaky, Technion
 * Copyright (C) 2019-2021 Emilio J. Gallego Arias, INRIA
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq.
 *)

open Js_of_ocaml
open Jscoq_core
open Jscoq_proto.Proto

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
    else if instanceof cobj Typed_array.uint8Array then
      `String (Typed_array.String.of_uint8Array @@ coerce cobj)
    else
      let json_string = Js.to_string (Json.output cobj) in
      Yojson.Safe.from_string json_string

(* This is an internal js_of_ocaml primitive... *)
external string_bytes : string -> Typed_array.uint8Array Js.t = "caml_convert_bytes_to_array"

(* (following is a reference implementation)
let string_bytes s : Typed_array.uint8Array Js.t =
  let ta = new%js Typed_array.uint8Array (String.length s) in
  String.iteri (fun i c -> Typed_array.set ta i (Char.code c)) s;
  ta *)

let buffer_of_uint8array array =    (* pretty much copied from CoqWorker.arrayBufferOfBuffer  :| *)
  let open Js.Unsafe in
  let buffer = array##.buffer in
  if Int.equal array##.byteOffset 0 && Int.equal array##.byteLength buffer##.byteLength then
    array, buffer
  else
    let buffer = (coerce buffer)##slice array##.byteOffset array##.byteLength in
    new%js Typed_array.uint8Array_fromBuffer buffer, buffer

external interrupt_setup : opaque (* Uint32Array *) -> unit = "interrupt_setup"

let _answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg                            in
  let json_str = Yojson.Safe.to_string json_msg                        in
  (* Workaround to avoid ml_string conversion of Json.unsafe_input     *)
  Js._JSON##(parse (Js.string json_str))

let answer_to_jsobj msg =
  let json_msg = jscoq_answer_to_yojson msg       in
  json_to_obj (Js.Unsafe.obj [||]) json_msg

let is_worker =
  let open Js.Unsafe in
  global##.WorkerGlobalScope != Js.undefined && global##.self != Js.undefined &&
    pure_js_expr "self instanceof WorkerGlobalScope"

(* Main jscoq object *)
let jsCoq = Js.Unsafe.obj [||]

let post_message : < .. > Js.t -> unit =
  if is_worker then Worker.post_message
  else
    fun msg ->
      Js.Unsafe.fun_call (jsCoq##.onmessage) [|Js.Unsafe.inject msg|]

(* Send messages to the main thread *)
let post_answer (msg : jscoq_answer) : unit =
  post_message (answer_to_jsobj msg)

let post_file tag filename content : unit =
  let open Js.Unsafe in
  let array, buf = buffer_of_uint8array (string_bytes content) in
  let msg = Js.array [|inject @@ Js.string tag;
                       inject @@ Js.string filename;
                       inject @@ array|] in
  if is_worker then
    Js.Unsafe.global##postMessage msg (Js.array [|buf|])  (* use `transfer` *)
  else
    post_message msg

let setup_pseudo_fs () =
  (* '/static' is the default working directory of jsoo *)
  Sys_js.unmount ~path:"/static";
  Sys_js.mount ~path:"/static/" (fun ~prefix:_ ~path -> Jslibmng.coq_vo_req path);
  (* '/lib' is the target for Put commands *)
  Sys_js.mount ~path:"/lib/" (fun ~prefix:_ ~path:_ -> None)

let setup_std_printers () =
  Sys_js.set_channel_flusher stdout (fun msg -> post_answer (Log (Notice, Pp.str @@ "stdout: " ^ msg)));
  Sys_js.set_channel_flusher stderr (fun msg -> post_answer (Log (Notice, Pp.str @@ "stderr: " ^ msg)));
  ()

external coq_vm_trap : unit -> unit = "coq_vm_trap"

let setup_top () =
  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  let load_cma = fun cma -> Jslibmng.coq_cma_link ~file_path:cma in
  let load_plugin pg =
    match Mltop.PluginSpec.repr pg with
    | None, _pkg -> ()             (* Findlib; not implemented *)
    | Some cma, _ -> load_cma cma  (* Legacy loading method *)    in

  let open Mltop in
  set_top
    { load_plugin = load_plugin
    ; load_module = load_cma
    (* We ignore all the other operations for now. *)
    ; add_dir  = (fun _ -> ())
    ; ml_loop  = (fun _ -> ());
    };

  coq_vm_trap ()

(* This is already taken care by the LSP layer *)
let jscoq_protect f =
  try f ()
  with
  | exn ->
    let exn = Exninfo.capture exn |> CErrors.iprint in
    post_answer @@ (Log (Feedback.Error, Pp.(str "Exn happened, this should never happen: " ++ exn)))

let jscoq_cmd_of_obj (cobj : < .. > Js.t) =
  let open Js.Unsafe in
  (* check if the given cobj is a "special" command *)
  (* that cannot be serialized by Yojson            *)
  let cmd = Js.array_get (coerce cobj) 0 in
  let o = Js.Optdef.bind cmd (fun cmd ->
    if Js.to_string cmd = "InterruptSetup" then
      let arg = Js.array_get (coerce cobj) 1 in
      Js.Optdef.return @@ Result.Ok (InterruptSetup (Obj.magic arg) (* @oops *))
    else Js.undefined) in
  Js.Optdef.get o (fun () -> jscoq_cmd_of_yojson @@ obj_to_json cobj)

(* Message from the main thread *)
let event_queue = ref []

let on_msg _doc msg =

  let log_cmd cmd =
    let str = match cmd with
      | Put (filename,_) -> "[\"Put\", \"" ^ filename ^ "\", ...]"  (* "Put" commands are too long *)
      | _ -> Js.to_string (Js._JSON##(stringify msg)) [@@warning "-4"] in
    post_answer (Log (Debug, Pp.str str))
  in

  match jscoq_cmd_of_obj msg with
  | Result.Ok cmd  ->
    log_cmd cmd;
    event_queue := !event_queue @ [cmd]
  | Result.Error s -> post_answer @@
    JsonExn ("Error in JSON conv: " ^ s ^ " | " ^ (Js.to_string (Json.output msg)))

let write_file ~name ~content =
  try         Sys_js.create_file ~name ~content
  with _e ->  Sys_js.update_file ~name ~content

let jsoo_cb =
  Jscoq_interp.Callbacks.
    { pre_init = setup_top
    ; post_message = (fun x -> json_to_obj (Js.Unsafe.obj [||]) x |> post_message)
    ; post_file = post_file
    ; interrupt_setup = interrupt_setup
    ; branding = "jsCoq"
    ; subsystem_version = "Js_of_ocaml " ^ Sys_js.js_of_ocaml_version
    ; read_file = Sys_js.read_file
    ; write_file = write_file
    ; register_cma = Jslibmng.register_cma
    ; load_pkg = (fun ~base_path ~pkg ~cb ->
      Lwt.async (fun () -> Jslibmng.load_pkg ~verb:false cb base_path pkg))
    ; info_pkg = (fun ~base_path ~pkgs ~cb ->
      Lwt.async (fun () -> Jslibmng.info_pkg cb base_path pkgs))
    }

let setup_interp () =
  Jscoq_interp.Callbacks.set jsoo_cb;
  ()

let setTimeout cb d = Dom_html.setTimeout cb d

(* The way we do interrupt this doesn't take effect. *)
let rec filter_queue (cmd, rest) queue =
  match queue with
  | [] -> cmd, rest
  | (Jscoq_proto.Proto.Update _ as cmd') :: rest' ->
    (* XXX: Cancel the events in rest that we have discarded *)
    Format.eprintf "discarding %d events@\n%!" (List.length rest + 1);
    filter_queue (cmd', []) rest'
  | cmd' :: rest' ->
    filter_queue (cmd, rest @ [cmd']) rest'

let rec process_queue () =
  match !event_queue with
  | [] ->
    ignore(setTimeout process_queue 0.1)
  | cmd :: rest ->
    Format.eprintf "Queue length: %d@\n%!" (List.length rest + 1);
    let cmd, rest = filter_queue (cmd, []) rest in
    event_queue := rest;
    jscoq_protect (fun () ->
        Jscoq_interp.jscoq_execute cmd);
    (* Give a chance to receive pending messages *)
    ignore(setTimeout process_queue 0.1)

(* This code is executed on Worker initialization *)
let _ =

  (* This is needed if dynlink is enabled in 4.03.0 *)
  Sys.interactive := false;

  setup_pseudo_fs    ();
  setup_std_printers ();

  setup_interp ();

  let doc = ref (Obj.magic 0) in
  let on_msg = on_msg doc  in

  if is_worker then
    Worker.set_onmessage on_msg
  else
    begin
      Js.export "jsCoq" jsCoq;
      jsCoq##.postMessage := Js.wrap_callback on_msg ;
      jsCoq##.onmessage := Js.wrap_callback (fun _ -> ())
    end;
  ignore(setTimeout process_queue 0.1);
  ()
