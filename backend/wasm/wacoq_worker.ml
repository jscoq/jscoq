open Jscoq_core
open Jscoq_core.Jscoq_interp
open Jscoq_core.Jscoq_proto.Proto

external emit : string -> unit = "wacoq_emit" (* implemented in `core.ts` *)
external interrupt_setup : opaque -> unit = "interrupt_setup" (* implemented in `core.ts` *)

let deserialize (json : string) =
  [%of_yojson: jscoq_cmd] @@ Yojson.Safe.from_string json

let serialize (answers : jscoq_answer list) =
  Yojson.Safe.to_string @@ `List (List.map [%to_yojson: jscoq_answer] answers)

let handleRequest json_str =
  let resp =
    let cmd = deserialize json_str                     in
    match cmd with
    | Result.Error e -> [JsonExn e]
    | Result.Ok cmd ->
      let token = Coq.Limits.Token.create () in
      jscoq_execute ~token cmd; []
  in
  serialize resp

(* We do this hack as to use the Coq default loading mechanism that
   works with findlib, but cannot intrument plugin loading *)
let handleRequest json_str =
  if (Mltop.is_ocaml_top ()) then Mltop.remove ();
  handleRequest json_str

let handleRequestsFromStdin () =
  try
    while true do
      emit @@ handleRequest @@ Stdlib.read_line ()
    done
  with End_of_file -> ()

(* Used only for native-compute, so not relevant *)
let load_module = Dynlink.loadfile

(* Findlib ready, but needs the setup *)
(* let load_plugin = Coq.Loader.plugin_handler None *)

let load_plugin pg =
  let legacy, pkg = Mltop.PluginSpec.repr pg in
  Format.eprintf "load_plugin: %s / %s@\n%!" (Option.default "null" legacy) pkg;
  match Mltop.PluginSpec.repr pg with
  | None, _pkg -> ()             (* Findlib; not implemented *)
  | Some cma, _ -> load_module cma  (* Legacy loading method *)

let wasm_cb =
  Jscoq_interp.Callbacks.
    { load_module
    ; load_plugin
    ; post_message = (fun msg -> emit @@ Yojson.Safe.to_string @@ `List [msg])
    ; post_file = (fun _ _ _ -> ())
    ; interrupt_setup
    ; branding = "waCoq"
    ; subsystem_version = "wasi-sdk 12"
    ; read_file = (fun ~name:_ -> "")
    ; write_file = (fun ~name:_ ~content:_ -> ())
    ; register_cma = (fun ~file_path:_ -> ())
    ; load_pkg = (fun ~base_path:_ ~pkg:_ ~cb:_ -> failwith "handled in JS")
    ; info_pkg = (fun ~base_path:_ ~pkgs:_ ~cb:_ -> failwith "handled in JS")
    }

let () =
  Jscoq_interp.Callbacks.set wasm_cb;
  try
    Callback.register "wacoq_post" handleRequest ;
    if (Array.length Sys.argv > 1) && Sys.argv.(1) = "-stdin" then
      handleRequestsFromStdin ()
  with CErrors.UserError(pp) ->
    print_endline @@ "error! " ^ Pp.string_of_ppcmds pp
