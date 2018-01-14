(* Coq JavaScript API. Based in the coq source code and js_of_ocaml.
 *
 * By Emilio J. Gallego Arias, Mines ParisTech, Paris.
 * LICENSE: GPLv3+
 *
 * We provide a message-based asynchronous API for communication with
 * Coq. Our object listens to the following messages:
 *
 * And emits:
 *
 * - CoqLogEvent(level, msg): Log [msg] of priority [level].
 *
 *)

open Js
open Dom

(* Packages to load *)
class type initInfo = object
  method init_pkgs_ : js_string t js_array t readonly_prop
  method all_pkgs_  : js_string t js_array t readonly_prop
  method base_path_ : js_string t            readonly_prop
end

class type jsCoq = object

  (* When the libraries are loaded and JsCoq is ready, onInit is called *)
  method init        : ('self t, initInfo t -> Stateid.t) meth_callback writeonly_prop
  method onInit      : ('self t, unit)                    event_listener prop

  method version     : ('self t, js_string t)           meth_callback writeonly_prop
  method goals       : ('self t, js_string t)           meth_callback writeonly_prop

  method add         : ('self t, Stateid.t -> int -> js_string t -> Stateid.t) meth_callback writeonly_prop
  method edit        : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop
  method commit      : ('self t, Stateid.t -> unit)     meth_callback writeonly_prop

  method query       : ('self t, Stateid.t -> js_string t -> unit) meth_callback writeonly_prop

  (* Options. XXX must improve thanks to json serialization *)
  method set_printing_width_ : ('self t, int -> unit) meth_callback writeonly_prop
  method set_type_in_type_   : ('self t, bool -> unit) meth_callback writeonly_prop
  method set_debug_mode_     : ('self t, bool -> unit) meth_callback writeonly_prop

  (* Package management *)
  method add_pkg_    : ('self t, js_string t -> unit) meth_callback writeonly_prop

  (* When a new package is known we push the information to the GUI *)
  method onBundleInfo  : ('self t, Jslibmng.bundleInfo t ) event_listener prop
  method onBundleStart : ('self t, Jslibmng.bundleInfo t ) event_listener prop
  method onBundleLoad  : ('self t, Jslibmng.bundleInfo t ) event_listener prop

  (* When package loading starts/progresses/completes  *)
  method onPkgLoadStart : ('self t, Jslibmng.progressInfo t) event_listener prop
  method onPkgProgress  : ('self t, Jslibmng.progressInfo t) event_listener prop
  method onPkgLoad      : ('self t, Jslibmng.progressInfo t) event_listener prop

  (* Request to log from Coq *)
  method onLog       : ('self t, js_string t)           event_listener prop

  (* Error from Coq *)
  method onError     : ('self t, Stateid.t)             event_listener writeonly_prop

  (* We don't want to use event_listener due to limitations of invoke_handler... *)
  (* method onLog       : ('self t, js_string t -> unit)      meth_callback opt writeonly_prop *)

end

let setup_pseudo_fs () =
  Sys_js.unmount ~path:"/static/";
  Sys_js.mount ~path:"/static/" (fun ~prefix ~path ->
      ignore(prefix); Jslibmng.coq_vo_req path)

(* type feedback = { *)
(*   id : edit_or_state_id;        (\* The document part concerned *\) *)
(*   contents : feedback_content;  (\* The payload *\) *)
(*   route : route_id;             (\* Extra routing info *\) *)
(* } *)

let string_of_lvl (lvl : Feedback.level) : string =
  match lvl with
  | Feedback.Debug   -> "Debug"
  | Feedback.Info    -> "Info"
  | Feedback.Notice  -> "Notice"
  | Feedback.Warning -> "Warning"
  | Feedback.Error   -> "Error"

let string_of_feedback fb : string =
  let open Feedback in
  match fb with
  (* STM mandatory data (must be displayed) *)
    | Processed       -> "Processed."
    | Incomplete      -> "Incomplete."
    | Complete        -> "Complete."

  (* STM optional data *)
    | ProcessingIn s       -> "ProcessingIn: " ^ s
    | InProgress d         -> "InProgress: " ^ (string_of_int d)
    | WorkerStatus(w1, w2) -> "WorkerStatus: " ^ w1 ^ ", " ^ w2

  (* Generally useful metadata *)
    | AddedAxiom -> "AddedAxiom."
    | GlobRef (_loc, s1, s2, s3, s4) -> "GlobRef: " ^ s1 ^ ", " ^ s2 ^ ", " ^ s3 ^ ", " ^ s4
    | GlobDef (_loc, s1, s2, s3) -> "GlobDef: " ^ s1 ^ ", " ^ s2 ^ ", " ^ s3
    | FileDependency (os, s) -> "FileDep: " ^ (Option.default "" os) ^ ", " ^ s
    | FileLoaded (s1, s2)    -> "FileLoaded: " ^ s1 ^ " " ^ s2

    (* Extra metadata *)
    | Custom(_loc, msg, _xml) -> "Custom: " ^ msg
    (* Old generic messages *)
    | Message(lvl, _loc, m) -> "Msg["^ (string_of_lvl lvl) ^"]: " ^ Pp.string_of_ppcmds m
    (* Richer printing needed in trunk. *)
    (* | Message m -> "Msg: " ^ (Xml_printer.to_string m.message_content) *)

let string_of_sid sid = "sid: " ^ (Stateid.to_string sid)

let internal_log (this : jsCoq t) (str : js_string t) =
  let _    = invoke_handler this##.onLog this str  in
  ()

let jscoq_feedback_handler this (fb : Feedback.feedback) =
  let open Feedback in
  let fb_s = Printf.sprintf "feedback for [%s]: %s\n%!"
                            (string_of_sid fb.span_id)
                            (string_of_feedback fb.contents)  in

  internal_log this (string fb_s)

let setup_printers (this : jsCoq t) =
  try
    (* How to create a channel *)
    (* let _sharp_chan = open_out "/dev/null0" in *)
    (* let _sharp_ppf = Format.formatter_of_out_channel _sharp_chan in *)
    (* Sys_js.set_channel_flusher stdout (add_text js_stdout Info); *)
    (* Sys_js.set_channel_flusher stderr (add_text js_stderr Info) *)
    Sys_js.set_channel_flusher stdout
           (fun s -> internal_log this (string @@ "stdout: " ^ s));
    Sys_js.set_channel_flusher stderr
           (fun s -> internal_log this (string @@ "stderr: " ^ s))
  with Not_found -> ()

let jscoq_init (this : jsCoq t) (init_info : initInfo t) =
  setup_printers this;
  setup_pseudo_fs ();
  let init_callback () = (
      let _sid = Icoq.init { Icoq.ml_load    = Jslibmng.coq_cma_req;
                             Icoq.fb_handler = (jscoq_feedback_handler this);
                           } in
      ignore(invoke_handler this##.onInit this ())
    ) in
  let open Jslibmng in
  let pkg_callbacks = {
    bundle_info  = (fun pi -> ignore (invoke_handler this##.onBundleInfo   this pi));
    bundle_start = (fun pi -> ignore (invoke_handler this##.onBundleStart  this pi));
    bundle_load  = (fun pi -> ignore (invoke_handler this##.onBundleLoad   this pi));
    pkg_start    = (fun pi -> ignore (invoke_handler this##.onPkgLoadStart this pi));
    pkg_progress = (fun pi -> ignore (invoke_handler this##.onPkgProgress  this pi));
    pkg_load     = (fun pi -> ignore (invoke_handler this##.onPkgLoad      this pi));
  } in
  Jslibmng.init init_callback pkg_callbacks init_info##.base_path_ init_info##.all_pkgs_ init_info##.init_pkgs_;
  Stateid.of_int 1

let jscoq_version _this =
  let coqv, coqd, ccd, ccv = Icoq.version                     in
  let header1 = Printf.sprintf
      " JsCoq beta, Coq %s (%s),\n   compiled on %s\n Ocaml %s"
      coqv coqd ccd ccv                                       in
  let header2 = Printf.sprintf
      " Js_of_ocaml version %s\n" Sys_js.js_of_ocaml_version  in
  string @@ header1 ^ header2

(* let jscoq_add this (cmd : js_string t) : Stateid.t = *)
let jscoq_add _this sid _eid cmd  =
  (* Printf.eprintf "adding command %s\n%!" (to_string cmd); *)
  (* Catch parsing errors. *)
  try
    Icoq.add_to_doc sid (to_string cmd)
  with
  (* Hackkk *)
  | _ -> Obj.magic 0

let jscoq_edit _this sid : unit = Icoq.edit_doc sid

let jscoq_commit this sid =
  let ee () = let _ = invoke_handler this##onError this sid in () in
  try
    (* XXX: Careful with the difference between Stm.observe and Stm.finish XXX *)
    Icoq.commit_doc sid
  with
    | CErrors.UserError(_msg, _pp) ->
       (* console.log *)
       ee ()
    | CErrors.AlreadyDeclared _pp ->
       ee ()
    | _ ->
       ee ()

let jscoq_query _this sid cmd : unit =
  Icoq.query sid (to_string cmd)

let jscoq_add_pkg _this pkg : unit =
  Jslibmng.load_pkg (to_string pkg)

(* see: https://github.com/ocsigen/js_of_ocaml/issues/248 *)
let jsCoq : jsCoq t =
  let open Js.Unsafe in
  global##.jsCoq := obj [||];
  global##.jsCoq

let _ =
  (* XXX: This is a long time workaround *)
  Sys.interactive := false;

  jsCoq##.init     := Js.wrap_meth_callback jscoq_init;
  jsCoq##.version  := Js.wrap_meth_callback jscoq_version;
  jsCoq##.add      := Js.wrap_meth_callback jscoq_add;
  jsCoq##.edit     := Js.wrap_meth_callback jscoq_edit;
  jsCoq##.commit   := Js.wrap_meth_callback jscoq_commit;
  jsCoq##.query    := Js.wrap_meth_callback jscoq_query;
  jsCoq##.goals    := Js.wrap_meth_callback (fun _this -> string @@ Icoq.string_of_goals ());

  jsCoq##.set_printing_width_ := begin
    let open Icoq.Options in
    Js.wrap_meth_callback (fun _this -> set_int_option print_width)
  end;

  jsCoq##.set_debug_mode_ := begin
    Js.wrap_meth_callback (fun _this -> Icoq.set_debug)
  end;

  jsCoq##.add_pkg_       := Js.wrap_meth_callback jscoq_add_pkg;

  (* Empty handlers *)
  jsCoq##.onInit         := no_handler;
  jsCoq##.onBundleInfo   := no_handler;
  jsCoq##.onBundleLoad   := no_handler;
  jsCoq##.onBundleStart  := no_handler;
  jsCoq##.onPkgLoadStart := no_handler;
  jsCoq##.onPkgLoad      := no_handler;
  jsCoq##.onPkgProgress  := no_handler;
  jsCoq##.onLog          := no_handler;
  jsCoq##.onError        := no_handler;

  (* This needs to happen here to not delete the effects the
     library manager later. *)
  Lib.init ();
  ()
