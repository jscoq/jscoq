(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(* Coq serialization API/Plugin                                         *)
(* Copyright 2016 MINES ParisTech                                       *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

type diagnostic = Fleche.Types.Diagnostic.t

type coq_opts =
  { notification_cb : diagnostic -> int -> unit
  (** callback to handle notifications *)
  ; debug        : bool
  (** Enable debug mode *)
  ; load_module : string -> unit
  (** callback to load cma/cmo files *)
  ; load_plugin : Mltop.PluginSpec.t -> unit
  }

type require_lib = (string * string option * Lib.export_flag option)

type doc_opts =
  { uri : string
  (** name of the top-level module *)
  ; require_libs : require_lib list
  (** Libs to require on startup *)
  ; opt_values : (string list * Goptions.option_value) list
  (** Initial values for Coq options *)
  ; vo_path      : Loadpath.vo_path list
  (** Initial LoadPath *)
  }

let _set_options opt_values =
  let open Goptions in
  let new_val v _old = v in
  List.iter
    (fun (opt, value) -> set_option_value new_val opt value)
    opt_values

let _default_warning_flags = "-notation-overridden"

let root_state = ref (Coq.State.of_coq (Vernacstate.freeze_interp_state ~marshallable:false))
let fb_queue = ref []

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
(* module LIO = Lsp.Io
 * module LSP = Lsp.Base *)

let lsp_cb =
  Fleche.Io.CallBack.
    { log_error = (fun cat msg -> Format.eprintf "[%s] %s@\n%!" cat msg)
    ; send_diagnostics = (fun ~uri:_ ~version:_ _diags -> ())
    }

let coq_init opts =

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* LSP.std_protocol := std; *)

  Fleche.Io.CallBack.set lsp_cb;

  (* XXX : set debug system for stderr *)
  let debug = opts.debug in

  let lvl_to_severity (lvl : Feedback.level) =
    match lvl with
    | Feedback.Debug -> 5
    | Feedback.Info -> 4
    | Feedback.Notice -> 3
    | Feedback.Warning -> 2
    | Feedback.Error -> 1
  in

  let fb_handler (Feedback.{ contents; _ }) =
    (* Format.fprintf lp_fmt "%s@\n%!" "fb received"; *)
    match contents with
    | Message (lvl, loc, msg) ->
      let lvl = lvl_to_severity lvl in
      fb_queue := (loc, lvl, msg) :: !fb_queue
    | _ -> ()
  in

  (* jsCoq-specific flags *)
  Global.set_VM false;
  Global.set_native_compiler false;

  (* This asserts false if called XD *)
  (* Flags.set_native_compiler false; *)

  (* CWarnings.set_flags default_warning_flags; *)
  (* set_options opts.opt_values; *)

  (* Initialize paths *)
  (* List.iter Mltop.add_ml_dir opts.ml_path; *)
  (* List.iter Loadpath.add_vo_path opts.vo_path; *)

  (* Init Coq *)
  let load_plugin = opts.load_plugin in
  let load_module = opts.load_module in
  root_state := Coq.Init.(coq_init { fb_handler; load_plugin; load_module; debug });
  ()

let check_doc ~doc =
  let ofmt = Format.formatter_of_out_channel stdout in
  Fleche.Doc.check ~ofmt ~doc ~fb_queue

let new_doc opts ~text =
  let state = !root_state, opts.vo_path, [], 0 in
  let uri = opts.uri in
  let doc = Fleche.Doc.create ~state ~uri ~version:1 ~contents:text in
  check_doc ~doc

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Printexc.record_backtrace debug;
  ()
  (* XXX fixme 8.14 *)
  (* Flags.debug := debug *)

let version =
  Coq_config.version, Coq_config.caml_version, Coq_config.vo_version
