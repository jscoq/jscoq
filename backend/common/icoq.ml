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

(* Init options for coq *)
type async_flags = {
  enable_async : string option;
  async_full   : bool;
  deep_edits   : bool;
}

type require_lib = (string * string option * Lib.export_flag option)
type top_mode = Interactive | Vo

type coq_opts = {
  (* callback to handle async feedback *)
  fb_handler : Feedback.feedback -> unit;
  (* Async flags *)
  aopts        : async_flags;
  (* callback to load cma/cmo files *)
  ml_load      : string -> unit;
  (* Initial values for Coq options *)    (* @todo this has to be set during init in 8.13 and older; in 8.14, move to doc_opts *)
  opt_values   : (string list * Goptions.option_value) list;
  (* Enable debug mode *)
  debug        : bool;
  (* Initial LoadPath *)
  vo_path      : Loadpath.vo_path list;
}

type doc_opts = {
  (* Libs to require on startup *)
  require_libs : require_lib list;
  (* name of the top-level module *)
  top_name     : string;
  (* document mode: interactive or batch *)
  mode         : top_mode;
}

type in_mode = Proof | General (* pun intended *)

external _coq_vm_trap : unit -> unit = "coq_vm_trap"

type 'a seq = 'a Seq.t

let feedback_id = ref None

let set_options opt_values =
  let open Goptions in
  let new_val v _old = v in
  List.iter
    (fun (opt, value) -> set_option_value new_val opt value)
    opt_values

let default_warning_flags = "-notation-overridden"

let load_plugin ml_load pg =
  match Mltop.PluginSpec.repr pg with
  | None, _pkg -> ()            (* Not implemented *)
  | Some cma, _ -> ml_load cma  (* Legacy loading method *)

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =

  if opts.debug then CDebug.set_debug_all true;

  (* coq_vm_trap (); *)

  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  let ser_mltop : Mltop.toplevel = let open Mltop in
    { load_plugin = load_plugin opts.ml_load
    ; load_module = opts.ml_load
    (* We ignore all the other operations for now. *)
    ; add_dir  = (fun _ -> ())
    ; ml_loop  = (fun _ -> ());
  } in

  Mltop.set_top ser_mltop;

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  Option.iter Feedback.del_feeder !feedback_id;
  feedback_id := Some (Feedback.add_feeder opts.fb_handler);

  (* Core Coq initialization *)
  Lib.init();

  Global.set_impredicative_set false;
  Global.set_VM false;
  Global.set_native_compiler false;
  Flags.set_native_compiler false;
  CWarnings.set_flags default_warning_flags;
  set_options opts.opt_values;

  (* Initialize paths *)
  (* List.iter Mltop.add_ml_dir opts.ml_path; *)
  List.iter Loadpath.add_vo_path opts.vo_path;

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ()

let new_doc opts =
  let doc_type = match opts.mode with
    | Interactive -> let dp = Libnames.dirpath_of_string opts.top_name in
                     Stm.Interactive (Coqargs.TopLogical dp)
    | Vo ->          Stm.VoDoc opts.top_name
  in
  let ndoc = { Stm.doc_type
             ; injections = List.map (fun x -> Coqargs.RequireInjection x) opts.require_libs
             (* ; ml_load_path = []
              * ; vo_load_path = opts.vo_path *)
             ; stm_options = Stm.AsyncOpts.default_opts
             } in
  let ndoc, nsid = Stm.new_doc ndoc in
  ndoc, nsid

let mode_of_stm ~doc sid =
  match Stm.state_of_id ~doc sid with
  | Valid (Some { lemmas = Some _; _ }) -> Proof
  | _ -> General

let context_of_st m = match m with
  | Stm.Valid (Some { Vernacstate.lemmas = Some lemma ; _ } ) ->
    Vernacstate.LemmaStack.with_top lemma
      ~f:(fun pstate -> Declare.Proof.get_current_context pstate)
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let context_of_stm ~doc sid =
  let st = Stm.state_of_id ~doc sid in
  context_of_st st

(* Compilation *)

let compile_vo ~read_file ~doc vo_out_fn =
  ignore(Stm.join ~doc);
  let dirp = Lib.library_dp () in
  (* freeze and un-freeze to to allow "snapshot" compilation *)
  (*  (normally, save_library_to closes the lib)             *)
  let frz = Vernacstate.freeze_interp_state ~marshallable:false in
  Library.save_library_to Library.ProofsTodoNone ~output_native_objects:false dirp vo_out_fn;
  Vernacstate.unfreeze_interp_state frz;
  read_file ~name:vo_out_fn

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Printexc.record_backtrace debug;
  ()
  (* XXX fixme 8.14 *)
  (* Flags.debug := debug *)

let version =
  Coq_config.version, Coq_config.caml_version, Coq_config.vo_version
