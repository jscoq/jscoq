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

type coq_opts = {

  (* callback to handle async feedback *)
  fb_handler : Feedback.feedback -> unit;

  (* Initial LoadPath XXX: Use the coq_pkg record? *)
  iload_path   : Loadpath.coq_path list;

  (* Libs to require prior to STM init *)
  require_libs : (string * string option * bool option) list;

  (* Async flags *)
  aopts        : async_flags;

  (* name of the top-level module *)
  top_name     : string;

  (* Initial values for Coq options *)
  opt_values   : (string list * Goptions.option_value) list;

  (* callback to load cma/cmo files *)
  ml_load    : string -> unit;

  (* Enable debug mode *)
  debug    : bool;
}


external coq_vm_trap : unit -> unit = "coq_vm_trap"


type 'a seq = 'a Seq.t


let feedback_id = ref None


let set_options opt_values =
  let open Goptions in
  let new_val v old = v in
  List.iter
    (fun (opt, value) -> set_option_value new_val opt value)
    opt_values


(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =

  if opts.debug then begin
    Printexc.record_backtrace true;
    Flags.debug := true;
  end;

  coq_vm_trap ();

  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  let ser_mltop : Mltop.toplevel = let open Mltop in
    {
    load_obj = opts.ml_load;
    (* We ignore all the other operations for now. *)
    use_file = (fun _ -> ());
    add_dir  = (fun _ -> ());
    ml_loop  = (fun _ -> ());
  } in

  Mltop.set_top ser_mltop;

  (* Core Coq initialization *)
  Lib.init();
  Global.set_engagement Declarations.PredicativeSet;
  Global.set_VM false;
  Global.set_native_compiler false;
  set_options opts.opt_values;

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  Option.iter Feedback.del_feeder !feedback_id;
  feedback_id := Some (Feedback.add_feeder opts.fb_handler);

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ();

  (* Return the initial state of the STM *)
  let sertop_dp = Stm.TopLogical (Libnames.dirpath_of_string opts.top_name) in
  let ndoc = { Stm.doc_type = Stm.Interactive sertop_dp;
               require_libs = opts.require_libs;
               iload_path = opts.iload_path;
               stm_options = Stm.AsyncOpts.default_opts } in
  let ndoc, nsid = Stm.new_doc ndoc in
  ndoc, nsid

let context_of_st m = match m with
  | `Valid (Some { Vernacstate.lemmas = Some lemma ; _ } ) ->
    Vernacstate.LemmaStack.with_top_pstate lemma
      ~f:(fun pstate -> Pfedit.get_current_context pstate)
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let context_of_stm ~doc sid =
  let st = Stm.state_of_id ~doc sid in
  context_of_st st


(* Inspection subroutines *)

let full_path_of_kn kn =
  let mp, l = Names.KerName.repr kn in
  Libnames.make_path (Lib.dp_of_mp mp) (Names.Label.to_id l)

let full_path_of_constant c = full_path_of_kn (Names.Constant.user c)

let inspect_globals ~env () =
  let global_consts = List.to_seq @@
      Environ.fold_constants (fun name _ l -> name :: l) env [] in
  Seq.map full_path_of_constant global_consts


let libobj_is_leaf obj =
  match obj with
  | Lib.Leaf _ -> true | _ -> false [@@warning "-4"]

let full_path_sibling path id =
  Libnames.make_path (Libnames.dirpath path) id  

let lookup_inductive env path mi =
  let open Declarations in
  try
    let defn_body = Environ.lookup_mind mi env in
    Array.to_seq defn_body.mind_packets
      |> Seq.map (fun p -> full_path_sibling path (p.mind_typename))
    (* TODO include constructors *)
  with Not_found -> Seq.empty

let find_definitions env obj_path =
  let open Names.GlobRef in
  try
    match Nametab.global_of_path obj_path with
    | ConstRef _ -> Seq.return obj_path
    | IndRef (mi,_) -> lookup_inductive env obj_path mi
    | _ -> Seq.empty
  with Not_found -> Seq.empty

let inspect_library ~env () =
  let ls = Lib.contents () in
  Seq.flat_map (fun ((obj_path, _), obj) ->
    if libobj_is_leaf obj then find_definitions env obj_path
    else Seq.empty)
    (List.to_seq ls)


let inspect_locals ~env ?(dir_path=Names.DirPath.empty) () =
  let named_ctx = Environ.named_context env in
  List.to_seq (Context.Named.to_vars named_ctx |> Names.Id.Set.elements) |>
    Seq.map (Libnames.make_path dir_path)


(* Compilation *)

let compile_vo ~doc =
  ignore(Stm.join ~doc);
  let tmp_vo_fn = "/static/._JsCoq.vo" in   (* save to fake fs *)
  let dirp = Lib.library_dp () in
  (* freeze and un-freeze to to allow "snapshot" compilation *)
  (*  (normally, save_library_to closes the lib)             *)
  let frz = Vernacstate.freeze_interp_state ~marshallable:false in
  Library.save_library_to Library.ProofsTodoNone ~output_native_objects:false dirp tmp_vo_fn (Global.opaque_tables ());
  Vernacstate.unfreeze_interp_state frz;
  Js_of_ocaml.Sys_js.read_file ~name:tmp_vo_fn

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Backtrace.record_backtrace debug;
  Flags.debug := debug

let version =
  Coq_config.version, Coq_config.date, Coq_config.compile_date, Coq_config.caml_version, Coq_config.vo_magic_number
