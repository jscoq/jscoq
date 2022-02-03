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

type require_lib = (string * string option * bool option)
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

type qualified_object_prefix = {
  dp: Names.DirPath.t;
  mod_ids: Names.Id.t list
}

type qualified_name = {
  prefix: qualified_object_prefix;
  basename: Names.Id.t
}

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

(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =

  if opts.debug then CDebug.set_debug_all true;

  (* coq_vm_trap (); *)

  (* Custom toplevel is used for bytecode-to-js dynlink  *)
  let ser_mltop : Mltop.toplevel = let open Mltop in
    {
    load_obj = opts.ml_load;
    (* We ignore all the other operations for now. *)
    add_dir  = (fun _ -> ());
    ml_loop  = (fun _ -> ());
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

(* Inspection subroutines *)

let qualified_object_prefix_of_mp mp =
  let dp, mod_ids = Lib.split_modpath mp in {dp; mod_ids}

let qualified_object_prefix_of_dp dp = {dp; mod_ids = []}

let qualified_name_of_kn kn =
  let mp, l = Names.KerName.repr kn in
  {prefix = qualified_object_prefix_of_mp mp; basename = Names.Label.to_id l}

let qualified_name_of_constant c = qualified_name_of_kn (Names.Constant.user c)

let qualified_name_of_full_path fp =
  let (dp, id) = Libnames.repr_path fp in
  {prefix = qualified_object_prefix_of_dp dp; basename = id}

let string_of_qualified_name qn =
  let {prefix = {dp; mod_ids}; basename} = qn in (* todo use `ids` as well *)
  let dp = match Names.DirPath.repr dp with
    | [] -> [] | _ -> [Names.DirPath.to_string dp] in
  String.concat "." (dp @ (List.map Names.Id.to_string mod_ids) @ [Names.Id.to_string basename])

(* Get constants in global scope *)
let inspect_globals ~env () =
  let global_consts = List.to_seq @@
      Environ.fold_constants (fun name _ l -> name :: l) env [] in
  Seq.map qualified_name_of_constant global_consts


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

(* Get definitions in current module *)
let inspect_library ~env () =
  let ls = Lib.contents () in
  Seq.flat_map (fun ((obj_path, _), obj) ->
    if libobj_is_leaf obj then find_definitions env obj_path
    else Seq.empty)
    (List.to_seq ls) |> Seq.map qualified_name_of_full_path

(* Get local names in proof context *)
let inspect_locals ~env ?(dir_path=Names.DirPath.empty) () =
  let named_ctx = Environ.named_context env in
  List.to_seq (Context.Named.to_vars named_ctx |> Names.Id.Set.elements) |>
    Seq.map (Libnames.make_path dir_path)
    |> Seq.map qualified_name_of_full_path


(* Compilation *)

let compile_vo ~doc vo_out_fn =
  ignore(Stm.join ~doc);
  let dirp = Lib.library_dp () in
  (* freeze and un-freeze to to allow "snapshot" compilation *)
  (*  (normally, save_library_to closes the lib)             *)
  let frz = Vernacstate.freeze_interp_state ~marshallable:false in
  Library.save_library_to Library.ProofsTodoNone ~output_native_objects:false dirp vo_out_fn;
  Vernacstate.unfreeze_interp_state frz;
  Js_of_ocaml.Sys_js.read_file ~name:vo_out_fn

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Printexc.record_backtrace debug;
  ()
  (* XXX fixme 8.14 *)
  (* Flags.debug := debug *)

let version =
  Coq_config.version, Coq_config.caml_version, Coq_config.vo_version
