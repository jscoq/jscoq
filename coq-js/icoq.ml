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
  iload_path   : Mltop.coq_path list;

  (* Libs to require prior to STM init *)
  require_libs : (string * string option * bool option) list;

  (* Async flags *)
  aopts        : async_flags;

  (* name of the top-level module *)
  top_name     : string;

  (* callback to load cma/cmo files *)
  ml_load    : string -> unit;

  (* Enable debug mode *)
  debug    : bool;
}


external coq_vm_trap : unit -> unit = "coq_vm_trap"


type 'a seq = 'a Seq.t

let rec seq_append s1 s2 =  (* use batteries?? *)
  match s1 () with
  | Seq.Nil -> s2
  | Seq.Cons (x, xs) -> fun () -> Seq.Cons (x, seq_append xs s2)


(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =
  let open Names in

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

  (**************************************************************************)
  (* Feedback setup                                                         *)
  (**************************************************************************)

  (* Initialize logging. *)
  ignore(Feedback.add_feeder opts.fb_handler);

  (**************************************************************************)
  (* Start the STM!!                                                        *)
  (**************************************************************************)
  Stm.init_core ();

  (* Return the initial state of the STM *)
  let sertop_dp = DirPath.make [Id.of_string opts.top_name] in
  let ndoc = { Stm.doc_type = Stm.Interactive sertop_dp;
               require_libs = opts.require_libs;
               iload_path = opts.iload_path;
               stm_options = Stm.AsyncOpts.default_opts } in
  let ndoc, nsid = Stm.new_doc ndoc in
  ndoc, nsid

let context_of_st m = match m with
  | `Valid (Some st) ->
    begin try
        Pfedit.get_current_context ~p:(Proof_global.proof_of_state st.Vernacstate.proof) ()
      with Proof_global.NoCurrentProof ->
        Pfedit.get_current_context ()
    end
  | _ ->
    let env = Global.env () in Evd.from_env env, env

let context_of_stm ~doc sid =
  let st = Stm.state_of_id ~doc sid in
  context_of_st st

(* Inspection subroutines *)

let inspect_globals ~env () =
  let global_consts = List.to_seq @@
      Environ.fold_constants (fun name _ l -> name :: l) env [] in
  global_consts |> Seq.map Names.Constant.user

let libobj_is_leaf obj =
  match obj with
  | Lib.Leaf _ -> true | _ -> false [@@warning "-4"]

let kn_sibling kn id =
  let (mp, dp, _) = Names.KerName.repr kn in
  Names.KerName.make mp dp (Names.Label.of_id id)

let lookup_constant env kn =
  try
    ignore @@ Environ.lookup_constant (Names.Constant.make1 kn) env;
    Seq.return kn
  with Not_found -> Seq.empty

let lookup_inductive env kn =
  let open Declarations in
  try
    let defn_body = Environ.lookup_mind (Names.MutInd.make1 kn) env in
    Array.to_seq defn_body.mind_packets
      |> Seq.map (fun p -> kn_sibling kn (p.mind_typename))
  with Not_found -> Seq.empty

let find_definitions env kn = seq_append (lookup_constant env kn) (lookup_inductive env kn)

let inspect_library ~env () =
  let ls = Lib.contents () in
  Seq.flat_map (fun ((_, kn), obj) ->
    if libobj_is_leaf obj then find_definitions env kn
    else Seq.empty)
    (List.to_seq ls)

let default_mod_path = Names.ModPath.MPfile Names.DirPath.empty

let inspect_locals ~env ?(mod_path=default_mod_path) () =
  let make_kername id = Names.KerName.make2 mod_path (Names.Label.of_id id) in
  let named_ctx = Environ.named_context env in
  List.to_seq (Context.Named.to_vars named_ctx |> Names.Id.Set.elements) |>
    Seq.map make_kername

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Backtrace.record_backtrace debug;
  Flags.debug := debug

let version =
  Coq_config.version, Coq_config.date, Coq_config.compile_date, Coq_config.caml_version, Coq_config.vo_magic_number
