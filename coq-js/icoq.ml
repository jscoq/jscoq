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


type 'a seq = 'a Seq.t

let rec seq_of_list l = match l with
  | [] -> Seq.empty
  | x :: xs -> fun () -> Seq.Cons (x, seq_of_list xs)

let seq_of_opt o = match o with
  | None -> Seq.empty
  | Some v -> fun () -> Seq.Cons (v, Seq.empty)


(**************************************************************************)
(* Low-level, internal Coq initialization                                 *)
(**************************************************************************)
let coq_init opts =
  let open Names in

  if opts.debug then begin
    Printexc.record_backtrace true;
    Flags.debug := true;
  end;

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

let pp_of_goals () =
  try
    let proof = Proof_global.give_me_the_proof () in
    Printer.pr_open_subgoals ~proof
  with Proof_global.NoCurrentProof -> Pp.str ""

(* Inspection subroutines *)

let libobj_is_leaf obj =
  match obj with
  | Lib.Leaf _ -> true | _ -> false [@@warning "-4"]

let inspect_library ?(env=Global.env ()) () =
  let const_map = Pre_env.((Environ.pre_env env).env_globals.env_constants) in
  let ls = Lib.contents () in
  Seq.flat_map (fun ((_, kn), obj) -> seq_of_opt @@
    if libobj_is_leaf obj && Names.Cmap_env.mem (Names.Constant.make1 kn) const_map then
      Some kn
    else None)
    (seq_of_list ls)

let default_mod_path = Names.ModPath.MPfile Names.DirPath.empty

let inspect_locals ?(env=Global.env ()) ?(mod_path=default_mod_path) () =
  let make_kername id = Names.KerName.make2 mod_path (Names.Label.of_id id) in
  let named_ctx = Pre_env.((Environ.pre_env env).env_named_context.env_named_ctx) in
  seq_of_list (Context.Named.to_vars named_ctx |> Names.Id.Set.elements) |>
    Seq.map make_kername

(** [set_debug t] enables/disables debug mode  *)
let set_debug debug =
  Backtrace.record_backtrace debug;
  Flags.debug := debug

let version =
  Coq_config.version, Coq_config.date, Coq_config.compile_date, Coq_config.caml_version, Coq_config.vo_magic_number
