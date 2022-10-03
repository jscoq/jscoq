(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq Interface to be used by JavaScript Ocaml code. Parts based in
   the coq source code.

   Copyright (C) 2016-2017 Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

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

(** [init opts] Initialize the Coq engine *)
val coq_init : coq_opts -> unit
val new_doc : doc_opts -> Stm.doc * Stateid.t

(** [version] returns miscellaneous version information *)
val version : string * string * int32

val mode_of_stm : doc:Stm.doc -> Stateid.t -> in_mode
val context_of_stm : doc:Stm.doc -> Stateid.t -> (Evd.evar_map * Environ.env)

val compile_vo : doc:Stm.doc -> string -> string

(** [set_debug t] enables/disables debug mode  *)
val set_debug : bool -> unit
