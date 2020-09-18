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

type require_lib = (string * string option * bool option)
type top_mode = Interactive | Vo

type coq_opts = {

  (* callback to handle async feedback *)
  fb_handler : Feedback.feedback -> unit;

  (* Async flags *)
  aopts        : async_flags;

  (* Initial values for Coq options *)
  opt_values   : (string list * Goptions.option_value) list;

  (* callback to load cma/cmo files *)
  ml_load      : string -> unit;

  (* Enable debug mode *)
  debug        : bool;
}

type start_opts = {
  (* Libs to require on startup *)
  require_libs : require_lib list;
  (* Initial LoadPath *)
  vo_path      : Loadpath.vo_path list;
  (* name of the top-level module *)
  top_name     : string;
  (* document mode: interactive or batch *)
  mode         : top_mode;
}

type 'a seq = 'a Seq.t

(** [init opts] Initialize the Coq engine *)
val coq_init : coq_opts -> unit
val start : start_opts -> Stm.doc * Stateid.t

(** [version] returns miscellaneous version information *)
val version : string * string * string * string * int32

val context_of_stm : doc:Stm.doc -> Stateid.t -> (Evd.evar_map * Environ.env)

val inspect_globals : env:Environ.env -> unit -> Libnames.full_path seq
val inspect_library : env:Environ.env -> unit -> Libnames.full_path seq
val inspect_locals  : env:Environ.env -> ?dir_path:Names.DirPath.t -> unit -> Libnames.full_path seq

val compile_vo : doc:Stm.doc -> string -> string

(** [set_debug t] enables/disables debug mode  *)
val set_debug : bool -> unit
