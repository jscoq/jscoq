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

(** [init opts] Initialize the Coq engine *)
val coq_init : coq_opts -> Stm.doc * Stateid.t

(** [version] returns miscellaneous version information *)
val version : string * string * string * string * int

(** [richpp_of_goals ()] returns a pp representing the current goals  *)
val pp_of_goals : unit -> Pp.t (* Proof.pre_goals *)

val inspect_library : ?env:Environ.env -> unit -> Names.KerName.t seq
val inspect_locals : ?env:Environ.env -> ?mod_path:Names.ModPath.t -> unit -> Names.KerName.t seq

(** [set_debug t] enables/disables debug mode  *)
val set_debug : bool -> unit
