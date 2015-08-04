(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq Interface to be used by JavaScript Ocaml code. Parts based in
   the coq source code.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Feedback

(* Init options for coq *)
type init_opts = {

  (* callback to load cma files *)
  ml_load    : string -> unit;

  (* callback to handle async feedback *)
  fb_handler : feedback -> unit;

}

(** [init opts] Initialize the Coq engine *)
val init : init_opts -> Stateid.t

(** [version] returns miscellaneous version information *)
val version : string * string * string * string

(** [dyn_comp] true if dynamic compilation is enabled *)
val dyn_comp : bool

(** [add_load_path qid path] associate a coq package namespace [qid]
    to a [path] *)
val add_load_path : string list -> string -> unit

(** [add_to_doc sid eid cmd] Add [cmd] to the doc [sid] with edit_id
    [eid] and returns the new doc's stateid. Note that [add_to_doc] doesn't
    force Coq to process the new parts of the document, see [commit] *)
val add_to_doc : Stateid.t -> edit_id -> string -> Stateid.t

(** [edit_doc sid] moves the tip of the document to [sid], discarding
    all edits added after [sid] *)
val edit_doc : Stateid.t -> unit

(** [commit ()] commit the changes to the current document. It can
    produce an exception in case of error. *)
val commit : unit -> unit



