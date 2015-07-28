(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Helpers for the Coq JavaScript Toplevel. Based in the coq source
   code and js_of_ocaml toplevel.

   By Emilio J. Gallego Arias, Mines ParisTech, Paris.
*)

open Format

(** [execute print fmt content] Execute [content].
    [print] says whether the values and types of the results should be printed.
    [pp_code] formatter can be use to output ocaml source during lexing. *)
(* val execute : bool -> ?pp_code:formatter -> *)
(* 	      formatter -> string -> unit *)
val execute : string -> bool

(* [add_load_path qid path] associate a coq package namespace [qid] to a [path] *)
val add_load_path : string list -> string -> unit

(** [init load_ml] Initialize the Coq engine, [load_ml] is a function
    that will load .cma plugins and will be frontend-dependent.
 *)
val init : (string -> unit) -> unit

(** [version] returns miscellaneous version information  *)
val version : string * string * string * string

(* Enable dynamic compilation *)
val dyn_comp : bool
