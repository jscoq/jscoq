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
val execute : bool -> ?pp_code:formatter ->
	      formatter -> string -> unit

(** [init] Initialize the Coq Engine *)
val init : unit -> unit

