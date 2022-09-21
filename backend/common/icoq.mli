(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Coq Interface to be used by JavaScript Ocaml code. Parts based in
   the coq source code.

   Copyright (C) 2016-2019 Emilio J. Gallego Arias, Mines ParisTech, Paris.
   Copyright (C) 2019-2022 Emilio J. Gallego Arias, Inria, Paris.
   Copyright (C) 2019-2022 Shachar Itzhaky, Tehcnion, Haifa.
*)

type diagnostic = Lsp.Base.Diagnostic.t

type coq_opts =
  { notification_cb : diagnostic -> int -> unit
  (** callback to handle notifications *)
  ; debug        : bool
  (** Enable debug mode *)
}

type require_lib = (string * string option * Lib.export_flag option)

type doc_opts =
  { uri : string
  (** name of the top-level module *)
  ; require_libs : require_lib list
  (** Libs to require on startup *)
  ; opt_values : (string list * Goptions.option_value) list
  (** Initial values for Coq options *)
  ; vo_path : Loadpath.vo_path list
  (** Initial LoadPath *)
  }

(** [init opts] Initialize the Coq engine *)
val coq_init : coq_opts -> unit

(** [new_doc] Initialize a new Coq document *)
val new_doc : doc_opts -> markdown:bool -> text:string -> Controller.Coq_doc.t * Controller.Coq_state.t * diagnostic list

(** [check_doc] check a doc, with possibly updated contents *)
val check_doc
  : doc:Controller.Coq_doc.t
  -> Controller.Coq_doc.t * Controller.Coq_state.t * diagnostic list

(** [version] returns miscellaneous version information *)
val version : string * string * int32

(** [set_debug t] enables/disables debug mode  *)
val set_debug : bool -> unit
