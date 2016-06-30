(************************************************************************)
(* Coq SerAPI Plugin                                                    *)
(* Copyright 2016 Emilio J. Gallego Arias, MINES ParisTech              *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)
(* LICENSE: GPLv3+                                                      *)
(************************************************************************)

type ser_doc = Stm.doc * Stateid.t list

val create : Stm.doc -> ser_doc

val add :
  doc:ser_doc        ->
  ontop:Stateid.t    ->
  newid:Stateid.t    ->
  string             ->
  Loc.t option * [ `NewTip | `Unfocus of Stateid.t ] * ser_doc

val cancel  : doc:ser_doc -> Stateid.t -> Stateid.t list * ser_doc

(** [observe ~doc sid] evals up to state [sid] on document [doc]. *)
val observe : doc:ser_doc -> Stateid.t -> ser_doc

(* Deprecated *)
val edit   : doc:ser_doc -> Stateid.t -> Stateid.t list * ser_doc

