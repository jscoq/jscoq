(************************************************************************)
(* coq-layout-engine                                                    *)
(* Copyright 2021 Inria                                                 *)
(* Written by Emilio J. Gallego Arias                                   *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

val layout :
  ?debug:bool ->
  Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> BoxModel.t
