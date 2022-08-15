(************************************************************************)
(* coq-layout-engine                                                    *)
(* Copyright 2021 Inria                                                 *)
(* Written by Emilio J. Gallego Arias                                   *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

val intern_reference : Libnames.qualid -> Names.GlobRef.t option

(* val recover_notation : Environ.env -> Evd.evar_map -> Constrexpr.constr_expr -> Constrexpr.constr_expr option *)

(** [notation_raw env sigma expr] will return [Some raw_expr] if [raw_expr] is the unfolding of a notation [expr] *)
val notation_raw :
  Environ.env
  -> Evd.evar_map
  -> Constrexpr.constr_expr
  -> Constrexpr.constr_expr option

(* XXX: Really a reference *)
module Id : sig

  type 'a t =
    { relative : Libnames.qualid
    ; absolute : Libnames.full_path option
    ; typ : 'a option
    }

  val make : Libnames.qualid -> Constrexpr.constr_expr t
  val map_typ : f:('a -> 'b) -> 'a t -> 'b t

end
