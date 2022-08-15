(************************************************************************)
(* coq-layout-engine                                                    *)
(* Copyright 2021 Inria                                                 *)
(* Written by Emilio J. Gallego Arias                                   *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* Note: This file is independent of Coq        *)
(* XXX: TODO enforce the above in the dune file *)
type abs_kind = Prod | Lam

module Id : sig

  type 'a t =
    { relative : string
    ; absolute : string option
    ; typ : 'a option
    }

end

module Variable : sig
  type 'a t =
    { name : string
    ; typ : 'a
    }
end

module Binder : sig

  type 'a t =
    { namel : string list
    ; typ : 'a
    }

end

(** Output Layout Box model, designed to be embedded in DOM almost
   directly, and to replace Pp.t *)
type t =
  | Variable of t Variable.t
  (** Variable *)

  | Constant of string
  (** Constant *)

  | Identifier of t Id.t
  (** Identifier *)

  | Sort of string list
  (** Sort *)

  | App of { fn : t
           ; impl : t list
           ; argl : t list
           }
  (** Application box  *)

  | Cast of t * t
  (** Cast box *)

  | Abs of { kind : abs_kind; binderl : t Binder.t list; v : t }
  (** Abstraction  *)

  | Let of { lhs : t; rhs : t; typ : t option; v : t }
  (** Let *)

  | Notation of
      { key : string
      ; args : t list
      ; pretty : t list
      ; raw : t
      }
  (** Notation *)

  | Fixpoint of t * t

(** Simple wrapping in <div>  *)
module Render : sig
  val to_html : t -> [< Html_types.span_content_fun > `PCDATA `Span ] Tyxml.Html.elt
end
