(* Example of serialization to a sexp:

   Coq's main datatype, constr, is a private type so we need to define
   a serializable clone. Unfortunately, it's main view is "zippy" so we
   need to recurse throught a constr in order to fully build its clone.

   Another, and maybe better, option is to use extern_constr and
   serialize that one.
*)

(* Main type to be cloned:

type ('constr, 'types) kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of metavariable
  | Evar      of 'constr pexistential
  | Sort      of Sorts.t
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of Name.t * 'types * 'types
  | Lambda    of Name.t * 'types * 'constr
  | LetIn     of Name.t * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of constant puniverses
  | Ind       of inductive puniverses
  | Construct of constructor puniverses
  | Case      of case_info * 'constr * 'constr * 'constr array
  | Fix       of ('constr, 'types) pfixpoint
  | CoFix     of ('constr, 'types) pcofixpoint
  | Proj      of projection * 'constr
*)

module C = Constr
module N = Names

open Sexplib.Std

type coq_name = NS of string | Anonymous [@@deriving sexp]

type coq_sort = Prop | Type (* of universe Sorts.t *) [@@deriving sexp]

type coq_constr =
  | Rel       of int
  | Var       of string
  | Meta      of int
  | Evar      of int * coq_constr array
  | Sort      of coq_sort
  | Cast      of coq_constr *  (* C.cast_kind * *) coq_types
  | Prod      of coq_name * coq_types * coq_types
  | Lambda    of coq_name * coq_types * coq_constr
  | LetIn     of coq_name * coq_constr * coq_types * coq_constr
  | App       of coq_constr * coq_constr array
  | Const     of string        (* XXX: Missing universe instance *)
  | Ind       of string        (* XXX: Missing universe instance *)
  | Construct of string        (* XXX: Missing universe instance *)
  | Case      of (* C.case_info *  *) coq_constr * coq_constr * coq_constr array
  | Fix       of string        (* XXX: I'm lazy *)
  | CoFix     of string        (* XXX: I'm lazy *)
  | Proj      of string * coq_constr
and coq_types = coq_constr [@@deriving sexp]

let name_reify (n : N.Name.t) : coq_name =
  match n with
  | N.Name.Name id   -> NS (N.Id.to_string id)
  | N.Name.Anonymous -> Anonymous

let sort_reify (s : Sorts.t) : coq_sort =
  match s with
  | Sorts.Prop _ -> Prop
  | Sorts.Type _ -> Type

let rec constr_reify (c : C.constr) : coq_constr =
  let nr  = name_reify             in
  let cr  = constr_reify           in
  let cra = Array.map constr_reify in
  match C.kind c with
  | C.Rel i              -> Rel(i)
  | C.Var v              -> Var(N.Id.to_string v)
  | C.Meta(mv)           -> Meta mv
  | C.Evar(ek, csa)      -> Evar (Evar.repr ek, Array.map constr_reify csa)
  | C.Sort(st)           -> Sort (sort_reify st)
  | C.Cast(cs,_k,ty)     -> Cast(cr cs, cr ty)
  | C.Prod(n,tya,tyr)    -> Prod(nr n, cr tya, cr tyr)
  | C.Lambda(n,ab,bd)    -> Lambda(nr n, cr ab, cr bd)
  | C.LetIn(n,u,ab,bd)   -> LetIn(nr n, cr u, cr ab, cr bd)
  | C.App(hd, al)        -> App(cr hd, cra al)
  | C.Const(p,_)         -> Const (N.Constant.to_string p)
  | C.Ind((p,_),_)       -> Ind (N.MutInd.to_string p)
  | C.Construct(((c,_),_),_) -> Construct (N.MutInd.to_string c)
  | C.Case(_ci, d, c, ca) -> Case(cr d, cr c, cra ca)
  | C.Fix _              -> Fix "I'm lazy"
  | C.CoFix _            -> CoFix "I'm lazy"
  | C.Proj(p,c)          -> Proj(N.Projection.to_string p, cr c)

let sexp_of_proof () : Sexplib.Sexp.t option =
  let open Proof_global in
  try
    let pf = give_me_the_proof ()                                 in
    let (goals, stack , shelf, given_up, sigma ) = Proof.proof pf in
    match goals with
    | []     -> None
    | g :: _ ->
      let g_type = Goal.V82.concl sigma g                   in
      (* let env    = Goal.V82.env   sigma g                           in *)
      (* let _term  = Constrextern.extern_constr true env sigma g_type in *)
      (* let _k     = Term.kind_of_term g_type                         in *)
      Some (sexp_of_coq_constr (constr_reify g_type))
  with NoCurrentProof -> None

let string_of_proof () : string =
  Option.cata Sexplib.Sexp.to_string "" (sexp_of_proof ())
