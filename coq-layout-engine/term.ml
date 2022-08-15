(************************************************************************)
(* coq-layout-engine                                                    *)
(* Copyright 2021 Inria                                                 *)
(* Written by Emilio J. Gallego Arias                                   *)
(************************************************************************)
(* Status: Very Experimental                                            *)
(************************************************************************)

(* typrinter *)

(* introduce an unparsing monad *)

open CAst
open Constrexpr

(* notes with the discussion with Hugo:

 - there are two kinds of information that the printer can know:

   + parsing-level: this includes notations, implicit arities, etc...
   + semantic-level: only after typchecking has run! For example coertions!

 - how to remember for example the type of a sub-expression:

   The expression goes from Ast.t to Term.t, then goes back to Ast.t for printing.

   + doing it for all types, it is too expensive
   + doing it for some, requires a way to specify which
   + an interesting idea is to attach all the possible requests over the structure of a term
     in the term itself once it has been recosntructed from the typing phase

 - continuation maybe a meeting with Clement and Shachar?

 *)

module BM = BoxModel

let xxx str = BoxModel.Constant ("FIXME: " ^ str)

let ly_prim_token ptok =
  match ptok with
  | Number e -> BM.Constant (NumTok.Signed.sprint e)
  | String a -> BM.Constant a

let ly_sort_name_expr (s : sort_name_expr) =
  (match s with
   | CSProp -> "SProp"
   | CProp -> "Prop"
   | CSet -> "Set"
   | CType _qid -> "Type"
   | CRawType _ulvl -> "Type")

(* FIXME: _i *)
let ly_named_sort ((s,_i) : sort_name_expr * int) =
  ly_sort_name_expr s

let ly_sort (s : sort_expr) =
  match s with
  | Glob_term.UAnonymous { rigid } ->
    (* XXX: What's going on here *)
    if rigid then BM.Sort ["Type"] else BM.Sort ["Type"]
  | Glob_term.UNamed sl ->
    BM.Sort (List.map ly_named_sort sl)

type cast_kind = VMcast | NATIVEcast | DEFAULTcast

let ly_cast_kind (s : Constr.cast_kind) =
  match s with
  | VMcast ->
    xxx "VMcast"
  | NATIVEcast ->
    xxx "NATIVEcast"
  | DEFAULTcast ->
    xxx "DEFAULTcast"

let ly_qualid { Coq_util.Id.relative; absolute; typ } =
  let relative = Libnames.string_of_qualid relative in
  let absolute = Option.map Libnames.string_of_path absolute in
  BoxModel.Identifier { relative; absolute; typ }

let ly_fixexpr _ = BoxModel.Constant "TODO"
let ly_cofixexpr _ = BoxModel.Constant "TODO"

(* instance_expr = univ_level_expr list *)
let ly_instance_expr (_e : instance_expr) = []

[@@@ocaml.warning "-26-27"]

let abs_kind_of (t : constr_expr) =
  match t.CAst.v with
  | CProdN _ -> BoxModel.Prod
  | CLambdaN _ -> BoxModel.Lam
  | _ -> BoxModel.Lam           (* XXX *)

let _debug = ref false
let env = ref Environ.empty_env
let sigma = ref Evd.empty

let rec ly_hunks unp args =
  let open Ppextend in
  match unp with
  | [] -> []
  | UnpMetaVar _ :: l ->
    let la = List.hd args in
    let lr = ly_hunks l (List.tl args) in
    la :: lr
  | UnpTerminal s :: l ->
    BM.Constant s :: ly_hunks l args
  | UnpBox (_,l1) :: l ->
    let l1 = List.map (fun (_,l) -> l) l1 in
    ly_hunks (l1@l) args
  | UnpCut _ as unp :: l ->
    ly_hunks l args
  | _ ->
    [xxx "not_printer"]

let lname_to_string = CAst.with_val (function
    | Names.Anonymous -> "_"
    | Names.Name id -> Names.Id.to_string id)

let ly_notation key args =
  let { Ppextend.notation_printing_unparsing; notation_printing_level } = Ppextend.find_notation_printing_rule None key in
  ly_hunks notation_printing_unparsing args

let rec ly_qid qid =
  let id_info = Coq_util.Id.make qid in
  let id_info = Coq_util.Id.map_typ ~f:layout id_info in
  ly_qualid id_info

and ly_id id =
  ly_qid (Libnames.qualid_of_ident id)

and ly_lid (lid : Names.lident) =
  ly_id lid.v

and ly_lname (lid : Names.lname) =
  match lid.v with
  | Names.Anonymous -> xxx "name.anonymous"
  | Names.Name id -> ly_id id

and ly_binder_expr (b : local_binder_expr) =
  match b with
  | CLocalAssum (namel, kind, pat) ->
    let namel = List.map lname_to_string namel in
    { BM.Binder.namel; typ = layout pat }
  | CLocalDef (name, pat, pat_tyo) ->
    { BM.Binder.namel = ["XXX localdef"]; typ = layout pat }
  | CLocalPattern pat ->
    { BM.Binder.namel = ["XXX localpat"]; typ = xxx "local pat" }

and layout t =
  if !_debug then
    Feedback.msg_warning Pp.(str "ly [->]: " ++ Ppconstr.pr_constr_expr !env !sigma t);

  let res =
  match t.CAst.v with

  (* | CRef     of qualid * instance_expr option *)
  | CRef (qid, iexp) ->
    let _ = Option.map ly_instance_expr iexp in
    ly_qid qid

  (* | CFix     of lident * fix_expr list *)
  | CFix (lid, fixexpr) ->
    BoxModel.Fixpoint (ly_lid lid, ly_fixexpr fixexpr)

  (* | CCoFix   of lident * cofix_expr list *)
  | CCoFix (lid, cofixexpr) ->
    BoxModel.Fixpoint (ly_lid lid, ly_cofixexpr cofixexpr)

  (* | CProdN   of local_binder_expr list * constr_expr *)
  (* | CLambdaN of local_binder_expr list * constr_expr *)
  | CProdN (bds, inner)
  | CLambdaN (bds, inner) ->
    let kind = abs_kind_of t in
    let binderl = List.map ly_binder_expr bds in
    BoxModel.Abs { kind; binderl; v = layout inner }

  (* | CLetIn   of lname * constr_expr * constr_expr option * constr_expr *)
  | CLetIn (name, e, tyo, ty) ->
    let lhs = ly_lname name in
    let rhs = layout e in
    let typ = Option.map layout tyo in
    BoxModel.Let { lhs; rhs; typ; v = layout ty }

  (* | CAppExpl of (proj_flag * qualid * instance_expr option) * constr_expr list *)
  | CAppExpl ((fn, ioexp), argl) ->
    let impl = [] in
    let argl = List.map layout argl in
    let fn = ly_qid fn in
    BoxModel.App { fn; impl; argl }

  (* | CApp     of (proj_flag * constr_expr) *
   *               (constr_expr * explicitation CAst.t option) list *)
  | CApp (fn, argl) ->
    let impl = [] in
    let argl = List.map (fun (e,_) -> layout e) argl in
    BoxModel.App { fn = layout fn; impl; argl }

  | CProj _ ->
    xxx "proj"

  (* | CRecord  of (qualid * constr_expr) list *)
  | CRecord fl ->
    xxx "record"

  (* representation of the "let" and "match" constructs *)
  (* | CCases of Constr.case_style   (\* determines whether this value represents "let" or "match" construct *\)
   *           * constr_expr option  (\* return-clause *\)
   *           * case_expr list
   *           * branch_expr list    (\* branches *\) *)
  | CCases (sty, rtyo, brl, el) ->
    xxx "cases"

  (* | CLetTuple of lname list * (lname option * constr_expr option) *
   *                constr_expr * constr_expr *)
  | CLetTuple (nl, (no, eo), e1, e2) ->
    xxx "lettuple"

  (* | CIf of constr_expr * (lname option * constr_expr option)
   *        * constr_expr * constr_expr *)
  | CIf (cond, _, et, ef) ->
    xxx "if"

  (* | CHole   of Evar_kinds.t option * Namegen.intro_pattern_naming_expr * Genarg.raw_generic_argument option *)
  | CHole (evar, ipat, genarg) ->
    xxx "hole"

  (* | CPatVar of Pattern.patvar *)
  | CPatVar pat ->
    xxx "patvar"

  (* | CEvar   of Glob_term.existential_name CAst.t * (lident * constr_expr) list *)
  | CEvar (ename, ctx) ->
    xxx "evar"

  (* | CSort   of sort_expr *)
  | CSort s ->
    ly_sort s

  (* | CCast   of constr_expr * Constr.cast_kind * constr_expr *)
  | CCast (e, cast_kind, cast) ->
    let p_c = ly_cast_kind cast_kind in
    let p_e = layout e in
    Cast (p_c,p_e)

  (* | CNotation of notation_with_optional_scope option * notation * constr_notation_substitution *)
  | CNotation (oscope, ntn, ntn_subst) ->
    let ntn_entry, key = ntn in
    let args, _, _, _ = ntn_subst in
    let args = List.map layout args in
    let pretty = ly_notation (ntn_entry, key) args in
    let raw = Coq_util.notation_raw !env !sigma t
              |> Option.cata layout (xxx "raw notation failed [binders usually]") in
    Notation { key; args; pretty; raw }

    (* ntn_subst is:

       constr_expr list *      (* for constr subterms *)
       constr_expr list list * (* for recursive notations *)
       kinded_cases_pattern_expr list *   (* for binders *)
       local_binder_expr list list (* for binder lists (recursive notations) *)
    *)

    (* Unparsing for "_ + _":

       (UnpBox
         (PpHOVB 0)
         ((() (UnpMetaVar (LevelLe 50) (Left)))
          (() (UnpTerminal " +"))
          (() (UnpCut (PpBrk 1 0)))
          (() (UnpMetaVar (LevelLt 50) (Right))))))

       Unparsing for "_ = _":

       (UnpBox
         (PpHOVB 0)
         ((() (UnpMetaVar (LevelLt 70) (Left)))
         (() (UnpTerminal " ="))
         (() (UnpCut (PpBrk 1 0)))
         (() (UnpMetaVar (LevelLt 70) (Right)))))

   Unparsing for "_ -> _":

   (UnpBox
    (PpHOVB 0)
    ((() (UnpMetaVar (LevelLt 99) (Left)))
     (() (UnpTerminal " ->"))
     (() (UnpCut (PpBrk 1 0)))
     (() (UnpMetaVar (LevelLe 200) ()))))

  (Query () (Unparsing "exists2 _ : _ , _ & _"))

  (UnpBox
   (PpHOVB 0)
   ((() (UnpTerminal "exists2"))
    (() (UnpCut (PpBrk 1 2)))
    (() (UnpBinderMetaVar LevelSome NotQuotedPattern))
    (() (UnpTerminal " "))
    (() (UnpTerminal ":"))
    (() (UnpTerminal " "))
    (() (UnpMetaVar (LevelLe 200) ()))
    (() (UnpTerminal ","))
    (() (UnpCut (PpBrk 1 2)))
    (()
     (UnpBox
      (PpHOVB 0)
      ((() (UnpMetaVar (LevelLe 200) ()))
       (() (UnpTerminal " "))
       (() (UnpTerminal "&"))
       (() (UnpCut (PpBrk 1 0)))
       (() (UnpMetaVar (LevelLe 200) (Right))))))))

  *)


  (* | CGeneralization of Glob_term.binding_kind * abstraction_kind option * constr_expr *)
  | CGeneralization _ ->
    xxx "generalization"

  (* | CPrim of prim_token *)
  | CPrim ptok ->
    ly_prim_token ptok

  (* | CDelimiters of string * constr_expr *)
  | CDelimiters (delim, e) ->
    xxx "delimiters"

  (* | CArray of instance_expr option * constr_expr array * constr_expr * constr_expr *)
  | CArray (univs, el, eu, ea) ->
    xxx "array"

  in

  if !_debug then
    Feedback.msg_warning Pp.(str "ly [<-]: " ++ Ppconstr.pr_constr_expr !env !sigma t);

  res

let layout ?(debug=false) e s t =
  _debug := debug;
  env := e;
  sigma := s;
  layout t
