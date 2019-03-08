(* Parts taken from classfun.v:                                         *)
(* (c) Copyright Microsoft Corporation and Inria.                       *)
(* You may distribute this file under the terms of the CeCILL-B license *)

(* Copyright (c) 2015, CRI, MINES ParisTech, PSL Research University    *)
(* All rights reserved.                                                 *)
(* You may distribute this file under the terms of the CeCILL-B license *)

From mathcomp
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice.
From mathcomp
Require Import fintype tuple finfun bigop prime ssralg poly.
From mathcomp
Require Import finset fingroup perm.
From mathcomp
Require Import matrix mxalgebra vector ssrnum zmodp ssrint intdiv algC cyclotomic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

(* Auxiliary algebra lemmas *)
Section AlgAux.

(*
 * The lemmas below are not in Mathcomp, could they be candidates?
 **)

Lemma eq_mulr (R : unitRingType) (x y z : R) (y_unit : y \is a GRing.unit) :
  (x * y == z) = (x == z / y).
Proof. by rewrite -(can_eq (divrK y_unit)) -mulrA divrr ?mulr1. Qed.

Lemma eq_mull (R : comUnitRingType) (x y z : R) (x_unit : x \is a GRing.unit) :
  (x * y == z) = (y == z / x).
Proof. by rewrite mulrC eq_mulr. Qed.

(* Explicit sum of geometric series. *)
Lemma sumr_expr (F : fieldType) n (r : F) (r_neq1 : r != 1) :
  \sum_(0 <= i < n) r ^+ i = (1 - r ^+ n) / (1 - r).
Proof.
apply/eqP; rewrite -eq_mulr; last by rewrite unitfE subr_eq add0r eq_sym.
by rewrite -opprB subrX1 -mulNr -opprB opprK mulrC big_mkord.
Qed.

Lemma sum1_expr (F : fieldType) n : \sum_(0 <= i < n) 1 ^+ i = n%:R :> F.
Proof.
rewrite (eq_bigr _ (fun i _ => expr1n _ i)).
by rewrite big_mkord sumr_const card_ord.
Qed.

End AlgAux.

Section PrimitiveRoot.

Variable N : nat.
Notation n := N.+2.
Variable F : fieldType.
Variable z : F.
Hypothesis zP : n.-primitive_root z.

Lemma z_neq1 : z != 1.
Proof. by rewrite (eq_prim_root_expr zP 1 0). Qed.

Lemma z_expr_neq1 i : (0 < i < n)%N -> z ^+ i != 1.
Proof.
by case/andP=>??; rewrite (eq_prim_root_expr zP i 0) eqn_mod_dvd ?subn0 ?gtnNdvd.
Qed.

Lemma unitrzn : z ^+ n \is a GRing.unit.
Proof. by rewrite prim_expr_order ?unitr1. Qed.

Lemma unitrz : z \is a GRing.unit.
Proof. by rewrite -(unitrX_pos _ (ltn0Sn n.-1)) ?unitrzn. Qed.

Lemma z_neq0 : z != 0.
Proof. by rewrite -unitfE unitrz. Qed.

Lemma sum_expr_z_zero : \sum_(0 <= j < n) z ^+ j = 0.
Proof. by rewrite sumr_expr ?z_neq1 ?prim_expr_order ?subrr ?mul0r. Qed.

Lemma prim_expr_oppr (i : 'I_n) : z ^+ (-i) = z ^- i.
Proof.
rewrite -[z^-i]mul1r -(prim_expr_order zP) -exprB ?unitrz ?prim_expr_mod //.
by rewrite ltnW ?ltn_ord.
Qed.

(* XXX: This has to change *)
Lemma prim_expr_addn (i j : 'I_n) : z ^+ (i + j) = z ^+ (i + j)%R.
Proof. by rewrite prim_expr_mod. Qed.

Lemma prim_expr_muln (i j : 'I_n) : z ^+ (i * j) = z ^+ (i * j)%R.
Proof. by rewrite prim_expr_mod. Qed.

End PrimitiveRoot.

Section PrimitiveNumRoot.

Variable N : nat.
Notation n := N.+2.
Variable R : numDomainType.
Variable z : R.
Hypothesis zP : n.-primitive_root z.

(* Norms and primitive roots *)
Lemma norm_prim : `|z| = 1.
Proof.
apply: (pexpIrn (ltn0Sn n.-1)); rewrite ?nnegrE ?normr_ge0 //.
by rewrite -normrX prim_expr_order ?expr1n ?normr1.
Qed.

Lemma norm_primX k : `|z^+k| = 1.
Proof. by rewrite normrX norm_prim expr1n. Qed.

(* Lemma norm_neg : z *)
End PrimitiveNumRoot.

Section PrimitiveRootC.

Variable N : nat.
Notation n := N.+2.

Definition p_root :=
  let: exist z _ := C_prim_root_exists (ltn0Sn n.-1) in z.

Notation z := p_root.

Lemma zP : n.-primitive_root p_root.
Proof. by rewrite /p_root; case: (C_prim_root_exists _). Qed.

Lemma conj_zP : n.-primitive_root z^*.
Proof. by rewrite fmorph_primitive_root zP. Qed.

Hint Resolve zP conj_zP.

(* Conjugate and algebraic primitive roots *)
Lemma prim_conj : z^* = z^-1.
Proof. by rewrite invC_norm (norm_prim zP) expr2 mul1r invr1 mul1r. Qed.

Lemma prim_expr_conj k : (z ^+ k)^* = z ^- k.
Proof. by rewrite rmorphX prim_conj exprVn. Qed.

(* Orthogonality and (vector) norm *)
Lemma prim_exprnX i : z ^+ n ^+ i = 1.
Proof. by rewrite (prim_expr_order zP) expr1n. Qed.

Lemma prim_exprXn i : z ^+ i ^+ n = 1.
Proof. by rewrite exprAC prim_exprnX. Qed.

Lemma inner_z (i j : 'I_n) : \sum_(k < n) (z ^+ (i * k)) * (z ^+ (j * k))^* = n%:R * (i == j)%:R.
Proof.
transitivity (\sum_(k < n) z^+(i - j)%R ^+ k).
  apply: eq_bigr => k _.
  rewrite prim_expr_conj !prim_expr_muln -?prim_expr_oppr //.
  rewrite -exprD prim_expr_addn //.
  by rewrite -mulrBl -prim_expr_muln // exprM.
case: eqP => [->| /eqP Hneq ].
  by rewrite subrr expr0 -(big_mkord predT) sum1_expr mulr_natr.
rewrite mulr_natr mulr0n -(big_mkord predT) sumr_expr.
  by rewrite exprAC (prim_expr_order zP) expr1n subrr mul0r.
rewrite (z_expr_neq1 zP) // ltn_ord andbT ltn_neqAle.
by rewrite -subr_eq0 eq_sym in Hneq; rewrite Hneq.
Qed.

Local Open Scope nat.
Lemma mod_sub_transfer (k m : 'I_n) (H : (k <= m) ) :
   (m - k)%R == m - k %[mod n].
Proof.
rewrite modn_mod /= -[(m-k)%%n]modnDl.
rewrite addnBA ?[n+m]addnC -?addnBA //; last by rewrite ltnW.
by rewrite eqn_modDl modn_mod.
Qed.
Local Open Scope ring_scope.

End PrimitiveRootC.

Arguments zP [N].
Arguments conj_zP [N].
Hint Resolve zP conj_zP.
