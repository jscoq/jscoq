(* From Coq Require Import ssrsearch. *)
From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

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

End PrimitiveRootC.

Hint Resolve zP conj_zP.

Section DftSum.

Variable N' : nat.
Notation N := N'.+2.
Notation R := algC.
Notation S := 'cV[R]_N.

Notation "'ω" := (@p_root N').
Implicit Types x y : S.

Definition dft x k := \sum_m (x m 0) * 'ω ^+ (k * m).

(* Trivial properties: Linearity & scaling *)
Lemma dft_sum x y k : dft (x + y) k = dft x k + dft y k.
Proof.
by rewrite -big_split /=; apply/eq_bigr=> i _; rewrite -mulrDl mxE.
Qed.

Lemma dft_scale a x k : a * dft x k = dft (a *: x) k.
Proof.
by rewrite mulr_sumr; apply/eq_bigr=> ? _; rewrite mxE mulrA.
Qed.

Definition shifts d x := \col_n (x (n - d) 0).
Lemma shiftsE d x i j : (shifts d x) i j = x (i - d) 0.
Proof. by rewrite mxE. Qed.

Lemma dft_shifts d x k : dft (shifts d x) k = 'ω ^+ (k * d) * dft x k.
Proof.
rewrite /dft (reindex_inj (addIr d)) mulr_sumr.
apply/eq_bigr => i _; rewrite shiftsE.
by rewrite addrK mulrCA mulnC !exprM prim_expr_mod // exprAC addnC exprD.
Qed.

Definition convs x y := \col_n \sum_m x m 0 * y (n-m) 0.

Lemma dft_convs x y k : dft (convs x y) k = dft x k * dft y k.
Proof.
rewrite /dft (eq_bigr (fun i => \sum_m x m 0 * y (i - m) 0 * 'ω ^+ (k*i)));
 last by move=> ? ?; rewrite !mxE mulr_suml.
rewrite big_distrlr /= exchange_big /=.
apply/eq_bigr=> i _ /=.
rewrite -!mulr_sumr -mulrA -dft_shifts mulr_sumr.
by apply/eq_bigr => j _; rewrite shiftsE mulrA.
Qed.

End DftSum.
