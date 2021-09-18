From Coq Require Import Arith Lia.

Lemma monotonic_inverse :
 forall f : nat -> nat,
 (forall x y : nat, x < y -> f x < f y) ->
 forall x y : nat, f x < f y -> x < y.
Proof.
intros f Hmon x y Hlt; case (le_gt_dec y x); auto.
intros Hle; elim (le_lt_or_eq _ _ Hle).
intros Hlt'; elim (lt_asym _ _ Hlt); apply Hmon; auto.
intros Heq; elim (Nat.lt_neq _ _ Hlt); rewrite Heq; auto.
Qed.
 
Lemma add_sub_square_identity : 
 forall a b : nat, (b + a - b) * (b + a - b) = 
 (b + a) * (b + a) + b * b - 2 * ((b + a) * b).
Proof. lia. Qed.
 
Lemma sub_square_identity :
 forall a b : nat, b <= a -> (a - b) * (a - b) = a * a + b * b - 2 * (a * b).
Proof. 
intros a b H; rewrite (le_plus_minus b a H). 
apply add_sub_square_identity.
Qed.

Lemma root_monotonic : forall x y : nat, x * x < y * y -> x < y.
Proof. 
apply (monotonic_inverse (fun x => x * x)). 
apply Nat.square_lt_mono.
Qed.
 
Lemma square_recompose : forall x y : nat, x * y * (x * y) = x * x * (y * y).
Proof. lia. Qed.
 
Section sqrt2_decrease.

Variables (p q : nat).
Hypotheses (pos_q : 0 < q) (hyp_sqrt : p * p = 2 * (q * q)).
 
Lemma sqrt_q_non_zero : 0 <> q * q.
Proof. lia. Qed.

Local Ltac solve_comparison :=
  apply root_monotonic; repeat rewrite square_recompose; rewrite hyp_sqrt;
   rewrite (mult_assoc _ 2 _); apply mult_lt_compat_r;
    auto using sqrt_q_non_zero with arith.
 
Lemma comparison1 : q < p.
Proof.
replace q with (1 * q); try ring.
replace p with (1 * p); try ring.
solve_comparison.
Qed.

Lemma comparison2 : 2 * p < 3 * q.
Proof. solve_comparison. Qed.
 
Lemma comparison3 : 4 * q < 3 * p.
Proof. solve_comparison. Qed.

Lemma comparison4 : 3 * q - 2 * p < q.
Proof.
apply plus_lt_reg_l with (2 * p).
rewrite <- le_plus_minus; 
 try (simple apply lt_le_weak; auto using comparison2 with arith).
replace (3 * q) with (2 * q + q); try ring.
apply plus_lt_le_compat; auto.
repeat rewrite (mult_comm 2); apply mult_lt_compat_r;
auto using comparison1 with arith.
Qed.

Lemma minus_eq_decompose :
 forall a b c d : nat, a = b -> c = d -> a - c = b - d.
Proof. lia. Qed.
 
Lemma new_equality :
 (3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p)).
Proof.
repeat rewrite sub_square_identity; auto using comparison2,comparison3 with arith.
repeat rewrite square_recompose; rewrite Nat.mul_sub_distr_l.
apply minus_eq_decompose; try rewrite hyp_sqrt; ring.
Qed.

End sqrt2_decrease.

Theorem sqrt2_not_rational :
 forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> False.
Proof.
intros p q; generalize p; clear p; elim q using (well_founded_ind lt_wf).
clear q; intros q Hrec p Hneq; generalize (neq_O_lt _ (sym_not_equal Hneq));
 intros Hlt_O_q Heq.
apply (Hrec (3 * q - 2 * p) (comparison4 _ _ Hlt_O_q Heq) (3 * p - 4 * q)).
apply sym_not_equal; apply Nat.lt_neq; apply plus_lt_reg_l with (2 * p);
 rewrite <- plus_n_O; rewrite <- le_plus_minus; auto using lt_le_weak,comparison2.
apply new_equality; auto.
Qed.
