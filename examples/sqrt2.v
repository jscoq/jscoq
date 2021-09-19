(** * Irrationality of the square root of two *)

(**
The original problem on the square root of two arose when
comparing the side with the diagonal of a square,
which reduces to considering an isosceles right triangle.

Below, we prove a statement in Coq of the irrationality
of the square root of two that is expressed only in terms
of natural numbers (Coq's <<nat>>). The proof is a simplified version of a
#<a href="https://github.com/coq-community/qarith-stern-brocot/blob/master/theories/sqrt2.v">proof by Milad Niqui</a>#.
*)

(**
We begin by loading results on arithmetic on natural numbers, and
the lia arithmetic proof tactic.
*)
From Coq Require Import Arith Lia.

(** ** Arithmetic utility results *)

Lemma lt_monotonic_inverse :
 forall f : nat -> nat,
 (forall x y : nat, x < y -> f x < f y) ->
 forall x y : nat, f x < f y -> x < y.
Proof.
intros f Hmon x y Hlt; case (le_gt_dec y x); auto.
intros Hle; case (le_lt_or_eq _ _ Hle).
intros Hlt'; case (lt_asym _ _ Hlt); apply Hmon; auto.
intros Heq; case (Nat.lt_neq _ _ Hlt); rewrite Heq; auto.
Qed.
 
Lemma sub_square_identity :
 forall a b : nat, b <= a -> (a - b) * (a - b) = a * a + b * b - 2 * (a * b).
Proof.
intros a b H.
rewrite (le_plus_minus b a H); lia.
Qed.

Lemma root_monotonic : forall x y : nat, x * x < y * y -> x < y.
Proof. 
apply (lt_monotonic_inverse (fun x => x * x)).
apply Nat.square_lt_mono.
Qed.

(** The lia tactic easily proves simple arithmetic statements. *)
Lemma square_recompose : forall x y : nat, x * y * (x * y) = x * x * (y * y).
Proof. lia. Qed.

(** ** Key arithmetic lemmas *)

Section sqrt2_decrease.
(** We use sections to simplify lemmas that use the same assumptions. *)
Variables (p q : nat).
Hypotheses (pos_q : 0 < q) (hyp_sqrt : p * p = 2 * (q * q)).
 
Lemma sqrt_q_non_zero : 0 <> q * q.
Proof. lia. Qed.

(** We define a local custom proof tactic. *)
Local Ltac solve_comparison :=
  apply root_monotonic; repeat rewrite square_recompose; rewrite hyp_sqrt;
   rewrite (mult_assoc _ 2 _); apply mult_lt_compat_r;
    auto using sqrt_q_non_zero with arith.
 
Lemma comparison1 : q < p.
Proof.
replace q with (1 * q); try lia.
replace p with (1 * p); try lia.
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
replace (3 * q) with (2 * q + q); try lia.
apply plus_lt_le_compat; auto.
repeat rewrite (mult_comm 2); apply mult_lt_compat_r;
auto using comparison1 with arith.
Qed.
 
Lemma new_equality :
 (3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p)).
Proof.
repeat rewrite sub_square_identity;
 auto using comparison2,comparison3 with arith.
lia.
Qed.

(**
After the section, lemmas inside the section are generalized
with the variables and hypotheses they use.
*)
End sqrt2_decrease.

(** ** Statement and proof *)

(** The proof proceeds by well-founded induction on q.
We apply the induction hypothesis with the numbers <<3 * q - 2 * q>>
and <<3 * p - 4 * q>>. This leaves two key proof goals:
- <<3 * q - 2 * p <> 0>>, which we prove using arithmetic and the
  [comparison2] lemma above.
- <<(3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p))>>,
  which we prove using the [new_equality] lemma above.
*)
Theorem sqrt2_not_rational :
 forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> False.
Proof.
intros p q; generalize p; clear p; elim q using (well_founded_ind lt_wf).
clear q; intros q Hrec p Hneq.
generalize (neq_O_lt _ (sym_not_equal Hneq)); intros Hlt_O_q Heq.
apply (Hrec (3 * q - 2 * p) (comparison4 _ _ Hlt_O_q Heq) (3 * p - 4 * q)).
- apply sym_not_equal; apply Nat.lt_neq; apply plus_lt_reg_l with (2 * p).
  rewrite <- plus_n_O; rewrite <- le_plus_minus; auto using lt_le_weak,comparison2.
- apply new_equality; auto.
Qed.
