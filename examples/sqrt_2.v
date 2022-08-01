(** * Irrationality of the square root of two *)

(**
The original problem on the square root of two arose when
comparing the side with the diagonal of a square,
which reduces to considering an isosceles right triangle.

Below, we prove a statement in Coq of the irrationality
of the square root of two that is expressed only in terms
of natural numbers (Coq's <<nat>>). The proof is a simplified
version of a #<a href="https://github.com/coq-community/qarith-stern-brocot/blob/master/theories/sqrt2.v">proof by Milad Niqui</a>#.

We begin by loading results on arithmetic on natural numbers,
and the lia arithmetic solver tactic.
*)
From Coq Require Import Utf8 Arith Lia.

(** ** Arithmetic utility results *)

Lemma lt_monotonic_inverse :
  forall f : nat -> nat,
  (forall x y : nat, x < y -> f x < f y) ->
  forall x y : nat, f x < f y -> x < y.
Proof.
  intros f Hmon x y Hlt; case (le_gt_dec y x); auto.
  intros Hle; elim (le_lt_or_eq _ _ Hle).
  intros Hlt'; elim (lt_asym _ _ Hlt); apply Hmon; auto.
  intros Heq; elim (Nat.lt_neq _ _ Hlt); rewrite Heq; auto.
Qed.

(** The lia tactic easily proves linear arithmetic statements. *)
Lemma sub_square_identity :
 forall a b : nat, b <= a -> (a - b) * (a - b) = a * a + b * b - 2 * (a * b).
Proof.
  intros a b H.
  rewrite <- (Nat.sub_add b a H). lia.
Qed.

Lemma root_monotonic : forall x y : nat, x * x < y * y -> x < y.
Proof. 
  apply (lt_monotonic_inverse (fun x => x * x)). 
  apply Nat.square_lt_mono.
Qed.

Lemma square_recompose : forall x y : nat, x * y * (x * y) = x * x * (y * y).
Proof. lia. Qed.

(** ** Key arithmetic lemmas *)

Section sqrt2_decrease.

  (** We use sections to simplify lemmas that use the same assumptions. *)

  Variables (p q : nat).
  Hypotheses (pos_q : 0 <> q) (hyp_sqrt : p * p = 2 * (q * q)).

  Lemma sqrt_q_non_zero : 0 <> q * q.
  Proof. lia. Qed.

  (** Define a local custom proof tactic. *)
  Local Ltac solve_comparison :=
    apply root_monotonic; repeat rewrite square_recompose; rewrite hyp_sqrt;
     rewrite (mult_assoc _ 2 _); apply Nat.mul_lt_mono_pos_r;
      auto using sqrt_q_non_zero with arith.

  Lemma comparison_qp : q < p.
  Proof.
    replace q with (1 * q) by lia.
    replace p with (1 * p) by lia.
    solve_comparison.
  Qed.

  Lemma comparison_2p3q : 2 * p < 3 * q.
  Proof. solve_comparison. Qed.

  Lemma comparison_4q3p : 4 * q < 3 * p.
  Proof. solve_comparison. Qed.

  Lemma comparison_3q2p : 3 * q - 2 * p < q.
  Proof.
    apply Nat.add_lt_mono_l with (2 * p).
    rewrite Nat.add_comm, Nat.sub_add;
    try (simple apply Nat.lt_le_incl; auto using comparison_2p3q).
    replace (3 * q) with (2 * q + q) by lia.
    apply Nat.add_lt_le_mono; auto.
    repeat rewrite (Nat.mul_comm 2); apply Nat.mul_lt_mono_pos_r;
    auto using comparison_qp.
  Qed.
 
  Lemma new_equality :
    (3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p)).
  Proof.
    rewrite! sub_square_identity.
    all: auto using comparison_2p3q, comparison_4q3p with arith.
    lia.
  Qed.

  (**
     After the `End` command, lemmas inside the section are generalized
     with the variables and hypotheses they depend on.
   *)
End sqrt2_decrease.

(** ** The Main Action: Statement and Proof *)

(**
   The proof proceeds by well-founded induction on q.
   We apply the induction hypothesis with the numbers <<3 * q - 2 * p>>
   and <<3 * p - 4 * q>>. This leaves two key proof goals:
   - <<3 * q - 2 * p <> 0>>, which we prove using arithmetic and the
     [comparison2] lemma above.
   - <<(3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p))>>,
     which we prove using the [new_equality] lemma above.
 *)
Theorem sqrt2_not_rational :
  forall p q : nat, q <> 0 -> ¬ p ^ 2 = 2 * (q ^ 2).
Proof.
  assert (forall x, x ^ 2 = x * x) as sq by (simpl; lia).
  intros p q; rewrite! sq; clear sq.
  revert p.
  induction q using (well_founded_ind lt_wf).
  intros p Hneq.
  
  specialize H with (y := 3 * q - 2 * p) (p := 3 * p - 4 * q).
  intros Heq.
  
  apply H.
  - apply comparison_3q2p. all: auto.
  - apply Nat.sub_gt. apply comparison_2p3q. all: auto.
  - apply new_equality. all: auto.
Qed.