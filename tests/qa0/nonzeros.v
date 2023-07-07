Require Import List.
Import ListNotations.


Definition natlist := list nat.

Fixpoint nonzeros (l : natlist) :=
  match l with
  | [] => []
  | 0 :: xs => nonzeros xs
  | x :: xs => x :: nonzeros xs
  end.

Check nonzeros.
(* Compute nonzeros [5;6;0;7;0;9;8]. *)
Eval cbv in nonzeros [5;6;0;7;0;9;8].

Arguments nonzeros l : simpl nomatch.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [| n' l' IHl'].
  -simpl. reflexivity.
  -simpl. case n'; simpl.
   + assumption.
   + congruence.
Qed.

Check nonzeros_app.
