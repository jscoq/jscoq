(** * More jsCoq *)

(** ** Literate documents -- the code route *)

(**
 This [.v] file contains some Coq code with block comments that
 can be processed by [coqdoc].
 Using [jscoqdoc], it can be made into an interactive document. #&#128526;#
 *)

Require Import List.
Import ListNotations.


(**
 We are going to define a recursive function, [nonzeros],
 that filters out all the zeros from a list of [nat] elements.
 *)

Definition natlist := list nat.

Fixpoint nonzeros (l : natlist) :=
  match l with
  | [] => []
  | 0 :: xs => nonzeros xs
  | x :: xs => x :: nonzeros xs
  end.

(**
 Jus to show you that it works:
 *)

Check nonzeros.
Compute nonzeros [5;6;0;7;0;9;8].

(**
 We will now prove that [nonzeros] distributes over [++] (list concatenation).
 First, we define a [simpl] hint, which will allow Coq tactics to expand its
 definition when it occurs in goals.


 #(See <a href="https://coq.github.io/doc/v8.15/refman/language/extensions/arguments-command.html##args-effect-on-unfolding">
   the relevant documentation.</a>)#
*)

Arguments nonzeros l : simpl nomatch.

(**
 _And now, to the proof_ !
*)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
(**
  #<dd>#
  Unsurprisingly, the proof progresses by induction on the first list, [l1].
  #</dd>#
 *)
  intros l1 l2. induction l1 as [| n' l' IHl'].
  - simpl. reflexivity.
  - simpl. case n'; simpl.
   + assumption.
   + congruence.
Qed.

Check nonzeros_app.
