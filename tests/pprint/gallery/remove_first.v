Set Printing Width 75.

Require Import List.
Import ListNotations.

Inductive loc := Loop : loc | Ret : bool -> loc.

Record state := {a: list nat; i: nat; used: list nat; pc: loc}.

Notation "x .a" := (a x)  (at level 1, format "x '.a'").
Notation "x .i" := (i x)  (at level 1, format "x '.i'").
Notation "x .used" := (used x)  (at level 1, format "x '.used'").
Notation "x .pc" := (pc x)  (at level 1, format "x '.pc'").



Fixpoint remove_first (v : nat) l := match l with
| [] => None
| x :: xs => if Nat.eqb x v then Some (xs, 0)
            else option_map (fun l'i => (x :: fst l'i, snd l'i + 1))
                            (remove_first v xs)
end.

Fixpoint remove_all (v : nat) l := match l with
| [] => []
| x :: xs => if Nat.eqb x v then remove_all v xs
            else x :: remove_all v xs
end.

Definition removen {A} n (l : list A) := firstn n l ++ skipn (1+n) l.

Definition decr_gt i j := if Nat.ltb j i then i - 1 else i.
Definition decr_ge i j := if Nat.leb j i then i - 1 else i.


Definition dec P := {P}+{~P}.

Definition as_bool {P} (x : dec P) := if x then true else false.

Definition Inb : forall v l, dec (In v l) := in_dec PeanoNat.Nat.eq_dec.


Coercion as_bool : dec >-> bool.

Definition init a0 := {| a := a0; i := 0; used := []; pc := Loop |}.


Definition f s := match remove_first (length s.a - 1) s.a with
| None =>          {| a := removelast s.a;   i := decr_ge s.i (length s.a); 
                     used := [];            pc := s.pc |}
| Some (a', j) =>  {| a := a';               i := decr_gt s.i j;
                     used := s.used;        pc := s.pc |}
end.

Lemma decr_ge_range_shrink i j n : i <= n -> j <= n -> decr_ge i j <= n - 1.
Admitted.

Lemma decr_gt_range_shrink i j n : i <= n -> j < n -> decr_gt i j <= n - 1.
Admitted.

Lemma removelast_shrink A (l : list A) : length (removelast l) = length l - 1.
Admitted.

Lemma remove_first_range l a :
  remove_first l a = None \/
  exists a' j, remove_first l a = Some (a', j) /\ j < length a /\ length a' = length a - 1.
Proof.
  unfold remove_first.
Admitted.

Lemma in_range s : s.i <= length s.a -> (f s).i <= length (f s).a.
Proof.
  destruct (remove_first_range (length s.a - 1) s.a).
  - unfold f; rewrite H; simpl. rewrite removelast_shrink.
    intro; apply decr_ge_range_shrink. assumption. reflexivity.
  - destruct H as [a' [j [H1 [H2 H3]]]].
    unfold f; rewrite H1; simpl. rewrite H3.
    intro; apply decr_gt_range_shrink; assumption.
Qed.

Definition cond0 s := In (length s.a - 1) s.a.

Lemma remove_first_in v l : In v l ->
  exists j, remove_first v l = Some (removen j l, j) /\
       nth_error l j = Some v.
Proof.
  unfold remove_first.
  Show.
Admitted.

Require Import Bool.

