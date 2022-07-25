# Welcome to the jsCoq Interactive Online System!

*jsCoq* is an interactive, web-based environment for the Coq Theorem prover, and is a collaborative development effort. See the list of contributors below.

*jsCoq* is open source. If you find any problem that you wish to report or want to add your own contribution, you are extremely welcome! We await your feedback at [GitHub](https://github.com/jscoq/jscoq) and [Zulip](https://https://coq.zulipchat.com/#narrow/stream/256336-jsCoq).

## First example: `rev ∘ rev = id`

The following is a simple proof that `rev`, the standard list reversal function as commonly defined in ML and other languages of the family, is an involution.

```coq
From Coq Require Import List.
Import ListNotations.
```

We are going to need a simpler auxiliary lemma, one that connects `rev`, `::` (the list constructor, also known as `cons`), and `snoc` (the dual of `cons`, a function that appends an element at the end of a list). This is because the latter two participate in the definition of the former, `rev`.

```coq
Lemma rev_snoc_cons A :
  forall (x : A) (l : list A), rev (l ++ [x]) = x :: rev l.
```

This proposition is proven by way of the standard induction on the structure of the list `l`.

```coq
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. simpl. reflexivity.
Qed.
```