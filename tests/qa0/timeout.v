Require Import Nat.

Axiom add_comm : forall n m , n + m = m + n.

Lemma zz x : x + 0 = x.

Timeout 1 repeat rewrite add_comm.
