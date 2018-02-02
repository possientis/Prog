Require Import nat.
Require Import or.
Require Import Setoid.

Lemma mult_0_3 : forall (n m p:nat),
    n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
    intros n m p. rewrite mult_0. rewrite mult_0. 
    rewrite or_assoc. reflexivity.
Qed.
