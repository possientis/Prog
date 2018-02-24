Example or_exercise1 : forall (n m:nat),
    n = 0 \/ m = 0 -> n * m = 0.
Proof.
    intros n m [H1|H2].
    - rewrite H1. reflexivity.
    - rewrite H2. apply mult_n_0. 
Qed.

Lemma mult_0 : forall (n m:nat),
    n * m = 0 <-> n = 0 \/ m = 0.
Proof.
    split. 
    - apply mult_eq_0.
    - apply or_exercise1.
Qed.



