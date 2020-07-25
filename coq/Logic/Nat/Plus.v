Lemma sum_0 : forall (n m:nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
    intros [|n] [|m].
    - intros _. split; reflexivity.
    - intros H. inversion H.
    - intros H. inversion H.
    - intros H. inversion H.
Qed.


