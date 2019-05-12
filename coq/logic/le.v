Lemma not_le_Sn_n : forall (n:nat), ~(S n <= n).
Proof.
    induction n as [|n IH]; intros H.
    - inversion H.
    - apply IH. apply le_S_n. assumption.
Qed.
