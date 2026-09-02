Lemma n_le_max : forall (n m:nat), n <= max n m.
Proof.
    induction n as [|n IH].
        - induction m as [|m IH'].
            + apply le_n.
            + apply le_S. assumption.
        - induction m as [|m IH'].
            + apply le_n.
            + apply le_n_S, IH.
Qed.

Lemma max_sym : forall (n m:nat), max n m = max m n.
Proof.
    induction n as [|n IH].
        - induction m as [|m IH']; reflexivity.
        - induction m as [|m IH'].
            + reflexivity.
            + simpl. rewrite IH. reflexivity.
Qed.

Lemma m_le_max : forall (n m:nat), m <= max n m.
Proof.
    intros n m. rewrite max_sym. apply n_le_max.
Qed.
