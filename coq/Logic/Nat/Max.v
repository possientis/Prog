Lemma max_n_0 : forall (n:nat), max n 0 = n.
Proof.
    destruct n as [|n]; reflexivity.
Qed.

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

Lemma max_lub : forall (n m N:nat), n <= N -> m <= N -> max n m <= N.
Proof.
    intros n m N. revert m N. induction n as [|n IH].
    - simpl. intros. assumption.
    - intros m N H1 H2. simpl. destruct m as [|m].
        + assumption.
        + destruct N as [|N].
            { inversion H1. }
            { apply le_n_S. apply IH; apply le_S_n; assumption. }
Qed.


