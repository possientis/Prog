Definition Definite (X:Prop) : Prop := X \/ ~X.
Definition Stable (X:Prop) : Prop := ~~X -> X.

Lemma L1 : forall (X:Prop), Definite X -> Stable X.
Proof.
    unfold Definite, Stable. intros X [H1|H1] H2.
    - assumption.
    - apply H2 in H1. contradiction.
Qed.


Lemma L2 : forall (X:Prop), Stable (~X).
Proof.
    unfold Stable. intros X H1 H2. apply H1. intros H3. apply H3. assumption.
Qed.
