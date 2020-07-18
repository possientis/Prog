Definition LEM : Prop := forall (X:Prop), X \/ ~X.

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

Lemma L3 : Definite True /\ Stable True.
Proof.
    unfold Definite, Stable. split.
    - left. trivial.
    - intros H. trivial.
Qed.

Lemma L4 : Definite False /\ Stable False.
Proof.
    unfold Definite, Stable. split.
    - right. auto.
    - intros H. apply H. intros H'. contradiction.
Qed.

Lemma L5 : forall (X Y:Prop), X <-> Y -> Stable X -> Stable Y.
Proof.
    unfold Stable. intros X Y [H1 H2] H3 H4. 
    apply H1, H3. intros H5. apply H4. intros H6. apply H5, H2. assumption.
Qed.

Lemma L6 : forall (X Y:Prop), X <-> Y -> Definite X -> Definite Y.
Proof.
    unfold Definite. intros X Y [H1 H2] [H3|H3].
    - left. apply H1. assumption.
    - right. intros H4. apply H3. apply H2. assumption.
Qed.

Lemma L7 : LEM -> forall (X:Prop), Stable X /\ Definite X.
Proof.
    unfold LEM, Stable, Definite. intros L X. split.
    - intros H. destruct (L X) as [H1|H1].
        + assumption.
        + exfalso. apply H. assumption.
    - apply L.
Qed.

Lemma L8 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X -> Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. intros H3. assumption.
    - right. intros H3. apply H2, H3. assumption.
    - left. intros H3. assumption.
    - left. intros H3. exfalso. apply H1. assumption.
Qed.

Lemma L9 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X /\ Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. split; assumption.
    - right. intros [H3 H4]. apply H2. assumption.
    - right. intros [H3 H4]. apply H1. assumption.
    - right. intros [H3 H4]. apply H1. assumption.
Qed.

Lemma L10 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X \/ Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. left. assumption.
    - left. left. assumption.
    - left. right. assumption.
    - right. intros [H3|H3].
        + apply H1. assumption.
        + apply H2. assumption.
Qed.    

Lemma L11 : forall (X:Prop), Definite X -> Definite (~X).
Proof.
    unfold Definite. intros X [H1|H1].
    - right. intros H2. apply H2. assumption.
    - left. assumption.
Qed.

