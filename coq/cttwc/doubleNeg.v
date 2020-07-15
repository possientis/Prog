Lemma L1 : forall (X Y:Prop), ~~(X -> Y) <-> (~~X -> ~~Y).
Proof.
    intros X Y. split; intros H1 H2.
    - intros H3. apply H1. intros H4. apply H2. intros H5.
      apply H3, H4. assumption.
    - assert (~Y) as H3.
        { intros H3. apply H2. intros H4. assumption. }
      apply H2. intros H4. exfalso. apply H1.
            + intro H5. apply H5. assumption.
            + assumption.
Qed. 


Lemma L2 : forall (X Y:Prop), ~~(X /\ Y) <-> ~~X /\ ~~Y.
Proof.
    intros  X Y. split.
    - intros H1. split; intros H2; 
      apply H1; intros [H3 H4]; apply H2; assumption.
    - intros [H1 H2] H3. apply H1. intros H4. apply H2. intros H5.
      apply H3. split; assumption.
Qed.

Lemma L3 : ~~True <-> True.
Proof.
    split; intros H1.
    - trivial.
    - intros H2. apply H2. trivial.
Qed.


Lemma L4 : ~~False <-> False.
Proof.
    split; intros H1.
    - apply H1. intros H2. contradiction.
    - contradiction.
Qed.

Lemma L5 : forall (X Y:Prop), ~(X /\ Y) <-> ~~(~X \/ ~Y).
Proof.
    intros X Y. split; intros H1.
    - intros H2. 
      assert (~~X) as H3. { intros H3. apply H2. left. assumption. }
      assert (~~Y) as H4. { intros H4. apply H2. right. assumption. }
      apply H3. intros H5. apply H4. intros H6. apply H1. split; assumption.
    - intros [H2 H3]. apply H1. intros [H4|H4]; apply H4; assumption.
Qed.

Lemma L6 : forall (X Y:Prop), (~X -> ~Y) <-> ~~(Y -> X).
Proof.
    intros X Y. split; intros H1 H2.
    - assert (~X) as H3. { intros H3. apply H2. intros H4. assumption. }
      assert (~~Y) as H4. 
        { intros H4. apply H2. intros H5. exfalso. apply H4. assumption. }
      apply H4, H1, H3.
    - intros H3. apply H1. intros H4. apply H2, H4, H3.
Qed.
