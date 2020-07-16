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


Lemma L7 : forall (X Y:Prop), (~X -> ~Y) <-> (Y -> ~~X).
Proof.
    intros X Y. split; intros H1 H2 H3; apply H1; assumption.
Qed.

Lemma L8 : forall (X Y:Prop), (X -> Y) -> ~~(~X \/ Y).
Proof.
    intros X Y H1 H2. 
    assert (~Y) as H3. { intros H3. apply H2. right. assumption. }
    assert (~~X) as H4. {intros H4. apply H2. left. assumption. }
    assert (~X) as H5. { intros H5. apply H3, H1. assumption. }
    apply H4. assumption.
Qed.


Lemma L9 : forall (a:Type) (p:a -> Prop), 
    ~(forall (x:a), ~p x) <-> ~~ exists (x:a), p x.
Proof.
    intros a p. split; intros H1 H2; apply H1.
    - intros x H3. apply H2. exists x. assumption.
    - intros [x H3]. apply (H2 x). assumption.
Qed.

Lemma L10 : forall (X Y:Prop), ~~X \/ ~~Y -> ~~(X \/ Y).
Proof.
    intros X Y [H1|H1] H2; apply H1; intros H3; apply H2.
    - left. assumption.
    - right. assumption.
Qed.

Lemma L11 : forall (a:Type) (p:a -> Prop), 
    (exists (x:a), ~~ p x) -> ~~ exists (x:a), p x.
Proof.
    intros a p [x H1] H2. apply H1. intros H3. apply H2. exists x. assumption.
Qed.

Lemma L12 : forall (a:Type) (p:a -> Prop), 
    ~~(forall (x:a), p x) -> forall (x:a), ~~ p x.
Proof.
    intros a p H1 x H2. apply H1. intros H3. apply H2, H3.
Qed.

(* Coq meta-property not provable in Coq: The double negation of a quantifier   *)
(* free proposition which is provable using LEM, is provable.                   *)

(* X \/ ~X is provable using LEM, hence ...                                     *)
Lemma L13 : forall (X:Prop), ~~(X \/ ~X).
Proof.
    intros X H1.
    assert (~X) as H2.  { intros H2. apply H1. left.  assumption. }
    assert (~~X) as H3. { intros H3. apply H1. right. assumption. }
    apply H3. assumption.
Qed.

(* ~~X -> X is provable using LEM, hence...                                     *)
Lemma L14 : forall (X:Prop), ~~(~~X -> X).
Proof.
    intros X H1. apply H1. intros H2. exfalso. apply H2. intros H3. apply H1.
    intros H4. assumption.
Qed.

Lemma L15 : forall (X Y:Prop), ~~(~(X /\ Y) -> ~X \/ ~Y).
Proof.
    intros X Y H1. apply H1. intros H2. 
    assert (~~X) as H3. { intros H3. apply H1. intros H4. left.  assumption. }
    assert (~~Y) as H4. { intros H4. apply H1. intros H5. right. assumption. }
    exfalso. apply H3. intros H5. apply H4. intro H6. apply H2. 
    split; assumption.
Qed.
