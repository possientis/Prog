Definition LEM : Prop := forall (p:Prop), p \/ ~p.
 
Definition PropExt : Prop := forall (p q:Prop), p <-> q -> p = q.

Lemma L1 : LEM -> forall (p:Prop), (p <-> True) \/ (p <-> False).
Proof.
    intros L p. destruct (L p) as [H1|H1].
    - left. split; intros H2.
        + trivial.
        + assumption.
    - right. split; intros H2.
        +  apply H1. assumption.
        + contradiction.
Qed.

Lemma PropostionalCompleteness : LEM -> PropExt ->
    forall (p:Prop), p = True \/ p = False.
Proof.
    intros L P p. destruct (L1 L p) as [H|H].
    - left. apply P. assumption.
    - right. apply P. assumption.
Qed.

