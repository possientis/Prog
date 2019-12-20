Definition LEM : Prop :=  forall (p:Prop), p \/ ~p.

Lemma LEMor : LEM -> forall (p q:Prop), (~p -> q) <-> p \/ q.
Proof.
    unfold LEM. intros L p q. split; intros H.
    - destruct (L p) as [H'|H'].
        + left. assumption.
        + right. apply H. assumption.
    - intros H1. destruct H as [H2|H2].
        + exfalso. apply H1. assumption.
        + assumption.
Qed.

(*
Lemma LEMAnd : LEM -> forall (p q:Prop), ~(~~p -> ~q) <-> p /\ q.
Proof.
    unfold LEM. intros L p q. split; intros H.
    -

Show.
*)
