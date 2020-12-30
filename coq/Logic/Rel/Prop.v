Lemma equivRelf : forall (A:Prop), A <-> A.
Proof.
    intro A. split; auto.
Qed.


Lemma equivSym : forall (A B:Prop), A <-> B -> B <-> A.
Proof.
    intros A B [H1 H2]. split; assumption.
Qed.


Lemma equivTrans : forall (A B C:Prop), A <-> B -> B <-> C -> A <-> C.
Proof.
    intros A B C [H1 H2] [H3 H4]. split; intros H5.
    - apply H3, H1. assumption.
    - apply H2, H4. assumption.
Qed.
